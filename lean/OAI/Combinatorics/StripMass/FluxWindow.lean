import Mathlib
import OAI.Combinatorics.StripMass.RibbonGlobal

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree Filter Topology

 
def IsExit (D : Vertex→Prop) (i : ℤ) (l : List Bool) : Prop :=
  l≠[] ∧ (visited Prod.fst next (bottom i) l).Nodup ∧
  (∀v∈visited Prod.fst next (bottom i) l,D v) ∧
  ¬D (terminal next (bottom i) l).1

def exitWeight (D : Vertex→Prop) (i : ℤ) (l : List Bool) : ℂ :=
  if IsExit D i l then wordWeight factor l else 0

def window (H : ℕ) (i : ℤ) (m : ℕ) : Finset Vertex :=
  (Finset.Ico (i-(m:ℤ)) (i+(m:ℤ)+1)).product ((Finset.Ico 0 (H:ℤ)).product Finset.univ)

@[simp] lemma mem_window (H : ℕ) (i : ℤ) (m : ℕ) (v : Vertex) :
    v∈window H i m ↔ i-(m:ℤ)≤v.1 ∧ v.1 < i+(m:ℤ)+1 ∧ 0≤v.2.1 ∧ v.2.1<(H:ℤ) := by
  rcases v with ⟨k,r,b⟩
  simp [window, and_assoc]

def clip (D : Vertex→Prop) (H : ℕ) (i : ℤ) (m : ℕ) : Finset Vertex :=
  (window H i m).filter D

def finiteExits (D : Vertex→Prop) (H : ℕ) (i : ℤ) (m : ℕ) : Finset (List Bool) :=
  (words (clip D H i m) (bottom i)).filter (fun l=>(terminal next (bottom i) l).1∉clip D H i m)

def physicalExits (D : Vertex→Prop) (H : ℕ) (i : ℤ) (m : ℕ) : Finset (List Bool) :=
  (finiteExits D H i m).filter (fun l=>¬D (terminal next (bottom i) l).1)

def sideExits (D : Vertex→Prop) (H : ℕ) (i : ℤ) (m : ℕ) : Finset (List Bool) :=
  (finiteExits D H i m).filter (fun l=>D (terminal next (bottom i) l).1)

lemma source_clip {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (m : ℕ) : (bottom i).1∈clip D H i m := by
  simp only [clip,Finset.mem_filter,mem_window,bottom]
  exact ⟨⟨by omega,by omega,by omega,by omega⟩,hi⟩

lemma finiteExit_nonempty {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) {m : ℕ} {l : List Bool} (hl : l∈finiteExits D H i m) : l≠[] := by
  intro he
  subst l
  exact (Finset.mem_filter.mp hl).2 (source_clip hH hi m)

lemma physicalExit_isExit {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) {m : ℕ} {l : List Bool} (hl : l∈physicalExits D H i m) : IsExit D i l := by
  obtain ⟨he,ht⟩:=Finset.mem_filter.mp hl
  refine ⟨finiteExit_nonempty hH hi he,visited_nodup Prod.fst next (Finset.mem_filter.mp he).1,?_,ht⟩
  intro v hv
  exact (Finset.mem_filter.mp (visited_mem_domain Prod.fst next (Finset.mem_filter.mp he).1 v hv)).2

lemma eventually_window {H : ℕ} {i : ℤ} {v : Vertex} (hv : 0≤v.2.1 ∧ v.2.1<(H:ℤ)) :
    ∀ᶠ m : ℕ in atTop,v∈window H i m := by
  filter_upwards [eventually_ge_atTop ((v.1-i).natAbs+1)] with m hm
  rw [mem_window]
  have ha : v.1-i≤((v.1-i).natAbs:ℤ) := Int.le_natAbs
  have hb : -(v.1-i)≤((v.1-i).natAbs:ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs : -(v.1-i)≤((-(v.1-i)).natAbs:ℤ))
  exact ⟨by omega,by omega,hv⟩

lemma eventually_physicalExit {D : Vertex→Prop} {H : ℕ} {i : ℤ}
    (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) {l : List Bool} (hl : IsExit D i l) :
    ∀ᶠ m : ℕ in atTop,l∈physicalExits D H i m := by
  have he : ∀ᶠ m : ℕ in atTop,∀v∈(visited Prod.fst next (bottom i) l).toFinset,v∈window H i m := by
    apply (Finset.eventually_all _).mpr
    intro v hv
    exact eventually_window (hD v (hl.2.2.1 v (List.mem_toFinset.mp hv)))
  filter_upwards [he] with m hm
  have hout : (terminal next (bottom i) l).1∉clip D H i m := by
    intro hx; exact hl.2.2.2 (Finset.mem_filter.mp hx).2
  have hw : l∈words (clip D H i m) (bottom i) := by
    apply (mem_leaves_iff _ _ _ _ _).mpr
    exact ⟨hl.2.1,fun v hv=>Finset.mem_filter.mpr ⟨hm v (List.mem_toFinset.mpr hv),hl.2.2.1 v hv⟩,Or.inl hout⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw,hout⟩,hl.2.2.2⟩

lemma physicalExit_limit {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ))
    (hs : Summable (exitWeight D i)) :
    Tendsto (fun m : ℕ=>∑l∈physicalExits D H i m,wordWeight factor l)
      atTop (𝓝 (∑'l,exitWeight D i l)) := by
  have he (m : ℕ) : (∑l∈physicalExits D H i m,wordWeight factor l)=
      ∑'l,if l∈physicalExits D H i m then wordWeight factor l else 0 := by
    symm
    rw [tsum_eq_sum (s:=physicalExits D H i m) (fun l hl=>ite_eq_right hl)]
    apply Finset.sum_congr rfl
    intro l hl
    rw [ite_eq_left hl]
  simp_rw [he]
  apply tendsto_tsum_of_dominated_convergence hs.norm
  · intro l
    by_cases hl : IsExit D i l
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_physicalExit hD hl] with m hm
      simp [exitWeight,hl,hm]
    · apply tendsto_const_nhds.congr'
      apply Eventually.of_forall
      intro m
      have hn : l∉physicalExits D H i m := fun hm=>hl (physicalExit_isExit hH hi hm)
      simp [exitWeight,hl,hn]
  · apply Eventually.of_forall
    intro m l
    split_ifs with hl
    · rw [exitWeight,ite_eq_left (physicalExit_isExit hH hi hl)]
    · simpa only [norm_zero] using norm_nonneg (exitWeight D i l)

lemma crossing_column {H : ℕ} {i : ℤ} {m : ℕ} {s : State}
    (hp : (back s).1∈window H i m) (hs : 0 ≤ s.1.2.1 ∧ s.1.2.1 < (H:ℤ))
    (hn : s.1∉window H i m) : s.2=1 ∧ (s.1.1=i-(m:ℤ)-1 ∨ s.1.1=i+(m:ℤ)+1) := by
  rcases s with ⟨⟨k,r,b⟩,p⟩
  fin_cases p <;> cases b <;> simp [mem_window,back,neighbor] at hp hs hn ⊢ <;> omega

lemma sideExit_column {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) {m : ℕ} {l : List Bool}
    (hl : l∈sideExits D H i m) :
    (terminal next (bottom i) l).2=1 ∧
    ((terminal next (bottom i) l).1.1=i-(m:ℤ)-1 ∨ (terminal next (bottom i) l).1.1=i+(m:ℤ)+1) := by
  obtain ⟨he,hd⟩:=Finset.mem_filter.mp hl
  obtain ⟨hw,hn⟩:=Finset.mem_filter.mp he
  apply crossing_column
    (Finset.mem_filter.mp (visited_mem_domain Prod.fst next hw _
      (lastVisited_mem _ _ (finiteExit_nonempty hH hi he)))).1 (hD _ hd)
  intro hm
  exact hn (Finset.mem_filter.mpr ⟨hm,hd⟩)

lemma sideExit_spec {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i k : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) {m : ℕ} {l : List Bool}
    (hl : l∈sideExits D H i m) (hk : (terminal next (bottom i) l).1.1=k) :
    l≠[] ∧ (visited Prod.fst next (bottom i) l).Nodup ∧
    (∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1 ∧ v.2.1<(H:ℤ) ∧ v.1≠k) ∧
    (terminal next (bottom i) l).2=1 ∧ (terminal next (bottom i) l).1.1=k := by
  have he := (Finset.mem_filter.mp hl).1
  have hw := (Finset.mem_filter.mp he).1
  have hc:=sideExit_column hH hi hD hl
  refine ⟨finiteExit_nonempty hH hi he,visited_nodup Prod.fst next hw,?_,hc.1,hk⟩
  intro v hv
  have hm:=Finset.mem_filter.mp (visited_mem_domain Prod.fst next hw v hv)
  have hb:=hD _ hm.2
  have hcol:=(mem_window H i m v).mp hm.1
  exact ⟨hb.1,hb.2,by rcases hc.2 with hc|hc <;> omega⟩

lemma side_sum_bound {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i k : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) {m : ℕ}
    (F : Finset (List Bool)) (hF : F⊆sideExits D H i m)
    (hk : ∀l∈F,(terminal next (bottom i) l).1.1=k) (hik : i≠k) :
    ∑l∈F,rho^l.length ≤ (rho^(2*H))⁻¹*K H (k-i) := by
  let e : F→SideWord H i k:=fun l=>⟨l.val,sideExit_spec hH hi hD (hF l.property) (hk l.val l.property)⟩
  have he : Function.Injective e := by intro l n h; apply Subtype.ext; exact congrArg (fun x : SideWord H i k=>x.val) h
  have hs:=SideWord.sum_le hH hik (Finset.univ.image e)
  rw [Finset.sum_image (fun x _ y _ h=>he h)] at hs
  change (∑x : F,rho^x.val.length)≤_ at hs
  rw [←Finset.sum_coe_sort F (fun l : List Bool=>rho^l.length)]
  exact hs

lemma sideExit_bound {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (m : ℕ) :
    ‖∑l∈sideExits D H i m,wordWeight factor l‖ ≤
      (rho^(2*H))⁻¹*(K H (-(m:ℤ)-1)+K H ((m:ℤ)+1)) := by
  have hl:=side_sum_bound hH hi hD
    ((sideExits D H i m).filter (fun l=>(terminal next (bottom i) l).1.1=i-(m:ℤ)-1))
    (Finset.filter_subset _ _) (fun l hl=>(Finset.mem_filter.mp hl).2) (by omega : i≠i-(m:ℤ)-1)
  have hr:=side_sum_bound hH hi hD
    ((sideExits D H i m).filter (fun l=>¬(terminal next (bottom i) l).1.1=i-(m:ℤ)-1))
    (Finset.filter_subset _ _) (fun l hl=>(sideExit_column hH hi hD (Finset.mem_filter.mp hl).1).2.resolve_left
      (Finset.mem_filter.mp hl).2) (by omega : i≠i+(m:ℤ)+1)
  have hs:=Finset.sum_filter_add_sum_filter_not (sideExits D H i m)
    (fun l=>(terminal next (bottom i) l).1.1=i-(m:ℤ)-1) (fun l : List Bool=>rho^l.length)
  calc
    _ ≤ ∑l∈sideExits D H i m,‖wordWeight factor l‖ := norm_sum_le _ _
    _ = ∑l∈sideExits D H i m,rho^l.length := by simp only [wordWeight_norm]
    _ ≤ _ := by
      rw [←hs]
      have he₁ : i-(m:ℤ)-1-i= -(m:ℤ)-1 := by ring
      have he₂ : i+(m:ℤ)+1-i=(m:ℤ)+1 := by ring
      rw [he₁] at hl
      rw [he₂] at hr
      simpa only [mul_add] using add_le_add hl hr

lemma finite_split {D : Vertex→Prop} {H : ℕ} {i : ℤ}
    (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (m : ℕ) :
    (∑l∈physicalExits D H i m,wordWeight factor l)+
    (∑l∈sideExits D H i m,wordWeight factor l)=1 := by
  have hs:=Finset.sum_filter_add_sum_filter_not (finiteExits D H i m)
    (fun l=>¬D (terminal next (bottom i) l).1) (wordWeight factor)
  simp only [not_not] at hs
  rw [physicalExits,sideExits,hs]
  exact finite_boundary_flux _ i (fun v hv=>(hD _ (Finset.mem_filter.mp hv).2).1)

 

theorem infinite_boundary_flux {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ))
    (hs : Summable (exitWeight D i)) : ∑'l,exitWeight D i l=1 := by
  have hleft : Summable (fun m : ℕ=>K H (-(m:ℤ)-1)) :=
    (stripSumsFinite hH).2.2.1.comp_injective (i:=fun m : ℕ=> -(m:ℤ)-1) (by intro m n he; dsimp at he; omega)
  have hright : Summable (fun m : ℕ=>K H ((m:ℤ)+1)) :=
    (stripSumsFinite hH).2.2.1.comp_injective (i:=fun m : ℕ=> (m:ℤ)+1) (by intro m n he; dsimp at he; omega)
  have hb : Tendsto (fun m : ℕ=>(rho^(2*H))⁻¹*(K H (-(m:ℤ)-1)+K H ((m:ℤ)+1))) atTop (𝓝 0) := by
    simpa using (hleft.tendsto_atTop_zero.add hright.tendsto_atTop_zero).const_mul ((rho^(2*H))⁻¹)
  have hz : Tendsto (fun m : ℕ=>∑l∈sideExits D H i m,wordWeight factor l) atTop (𝓝 0) :=
    squeeze_zero_norm (fun m=>sideExit_bound hH hi hD m) hb
  have ht:=(physicalExit_limit hH hi hD hs).add hz
  simp only [add_zero] at ht
  have hc : Tendsto (fun m : ℕ=>(∑l∈physicalExits D H i m,wordWeight factor l)+
      (∑l∈sideExits D H i m,wordWeight factor l)) atTop (𝓝 1) := by
    simpa only [finite_split hD] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℂ)) atTop (𝓝 1))
  exact tendsto_nhds_unique ht hc

end

 

 

noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

 
structure BoundaryPorts (D : Vertex→Prop) (B : Type*) where
  port : B→State
  injective : Function.Injective port
  inside : ∀b,D (port b).1
  outside : ∀b,¬D (back (port b)).1
  complete : ∀s : State,D s.1→¬D (back s).1→∃b,port b=s

abbrev ExitWord (D : Vertex→Prop) (i : ℤ) := {l : List Bool // IsExit D i l}

variable {D : Vertex→Prop} {B : Type*} (P : BoundaryPorts D B) {H : ℕ} {i : ℤ}

def ValidBoundaryPath (H : ℕ) (i : ℤ) (x : B×List Triangle) : Prop :=
  bottom i≠P.port x.1 ∧
  PathBetween H (up i 0) (retractVertex (P.port x.1).1) x.2 ∧
  ∀v∈x.2,D (embedTriangle v)

abbrev BoundaryPath (H : ℕ) (i : ℤ) := {x : B×List Triangle // ValidBoundaryPath P H i x}

def boundaryPathWeight (H : ℕ) (i : ℤ) (x : B×List Triangle) : ℝ :=
  if ValidBoundaryPath P H i x then rho^x.2.length else 0

lemma boundaryPathWeight_nonneg (H : ℕ) (i : ℤ) (x : B×List Triangle) :
    0≤boundaryPathWeight P H i x := by
  unfold boundaryPathWeight
  split_ifs <;> positivity [rho_pos]

lemma source_outside (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) : ¬D (back (bottom i)).1 := by
  intro hx
  have hh:=(hD _ hx).1
  norm_num [back,bottom,neighbor] at hh

lemma exists_exit_port (x : ExitWord D i) : ∃b,P.port b=back (terminal next (bottom i) x.val) := by
  apply P.complete
  · exact x.property.2.2.1 _ (lastVisited_mem _ _ x.property.1)
  · simpa only [back_back] using x.property.2.2.2

def exitPort (x : ExitWord D i) : B := Classical.choose (exists_exit_port P x)

lemma exitPort_spec (x : ExitWord D i) :
    P.port (exitPort P x)=back (terminal next (bottom i) x.val) := Classical.choose_spec (exists_exit_port P x)

lemma exitPort_terminal (x : ExitWord D i) :
    terminal next (bottom i) x.val=back (P.port (exitPort P x)) := by
  rw [exitPort_spec,back_back]

lemma visited_map_retract (l : List Bool)
    (hrow : ∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1) :
    ((visited Prod.fst next (bottom i) l).map retractVertex).map embedTriangle=
      visited Prod.fst next (bottom i) l := by
  rw [List.map_map]
  conv_rhs => rw [←List.map_id (visited Prod.fst next (bottom i) l)]
  exact List.map_congr_left (fun v hv=>embed_retract v (hrow v hv))

def exitToPath (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (x : ExitWord D i) : BoundaryPath P H i := by
  refine ⟨(exitPort P x,(visited Prod.fst next (bottom i) x.val).map retractVertex),?_,?_,?_⟩
  · intro he
    exact word_terminal_ne_source x.property.1 x.property.2.1
      (by calc
        terminal next (bottom i) x.val=back (P.port (exitPort P x)) := exitPort_terminal P x
        _=back (bottom i) := congrArg back he.symm)
  · apply visited_retract_path H (up i 0) _ (bottom i) x.val x.property.1 rfl
      _ x.property.2.1 (fun v hv=>hD v (x.property.2.2.1 v hv))
    rw [←exitPort_spec]
    exact (embed_retract _ (hD _ (P.inside _)).1).symm
  · intro v hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    rw [embed_retract _ (hD _ (x.property.2.2.1 w hw)).1]
    exact x.property.2.2.1 w hw

lemma exitToPath_injective (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) :
    Function.Injective (exitToPath P (i:=i) hD) := by
  intro x y he
  have hb:=congrArg (fun z : BoundaryPath P H i=>z.val.1) he
  have hp:=congrArg (fun z : BoundaryPath P H i=>z.val.2.map embedTriangle) he
  change exitPort P x=exitPort P y at hb
  change ((visited Prod.fst next (bottom i) x.val).map retractVertex).map embedTriangle=
    ((visited Prod.fst next (bottom i) y.val).map retractVertex).map embedTriangle at hp
  rw [visited_map_retract _ (fun v hv=>(hD v (x.property.2.2.1 v hv)).1),
    visited_map_retract _ (fun v hv=>(hD v (y.property.2.2.1 v hv)).1)] at hp
  apply Subtype.ext
  exact word_unique _ _ _ hp (by rw [exitPort_terminal P x,exitPort_terminal P y,hb])

lemma exitToPath_surjective (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) :
    Function.Surjective (exitToPath P (i:=i) hD) := by
  intro x
  have hp:=x.property.2.1
  have hh : (x.val.2.map embedTriangle).head?=some (bottom i).1 := by
    rw [List.head?_map,hp.1]; rfl
  have ht : (x.val.2.map embedTriangle).getLast?=some (back (back (P.port x.val.1))).1 := by
    rw [back_back,List.getLast?_map,hp.2.1,Option.map_some,embed_retract _ (hD _ (P.inside _)).1]
  have hn : (x.val.2.map embedTriangle).Nodup := hp.2.2.1.map embedTriangle_injective
  have hc : (x.val.2.map embedTriangle).IsChain (fun v w=>∃q : Fin 3,neighbor v q=w) :=
    (List.isChain_map _).mpr (hp.2.2.2.1.imp (fun v w h=>(adjacent_iff v w).mp h))
  have hi : (back (bottom i)).1∉x.val.2.map embedTriangle := by
    intro hv
    obtain ⟨v,hv,he⟩:=List.mem_map.mp hv
    exact source_outside hD (he ▸ x.property.2.2 v hv)
  have ho : (back (P.port x.val.1)).1∉x.val.2.map embedTriangle := by
    intro hv
    obtain ⟨v,hv,he⟩:=List.mem_map.mp hv
    exact P.outside _ (he ▸ x.property.2.2 v hv)
  obtain ⟨l,hv,he⟩:=exists_word (bottom i) (back (P.port x.val.1)) (x.val.2.map embedTriangle)
    hh ht hn hc hi ho (by simpa only [back_back] using x.property.1)
  have hne:=word_nonempty_of_head _ _ _ hh hv
  have hl : IsExit D i l := by
    refine ⟨hne,by rw [hv]; exact hn,?_,?_⟩
    · intro v hm
      rw [hv] at hm
      obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
      exact x.property.2.2 w hw
    · rw [he]; exact P.outside _
  refine ⟨⟨l,hl⟩,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply P.injective
    rw [show (exitToPath P hD ⟨l,hl⟩).val.1=exitPort P ⟨l,hl⟩ from rfl,
      exitPort_spec,he,back_back]
  · change (visited Prod.fst next (bottom i) l).map retractVertex=x.val.2
    rw [hv,List.map_map]
    calc
      List.map (retractVertex ∘ embedTriangle) x.val.2=List.map id x.val.2 :=
        List.map_congr_left (fun v _=>retract_embed v)
      _=x.val.2 := List.map_id x.val.2

def exitPathEquiv (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) : ExitWord D i ≃ BoundaryPath P H i :=
  Equiv.ofBijective (exitToPath P hD) ⟨exitToPath_injective P hD,exitToPath_surjective P hD⟩

lemma exitPathEquiv_length (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (x : ExitWord D i) :
    (exitPathEquiv P hD x).val.2.length=x.val.length := by
  change ((visited Prod.fst next (bottom i) x.val).map retractVertex).length=x.val.length
  simp only [List.length_map,visited_length]

lemma boundaryPath_summable_iff :
    Summable (fun x : BoundaryPath P H i=>rho^x.val.2.length) ↔ Summable (boundaryPathWeight P H i) := by
  change Summable (fun x : {x | ValidBoundaryPath P H i x}=>rho^x.val.2.length) ↔ _
  exact summable_subtype_iff_indicator (s:={x | ValidBoundaryPath P H i x})
    (f:=fun x : B×List Triangle=>rho^x.2.length)

lemma exitWord_summable_iff :
    Summable (fun x : ExitWord D i=>rho^x.val.length) ↔
    Summable (fun l=>if IsExit D i l then rho^l.length else 0) := by
  exact summable_subtype_iff_indicator (s:={l | IsExit D i l}) (f:=fun l : List Bool=>rho^l.length)

lemma exit_weight_norm (l : List Bool) :
    ‖exitWeight D i l‖=if IsExit D i l then rho^l.length else 0 := by
  unfold exitWeight
  split_ifs <;> simp only [wordWeight_norm,norm_zero]

 

theorem exitWeight_summable (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ))
    (hs : Summable (boundaryPathWeight P H i)) : Summable (exitWeight D i) := by
  have hpath := (boundaryPath_summable_iff P (H:=H) (i:=i)).mpr hs
  have hw : Summable (fun x : ExitWord D i=>rho^(exitPathEquiv P hD x).val.2.length) :=
    ((exitPathEquiv P (i:=i) hD).summable_iff
      (f:=fun x : BoundaryPath P H i=>rho^x.val.2.length)).mpr hpath
  have hw' : Summable (fun x : ExitWord D i=>rho^x.val.length) :=
    hw.congr (fun x=>congrArg (fun n : ℕ=>rho^n) (exitPathEquiv_length P hD x))
  have hi := (exitWord_summable_iff (D:=D) (i:=i)).mp hw'
  apply (summable_norm_iff (f:=exitWeight D i)).mp
  exact hi.congr (fun l=>(exit_weight_norm (D:=D) (i:=i) l).symm)

 
theorem exitWeight_tsum (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (θ : B→ℤ)
    (hθ : ∀x : ExitWord D i,turn x.val=θ (exitPort P x)) :
    (∑'l,exitWeight D i l)=
      ∑'x : B×List Triangle,(boundaryPathWeight P H i x:ℂ)*Diagram.phase^(θ x.1) := by
  calc
    _ = ∑'x : ExitWord D i,wordWeight factor x.val :=
      (tsum_subtype {l | IsExit D i l} (wordWeight factor)).symm
    _ = ∑'x : ExitWord D i,(rho:ℂ)^(exitPathEquiv P hD x).val.2.length *
        Diagram.phase^(θ (exitPathEquiv P hD x).val.1) := by
      apply tsum_congr
      intro x
      rw [wordWeight_eq,exitPathEquiv_length,hθ]
      rfl
    _ = ∑'x : BoundaryPath P H i,(rho:ℂ)^x.val.2.length*Diagram.phase^(θ x.val.1) :=
      (exitPathEquiv P (i:=i) hD).tsum_eq (fun x : BoundaryPath P H i=>(rho:ℂ)^x.val.2.length*Diagram.phase^(θ x.val.1))
    _ = _ := by
      change (∑'x : {x | ValidBoundaryPath P H i x},(rho:ℂ)^x.val.2.length*Diagram.phase^(θ x.val.1))=_
      rw [tsum_subtype {x | ValidBoundaryPath P H i x} (fun x : B×List Triangle=>(rho:ℂ)^x.2.length*Diagram.phase^(θ x.1))]
      apply tsum_congr
      intro x
      simp only [Set.indicator,Set.mem_ofPred_eq,boundaryPathWeight]
      split_ifs <;> simp

 

theorem boundary_flux (hH : 1≤H) (hi : D (bottom i).1)
    (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (hs : Summable (boundaryPathWeight P H i))
    (θ : B→ℤ) (hθ : ∀x : ExitWord D i,turn x.val=θ (exitPort P x)) :
    (∑'x : B×List Triangle,(boundaryPathWeight P H i x:ℂ)*Diagram.phase^(θ x.1))=1 := by
  rw [←exitWeight_tsum P hD θ hθ]
  exact infinite_boundary_flux hH hi hD (exitWeight_summable P hD hs)

end

 

 

noncomputable section
open scoped Classical
open FiniteBranchTree

 
def steppedVertices (N : ℕ) (s : ℤ) (v : Vertex) : Prop :=
  0≤v.2.1 ∧ (v.2.1<(N:ℤ) ∨ v.2.1=(N:ℤ) ∧ s≤v.1)

lemma steppedVertices_embed (N : ℕ) (s : ℤ) (v : Triangle) :
    steppedVertices N s (embedTriangle v) ↔ steppedDomain N s v := by
  dsimp [steppedVertices,embedTriangle,steppedDomain]
  omega

lemma steppedVertices_bound (N : ℕ) (s : ℤ) (v : Vertex) (hv : steppedVertices N s v) :
    0≤v.2.1 ∧ v.2.1<((N+1:ℕ):ℤ) := by
  dsimp [steppedVertices] at hv
  exact ⟨hv.1,by omega⟩

def sidePort (N : ℕ) (s : ℤ) : State := ((s,(N:ℤ),true),1)

def stepTop (N : ℕ) (s j : ℤ) : State := if j<s then top N j else top (N+1) j

lemma lower_top_turn (N : ℕ) (hN : 1≤N) (s i j : ℤ) (hj : j<s)
    (l : List Bool) (_hl : l≠[]) (hn : (visited Prod.fst next (bottom i) l).Nodup)
    (hD : ∀v∈visited Prod.fst next (bottom i) l,steppedVertices N s v)
    (ht : terminal next (bottom i) l=back (top N j)) : turn l=0 := by
  have hu : (j,(N:ℤ),true)∉visited Prod.fst next (bottom i) l := by
    intro hv
    have hh:=hD _ hv
    simp only [steppedVertices,lt_self_iff_false,true_and,false_or] at hh
    omega
  have hd : (j,(N:ℤ),false)∉visited Prod.fst next (bottom i) l := by
    intro hv
    have hh:=hD _ hv
    simp only [steppedVertices,lt_self_iff_false,true_and,false_or] at hh
    omega
  have hv : visited Prod.fst next (bottom i) (l++[false,true])=
      visited Prod.fst next (bottom i) l++[(j,(N:ℤ),true),(j,(N:ℤ),false)] := by
    rw [visited_append,ht]
    simp [visited,back,top,neighbor,next,outgoing]
  have he : terminal next (bottom i) (l++[false,true])=back (top (N+1) j) := by
    rw [terminal_append,ht]
    simp [terminal,back,top,neighbor,next,outgoing,Fin.add_def]
  have hh:=top_turn (N+1) (by omega) i j (l++[false,true]) (by simp) (by
      rw [hv]
      apply List.nodup_append.mpr
      refine ⟨hn,by simp,?_⟩
      intro v hv w hw hew
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact hu (hew ▸ hv)
      · exact hd (hew ▸ hv)) (by
      intro v hm
      rw [hv] at hm
      rcases List.mem_append.mp hm with hm|hm
      · exact steppedVertices_bound N s v (hD v hm)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl|rfl <;> dsimp <;> omega) he
  simpa [turn_append,turn,sign] using hh

lemma step_top_turn (N : ℕ) (hN : 1≤N) (s i j : ℤ)
    (l : List Bool) (hl : l≠[]) (hn : (visited Prod.fst next (bottom i) l).Nodup)
    (hD : ∀v∈visited Prod.fst next (bottom i) l,steppedVertices N s v)
    (ht : terminal next (bottom i) l=back (stepTop N s j)) : turn l=0 := by
  by_cases hj : j<s
  · rw [stepTop,ite_eq_left hj] at ht
    exact lower_top_turn N hN s i j hj l hl hn hD ht
  · rw [stepTop,ite_eq_right hj] at ht
    exact top_turn (N+1) (by omega) i j l hl hn (fun v hv=>steppedVertices_bound N s v (hD v hv)) ht

lemma step_side_turn (N : ℕ) (s i : ℤ)
    (l : List Bool) (_hl : l≠[]) (hn : (visited Prod.fst next (bottom i) l).Nodup)
    (hD : ∀v∈visited Prod.fst next (bottom i) l,steppedVertices N s v)
    (ht : terminal next (bottom i) l=back (sidePort N s)) : turn l=1 := by
  have hd : (s-1,(N:ℤ),false)∉visited Prod.fst next (bottom i) l := by
    intro hv
    have hh:=hD _ hv
    simp only [steppedVertices,lt_self_iff_false,true_and,false_or] at hh
    omega
  have hv : visited Prod.fst next (bottom i) (l++[false])=
      visited Prod.fst next (bottom i) l++[(s-1,(N:ℤ),false)] := by
    rw [visited_append,ht]
    simp [visited,back,sidePort,neighbor]
  have he : terminal next (bottom i) (l++[false])=back (top (N+1) (s-1)) := by
    rw [terminal_append,ht]
    simp [terminal,back,top,sidePort,neighbor,next,outgoing,Fin.add_def]
  have hh:=top_turn (N+1) (by omega) i (s-1) (l++[false]) (by simp) (by
      rw [hv]
      apply List.nodup_append.mpr
      refine ⟨hn,by simp,?_⟩
      intro v hm w hw hew
      have hw:=List.mem_singleton.mp hw
      exact hd ((hew.trans hw) ▸ hm)) (by
      intro v hm
      rw [hv] at hm
      rcases List.mem_append.mp hm with hm|hm
      · exact steppedVertices_bound N s v (hD v hm)
      · have he:=List.mem_singleton.mp hm
        rw [he]
        dsimp
        omega) he
  simp [turn_append,turn,sign] at hh
  omega

end
end CriticalStrip.HoneycombBranch

end OAI
