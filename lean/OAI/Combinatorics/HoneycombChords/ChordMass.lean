import OAI.Combinatorics.HoneycombChords.ChordSystems

namespace OAI

/-! Chord mass for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.ListBound
open scoped BigOperators

universe u
def Pad (α : Type u) : ℕ→Type u
  | 0=>PUnit
  | n+1=>Option α × Pad α n
noncomputable instance padFintype (α : Type*) [Fintype α] : (n : ℕ)→Fintype (Pad α n)
  | 0=>by change Fintype PUnit;infer_instance
  | n+1=>by letI:=padFintype α n;change Fintype (Option α × Pad α n);infer_instance

def encode {α : Type*} : (n : ℕ)→List α→Pad α n
  | 0,_=>PUnit.unit
  | n+1,[] => (none,encode n [])
  | n+1,a::as => (some a,encode n as)
def decode {α : Type*} : {n : ℕ}→Pad α n→List α
  | 0,_=>[]
  | _+1,(none,p)=>decode p
  | _+1,(some a,p)=>a::decode p
lemma decode_encode {α : Type*} (n : ℕ) (as : List α) (h : as.length≤n) :
    decode (encode n as)=as := by
  induction n generalizing as with
  | zero => have he : as=[]:=List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h);subst as;rfl
  | succ n ih =>
    cases as with
    | nil => exact ih [] (Nat.zero_le n)
    | cons a as =>
      change a::decode (encode n as)=a::as
      rw [ih as (Nat.le_of_succ_le_succ h)]
noncomputable def weight {α : Type*} (w : α→ℝ) : {n : ℕ}→Pad α n→ℝ
  | 0,_=>1
  | _+1,(a,p)=>a.elim 1 w*weight w p
lemma weight_nonnegative {α : Type*} {w : α→ℝ} (hw : ∀ a,0≤w a)
    {n : ℕ} (p : Pad α n) : 0≤weight w p := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih =>
    rcases p with ⟨a,p⟩
    apply mul_nonneg (show 0≤a.elim 1 w by cases a <;> simp_all)
    exact ih p
lemma weight_encode {α : Type*} (w : α→ℝ) (n : ℕ) (as : List α) (h : as.length≤n) :
    weight w (encode n as)=(as.map w).prod := by
  induction n generalizing as with
  | zero => have he : as=[]:=List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h);subst as;rfl
  | succ n ih =>
    cases as with
    | nil => simpa only [encode,weight,Option.elim_none,one_mul,List.map_nil,List.prod_nil] using ih [] (Nat.zero_le n)
    | cons a as =>
      change w a*weight w (encode n as)=w a*(as.map w).prod
      rw [ih as (Nat.le_of_succ_le_succ h)]
lemma sum_weight {α : Type*} [Fintype α] (w : α→ℝ) (n : ℕ) :
    (∑ p : Pad α n,weight w p)=(1+∑ a,w a)^n := by
  induction n with
  | zero => change (∑ _ : PUnit, (1:ℝ))=1; simp
  | succ n ih =>
    change (∑ p : Option α × Pad α n,p.1.elim 1 w*weight w p.2)=_
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum]
    rw [ih,←Finset.sum_mul,Fintype.sum_option]
    simp only [Option.elim_none,Option.elim_some]
    rw [pow_succ]
    ring

lemma finite_system_bound {α : Type*} [Fintype α] (w : α→ℝ) (hw : ∀ a,0≤w a)
    (S : Finset (List α)) (n : ℕ) (hlen : ∀ as∈S,as.length≤n) :
    (∑ as∈S,(as.map w).prod)≤(1+∑ a,w a)^n := by
  classical
  calc
    _ = ∑ as∈S,weight w (encode n as) := by
      apply Finset.sum_congr rfl
      intro as has
      exact (weight_encode w n as (hlen as has)).symm
    _ = ∑ p∈S.image (encode n),weight w p := by
      symm
      apply Finset.sum_image
      intro as has bs hbs he
      have hh:=congrArg decode he
      simpa only [decode_encode n as (hlen as has),decode_encode n bs (hlen bs hbs)] using hh
    _ ≤ ∑ p : Pad α n,weight w p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p hp hn
      exact weight_nonnegative hw p
    _ = _ := sum_weight w n
end CriticalHoneycomb.Transfer.ListBound

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations
open scoped BigOperators

noncomputable def relativePartition {W H : ℕ} (x₀ : Assignment W H) : ℂ :=
  ∑ cfg : Cell W H→Shape,∑ x : Assignment W H,relativeTerm cfg x₀ x
lemma relativePartition_eq_prescribed {W H : ℕ} (x₀ : Assignment W H) :
    relativePartition x₀=prescribedPartition W H
      (fun j=>x₀.1 (.inl (0,j))) (fun j=>x₀.1 (.inl (Fin.last W,j)))
      (fun i=>x₀.1 (.inr (i,0))) (fun i=>x₀.1 (.inr (i,Fin.last H))) := by
  simp only [relativePartition,relativeTerm_eq_masked,sum_maskedTerm,prescribed_shape_expansion]

lemma active_shape_decomposition {W H : ℕ} (x₀ : Assignment (W+1) (H+1))
    (cfg : Cell (W+1) (H+1)→Shape)
    (hn : (∑ x,relativeTerm cfg x₀ x)≠0) :
    ∃ (x : Assignment (W+1) (H+1)) (cs : List (BoundaryChord W H)),
      SameBoundary x x₀ ∧ Matches cfg x.1 x.2 ∧ SelectedSystem x cs ∧
      (∑ y,relativeTerm cfg x₀ y)=systemAmplitude x cs := by
  classical
  obtain ⟨x,_,hx⟩:=Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨hb,hm,hp⟩:=(relativeTerm_ne_zero cfg x₀ x).mp hx
  have hx' : relativeTerm cfg x x≠0 :=
    (relativeTerm_ne_zero cfg x x).mpr ⟨sameBoundary_refl x,hm,hp⟩
  have hr:=relativeTerm_change_reference cfg hb
  obtain ⟨cs,hcs,hval⟩:=all_boundary_shape_decomposition cfg x hx' (by simpa only [hr] using hn)
  exact ⟨x,cs,hb,hm,hcs,by simpa only [hr] using hval⟩

theorem actual_partition_component_bound {W H : ℕ} (x₀ : Assignment (W+1) (H+1)) :
    ∃ S : Finset (List (BoundaryChord W H)),
      (∀ cs∈S, ∃ x : Assignment (W+1) (H+1),SameBoundary x x₀ ∧ SelectedSystem x cs) ∧
      (∀ cs∈S,(systemNodes cs).Nodup) ∧
      ‖relativePartition x₀‖≤∑ cs∈S,kappa^(systemNodes cs).length := by
  classical
  let F := fun cfg : Cell (W+1) (H+1)→Shape=>∑ x,relativeTerm cfg x₀ x
  let A := {cfg : Cell (W+1) (H+1)→Shape // F cfg≠0}
  have hd : ∀ a : A,∃ x cs,SameBoundary x x₀ ∧ Matches a.val x.1 x.2 ∧
      SelectedSystem x cs ∧ F a.val=systemAmplitude x cs := fun a=>
    active_shape_decomposition x₀ a.val a.property
  choose x cs hb hm hs hc using hd
  have hi : Function.Injective cs := by
    intro a b he
    apply Subtype.ext
    exact SelectedSystem.shape_unique (hs a) (he ▸ hs b) (hm a) (hm b)
  let S := Finset.univ.image cs
  refine ⟨S,?_,?_,?_⟩
  · intro z hz
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hz
    exact ⟨x a,hb a,hs a⟩
  · intro z hz
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hz
    exact (hs a).nodes_nodup
  · have hsum : relativePartition x₀=∑ a : A,F a.val := by
      change (∑ cfg,F cfg)=_
      rw [←sum_subtype_indicator (fun cfg=>F cfg≠0) F]
      apply Finset.sum_congr rfl
      intro cfg hcfg
      by_cases hh : F cfg=0 <;> simp [hh]
    rw [hsum]
    calc
      _ ≤ ∑ a : A,‖F a.val‖ := norm_sum_le _ _
      _ = ∑ a : A,kappa^(systemNodes (cs a)).length := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hc a,(hs a).amplitude_norm]
      _ = _ := by
        change (∑ a : A,kappa^(systemNodes (cs a)).length)=
          ∑ z∈Finset.univ.image cs,kappa^(systemNodes z).length
        symm
        exact Finset.sum_image (f:=fun z : List (BoundaryChord W H)=>kappa^(systemNodes z).length)
          (s:=(Finset.univ : Finset A)) hi.injOn
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology

noncomputable def hardWeight {W H : ℕ} (c : BoundaryChord W H) : ℝ := by
  classical
  exact if EndPort c.source ∧ EndPort c.target then kappa^c.chord.val.length else 0
lemma hardWeight_nonnegative {W H : ℕ} (c : BoundaryChord W H) : 0≤hardWeight c := by
  unfold hardWeight
  split_ifs
  · exact (pow_pos kappa_positive _).le
  · exact le_refl _
lemma sum_hardWeight (W H : ℕ) : (∑ c : BoundaryChord W H,hardWeight c)=singleSystemMass W H := by
  classical
  unfold hardWeight singleSystemMass
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _
lemma systemNodes_weight {W H : ℕ} (cs : List (BoundaryChord W H)) :
    kappa^(systemNodes cs).length=(cs.map (fun c=>kappa^c.chord.val.length)).prod := by
  induction cs with
  | nil => simp [systemNodes]
  | cons c cs ih =>
    change kappa^(c.chord.val++systemNodes cs).length=_
    simp only [List.length_append,pow_add,List.map_cons,List.prod_cons,ih]
lemma system_hardWeight {W H : ℕ} {cs : List (BoundaryChord W H)}
    (hp : ∀ c∈cs,EndPort c.source ∧ EndPort c.target) :
    kappa^(systemNodes cs).length=(cs.map hardWeight).prod := by
  rw [systemNodes_weight]
  apply congrArg List.prod
  apply List.map_congr_left
  intro c hc
  simp only [hardWeight,ite_eq_left (hp c hc)]

theorem hard_wall_partition_bound {W H : ℕ} (x₀ : Assignment (W+1) (H+1))
    (hw : ∀ j,assignmentSpins x₀ (westPort W H j).wire=1)
    (he : ∀ j,assignmentSpins x₀ (eastPort W H j).wire=1) :
    ‖relativePartition x₀‖≤(1+poolMass W H)^(2*(W+1)) := by
  classical
  obtain ⟨S,hS,hN,hB⟩:=actual_partition_component_bound x₀
  have walls : ∀ cs∈S,∃ x : Assignment (W+1) (H+1),SelectedSystem x cs ∧
      (∀ j,assignmentSpins x (westPort W H j).wire=1) ∧
      (∀ j,assignmentSpins x (eastPort W H j).wire=1) := by
    intro cs hc
    obtain ⟨x,hx,hs⟩:=hS cs hc
    exact ⟨x,hs,fun j=>(sameBoundary_port hx _).trans (hw j),
      fun j=>(sameBoundary_port hx _).trans (he j)⟩
  have hn : ∀ cs∈S,cs.length≤2*(W+1) := by
    intro cs hc
    obtain ⟨x,hx,hw,he⟩:=walls cs hc
    exact hx.length_le_width hw he
  have hprod : ∀ cs∈S,kappa^(systemNodes cs).length=(cs.map hardWeight).prod := by
    intro cs hc
    obtain ⟨x,hx,hw,he⟩:=walls cs hc
    exact system_hardWeight (fun c hc=>hx.hard_endpoints hw he hc)
  calc
    _ ≤ ∑ cs∈S,kappa^(systemNodes cs).length := hB
    _ = ∑ cs∈S,(cs.map hardWeight).prod := Finset.sum_congr rfl (fun cs hc=>hprod cs hc)
    _ ≤ (1+∑ c : BoundaryChord W H,hardWeight c)^(2*(W+1)) :=
      ListBound.finite_system_bound hardWeight hardWeight_nonnegative S _ hn
    _ = (1+singleSystemMass W H)^(2*(W+1)) := by rw [sum_hardWeight]
    _ ≤ _ := pow_le_pow_left₀ (by
      have hh : 0 ≤ singleSystemMass W H := Finset.sum_nonneg (fun c hc=>(pow_pos kappa_positive _).le)
      linarith) (by have hh:=singleSystemMass_le W H; linarith) _

theorem eventually_hard_wall_partition_bound (W : ℕ) :
    ∃ C : ℝ,∀ᶠ H : ℕ in atTop,∀ x₀ : Assignment (W+1) (H+1),
      (∀ j,assignmentSpins x₀ (westPort W H j).wire=1)→
      (∀ j,assignmentSpins x₀ (eastPort W H j).wire=1)→‖relativePartition x₀‖≤C := by
  refine ⟨(2+2*archPoolMass W)^(2*(W+1)),?_⟩
  filter_upwards [(poolMass_limit W).eventually_lt_const (show 2*archPoolMass W<1+2*archPoolMass W by linarith)] with H hH
  intro x hw he
  apply (hard_wall_partition_bound x hw he).trans
  apply pow_le_pow_left₀
  · have hn : 0≤poolMass W H:=tsum_nonneg poolWeight_nonnegative
    linarith
  · linarith
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology

noncomputable def poolArchHeight {W : ℕ} (a : ArchPool W) : ℕ :=
  a.2.val.toFinset.sup (fun v=>v.2.1.natAbs)
lemma poolArchHeight_ge {W : ℕ} (a : ArchPool W) {v : Center} (hv : v∈a.2.val) :
    v.2.1≤(poolArchHeight a:ℤ) := by
  have hn : v.2.1.natAbs≤poolArchHeight a:=Finset.le_sup (f:=fun v : Center=>v.2.1.natAbs) (List.mem_toFinset.mpr hv)
  have ha : v.2.1≤(v.2.1.natAbs:ℤ):=Int.le_natAbs
  omega
noncomputable def archTailWeight {W : ℕ} (k : ℕ) (a : ArchPool W) : ℝ :=
  if k≤poolArchHeight a then archPoolWeight a else 0
noncomputable def archTailMass (W k : ℕ) : ℝ := ∑' a : ArchPool W,archTailWeight k a
lemma archTailWeight_nonnegative {W k : ℕ} (a : ArchPool W) : 0≤archTailWeight k a := by
  unfold archTailWeight
  split_ifs
  · exact (pow_pos kappa_positive _).le
  · exact le_refl _
lemma archTailWeight_le {W k : ℕ} (a : ArchPool W) : archTailWeight k a≤archPoolWeight a := by
  unfold archTailWeight
  split_ifs
  · exact le_refl _
  · exact (pow_pos kappa_positive _).le
lemma archTail_summable (W k : ℕ) : Summable (archTailWeight (W:=W) k) :=
  (archPool_summable W).of_nonneg_of_le (fun a=>archTailWeight_nonnegative a) (fun a=>archTailWeight_le a)
lemma archTailMass_limit (W : ℕ) : Tendsto (archTailMass W) atTop (𝓝 0) := by
  classical
  have ht : Tendsto (fun k=>∑' a : ArchPool W,archTailWeight k a) atTop (𝓝 (∑' _a : ArchPool W,(0:ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence (archPool_summable W)
    · intro a
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (poolArchHeight a)] with k hk
      simp only [archTailWeight,ite_eq_right (not_le_of_gt hk)]
    · apply Eventually.of_forall
      intro k a
      rw [Real.norm_eq_abs,abs_of_nonneg (archTailWeight_nonnegative a)]
      exact archTailWeight_le a
  change Tendsto (fun k=>∑' a : ArchPool W,archTailWeight k a) atTop (𝓝 0)
  simpa only [tsum_zero] using ht

noncomputable def badPoolWeight {W H : ℕ} (k : ℕ) : OnePathPool W H→ℝ
  | .inl (.inl a)=>archTailWeight k a
  | .inl (.inr a)=>archTailWeight k a
  | .inr (.inl a)=>bridgePoolWeight a
  | .inr (.inr a)=>bridgePoolWeight a
noncomputable def badPoolMass (W H k : ℕ) : ℝ := ∑' a : OnePathPool W H,badPoolWeight k a
lemma badPoolWeight_nonnegative {W H k : ℕ} (a : OnePathPool W H) : 0≤badPoolWeight k a := by
  rcases a with (a|a)|(a|a)
  · exact archTailWeight_nonnegative a
  · exact archTailWeight_nonnegative a
  · exact (pow_pos kappa_positive _).le
  · exact (pow_pos kappa_positive _).le
lemma badPoolWeight_le {W H k : ℕ} (a : OnePathPool W H) : badPoolWeight k a≤poolWeight a := by
  rcases a with (a|a)|(a|a)
  · exact archTailWeight_le a
  · exact archTailWeight_le a
  · exact le_refl _
  · exact le_refl _
lemma badPool_summable (W H k : ℕ) : Summable (badPoolWeight (W:=W) (H:=H) k) :=
  (pool_summable W H).of_nonneg_of_le badPoolWeight_nonnegative badPoolWeight_le
lemma badPoolMass_eq (W H k : ℕ) : badPoolMass W H k=2*archTailMass W k+2*bridgePoolMass W H := by
  have ht : HasSum (badPoolWeight (W:=W) (H:=H) k)
      ((archTailMass W k+archTailMass W k)+(bridgePoolMass W H+bridgePoolMass W H)) := by
    apply HasSum.sum
    · apply HasSum.sum
      · exact (archTail_summable W k).hasSum
      · exact (archTail_summable W k).hasSum
    · apply HasSum.sum
      · exact hasSum_fintype _
      · exact hasSum_fintype _
  change (∑' a : OnePathPool W H,badPoolWeight k a)=_
  rw [ht.tsum_eq]
  ring
lemma nat_half_tendsto : Tendsto (fun H : ℕ=>H/2) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (2*k)] with H hH
  omega
lemma badPoolMass_limit (W : ℕ) : Tendsto (fun H=>badPoolMass W H (H/2)) atTop (𝓝 0) := by
  simp_rw [badPoolMass_eq]
  simpa using ((archTailMass_limit W).comp nat_half_tendsto |>.const_mul 2).add ((bridgePoolMass_limit W).const_mul 2)

lemma pool_midrow_weight {W H : ℕ} (a : OnePathPool W H)
    (hm : ∃ v∈recoverTrace a,v.2.1=(H/2:ℕ)) :
    badPoolWeight (H/2) a=poolWeight a := by
  classical
  obtain ⟨v,hv,hy⟩:=hm
  rcases a with (a|a)|(a|a)
  · change archTailWeight (H/2) a=archPoolWeight a
    unfold archTailWeight
    rw [ite_eq_left]
    have hh:=poolArchHeight_ge a hv
    omega
  · change archTailWeight (H/2) a=archPoolWeight a
    unfold archTailWeight
    rw [ite_eq_left]
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hv
    have hh:=poolArchHeight_ge a hu
    change (H:ℤ)-u.2.1=(H/2:ℕ) at hy
    omega
  · rfl
  · rfl

lemma HardChord.midrow_weight {W H : ℕ} (c : HardChord W H)
    (hm : ∃ v∈c.val.chord.val,v.2.1=(H/2:ℕ)) :
    badPoolWeight (H/2) c.encode=poolWeight c.encode := by
  apply pool_midrow_weight
  simpa only [c.recover_encode] using hm
end CriticalHoneycomb.Transfer.RasterGrid

end

end OAI
