import Mathlib
import OAI.Combinatorics.StripMass.ReflectionIntegrals
import OAI.Combinatorics.StripMass.ScalarBridge

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical

 

def rotateTriangle (H : ℕ) (v : Triangle) : Triangle :=
  if v.2.1 < H then (-v.1,H-1-v.2.1,!v.2.2) else v

lemma rotateTriangle_band_lt {H : ℕ} {v : Triangle} (h : v.2.1<H) :
    (rotateTriangle H v).2.1<H := by simp only [rotateTriangle,ite_eq_left h]; omega

@[simp] lemma rotateTriangle_up {H : ℕ} (i : ℤ) (j : ℕ) (hj : j<H) :
    rotateTriangle H (up i j)=down (-i) (H-1-j) := by simp [rotateTriangle,up,down,hj]
@[simp] lemma rotateTriangle_down {H : ℕ} (i : ℤ) (j : ℕ) (hj : j<H) :
    rotateTriangle H (down i j)=up (-i) (H-1-j) := by simp [rotateTriangle,up,down,hj]

lemma rotateTriangle_involutive (H : ℕ) : Function.Involutive (rotateTriangle H) := by
  intro v
  by_cases h : v.2.1<H
  · have h' : H-1-v.2.1<H := by omega
    have he : H-1-(H-1-v.2.1)=v.2.1 := by omega
    simp [rotateTriangle,h,h',he]
  · simp [rotateTriangle,h]

lemma adjacent_rotate_iff {H : ℕ} {v w : Triangle} (hv : v.2.1<H) (hw : w.2.1<H) :
    adjacent (rotateTriangle H v) (rotateTriangle H w) ↔ adjacent v w := by
  rcases v with ⟨i,j,b⟩
  rcases w with ⟨i',j',b'⟩
  change j<H at hv
  change j'<H at hw
  cases b <;> cases b' <;> simp [adjacent,upDownAdjacent,rotateTriangle,hv,hw]
  all_goals omega

lemma PathBetween.rotate {H : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) :
    PathBetween H (rotateTriangle H a) (rotateTriangle H b) (p.map (rotateTriangle H)) := by
  refine ⟨?_,?_,hp.2.2.1.map (rotateTriangle_involutive H).injective,?_,?_⟩
  · rw [List.head?_map,hp.1]; rfl
  · rw [List.getLast?_map,hp.2.1]; rfl
  · apply (List.isChain_map _).mpr
    apply hp.2.2.2.1.imp_of_mem_imp
    intro v w hv hw h
    exact (adjacent_rotate_iff (hp.2.2.2.2 v hv) (hp.2.2.2.2 w hw)).mpr h
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact rotateTriangle_band_lt (hp.2.2.2.2 w hw)

lemma PathBetween.append_vertex {H : ℕ} {a b v : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) (hv : v.2.1<H) (hn : v∉p) (hab : adjacent b v) :
    PathBetween H a v (p++[v]) := by
  refine ⟨?_,by simp,?_,?_,?_⟩
  · rw [List.head?_append,hp.1]; rfl
  · apply List.nodup_append.mpr
    refine ⟨hp.2.2.1,by simp,?_⟩
    intro x hx y hy hxy
    have hyv := List.mem_singleton.mp hy
    exact hn ((hxy.trans hyv) ▸ hx)
  · apply List.isChain_append.mpr
    refine ⟨hp.2.2.2.1,by simp,?_⟩
    simpa [hp.2.1] using hab
  · intro w hw
    rcases List.mem_append.mp hw with hw|hw
    · exact hp.2.2.2.2 w hw
    · simpa using List.mem_singleton.mp hw ▸ hv

 

def stepSideWeight (N : ℕ) (s i : ℤ) (p : List Triangle) : ℝ :=
  if PathBetween (N+1) (up i 0) (up s N) p ∧ (∀ v∈p,steppedDomain N s v)
  then rho^p.length else 0

def stepSideKernel (N : ℕ) (s i : ℤ) : ℝ := ∑' p,stepSideWeight N s i p

def stepSideMass (N : ℕ) (s : ℤ) : ℝ := ∑' i,stepSideKernel N s i

lemma stepSideWeight_nonneg (N : ℕ) (s i : ℤ) (p : List Triangle) :
    0 ≤ stepSideWeight N s i p := by
  unfold stepSideWeight
  split
  · exact (pow_pos rho_pos _).le
  · exact le_rfl

 

def sideToTallBridge (N : ℕ) (s : ℤ) (p : List Triangle) : List Triangle :=
  (((p++[down (s-1) N]).reverse).map (rotateTriangle (N+1))).map (translateTriangle (s-1))

lemma sideToTallBridge_injective (N : ℕ) (s : ℤ) :
    Function.Injective (sideToTallBridge N s) := by
  intro p q h
  have h₁ := List.map_injective_iff.mpr (translateTriangle_injective (s-1))
  have h₂ := List.map_injective_iff.mpr (rotateTriangle_involutive (N+1)).injective
  unfold sideToTallBridge at h
  exact List.append_cancel_right ((List.reverse_inj).mp (h₂ (h₁ h)))

lemma sideToTallBridge_spec {N : ℕ} (s i : ℤ) {p : List Triangle}
    (hp : PathBetween (N+1) (up i 0) (up s N) p)
    (hD : ∀ v∈p,steppedDomain N s v) :
    IsPath (N+1) (down (s-1-i) N) (sideToTallBridge N s p) := by
  have hn : down (s-1) N ∉ p := by
    intro h
    have hh := hD _ h
    simp only [steppedDomain,down,lt_self_iff_false,false_or,true_and] at hh
    omega
  have hA : adjacent (up s N) (down (s-1) N) := by
    apply Or.inl
    exact ⟨rfl,rfl,Or.inl ⟨rfl,Or.inr (by change s-1+1=s; omega)⟩⟩
  have he := ((hp.append_vertex (Nat.lt_succ_self N) hn hA).reverse.rotate).translate (s-1)
  have h₀ : 0<N+1 := by omega
  simpa [sideToTallBridge,rotateTriangle_down,rotateTriangle_up,h₀,
    Nat.lt_succ_self,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using he

lemma sideToTallBridge_weight (N : ℕ) (s i : ℤ) (p : List Triangle) :
    rho * stepSideWeight N s i p ≤ bridgeWeight (N+1) (s-1-i) (sideToTallBridge N s p) := by
  unfold stepSideWeight
  split_ifs with hp
  · rw [bridgeWeight,ite_eq_left ⟨by omega,sideToTallBridge_spec s i hp.1 hp.2⟩]
    simp [sideToTallBridge,pow_succ,mul_comm]
  · simp only [mul_zero]
    exact bridgeWeight_nonneg _ _ _

lemma bridge_all_paths_summable {H : ℕ} (hH : StripSumsFinite H) :
    Summable (fun x : ℤ×List Triangle => bridgeWeight H x.1 x.2) := by
  apply (summable_prod_of_nonneg (fun x => bridgeWeight_nonneg _ _ _)).mpr
  exact ⟨hH.2.1,hH.2.2.2.1⟩

lemma bridge_all_paths_tsum {H : ℕ} (hH : StripSumsFinite H) :
    (∑' x : ℤ×List Triangle,bridgeWeight H x.1 x.2)=bridgeMass H :=
  (bridge_all_paths_summable hH).tsum_prod

 

theorem stepSideWeight_summable {N : ℕ} (s : ℤ) (h : StripSumsFinite (N+1)) :
    Summable (fun x : ℤ×List Triangle =>stepSideWeight N s x.1 x.2) := by
  let e : (ℤ×List Triangle) → (ℤ×List Triangle) :=
    fun x => (s-1-x.1,sideToTallBridge N s x.2)
  have he : Function.Injective e := by
    intro x y h
    have hi := congrArg Prod.fst h
    have hp := (sideToTallBridge_injective N s) (congrArg Prod.snd h)
    have hxy : x.1=y.1 := by dsimp [e] at hi; omega
    exact Prod.ext hxy hp
  have hg := (bridge_all_paths_summable h).comp_injective he
  have hmul : Summable (fun x : ℤ×List Triangle =>rho * stepSideWeight N s x.1 x.2) :=
    hg.of_nonneg_of_le (fun x =>mul_nonneg rho_pos.le (stepSideWeight_nonneg _ _ _ _))
      (fun x =>sideToTallBridge_weight N s x.1 x.2)
  exact (summable_mul_left_iff rho_pos.ne').mp hmul

theorem stepSideMass_le_tall_bridge {N : ℕ} (s : ℤ) (h : StripSumsFinite (N+1)) :
    rho * stepSideMass N s ≤ bridgeMass (N+1) := by
  let e : (ℤ×List Triangle) → (ℤ×List Triangle) :=
    fun x => (s-1-x.1,sideToTallBridge N s x.2)
  have he : Function.Injective e := by
    intro x y h
    have hi := congrArg Prod.fst h
    have hp := (sideToTallBridge_injective N s) (congrArg Prod.snd h)
    have hxy : x.1=y.1 := by dsimp [e] at hi; omega
    exact Prod.ext hxy hp
  have hs := stepSideWeight_summable s h
  have hb := bridge_all_paths_summable h
  have ht : rho * stepSideMass N s=∑' x : ℤ×List Triangle,rho * stepSideWeight N s x.1 x.2 := by
    rw [tsum_mul_left,hs.tsum_prod]; rfl
  rw [ht,←bridge_all_paths_tsum h]
  exact (hs.mul_left rho).tsum_le_tsum_of_inj e he (fun _ _ =>bridgeWeight_nonneg _ _ _)
    (fun x =>sideToTallBridge_weight N s x.1 x.2) hb

 

def bridgeToSide (N : ℕ) (s k : ℤ) (p : List Triangle) : List Triangle :=
  p.map (translateTriangle (s-k)) ++ [up s N]

lemma bridgeToSide_injective (N : ℕ) (s k : ℤ) :
    Function.Injective (bridgeToSide N s k) := by
  intro p q h
  exact List.map_injective_iff.mpr (translateTriangle_injective (s-k))
    (List.append_cancel_right h)

lemma bridgeToSide_spec {N : ℕ} (hN : 1≤N) (s k : ℤ) {p : List Triangle}
    (hp : IsPath N (down k (N-1)) p) :
    PathBetween (N+1) (up (s-k) 0) (up s N) (bridgeToSide N s k p) ∧
      (∀ v∈bridgeToSide N s k p,steppedDomain N s v) := by
  have ht : PathBetween N (up (s-k) 0) (down s (N-1)) (p.map (translateTriangle (s-k))) := by
    simpa using (show PathBetween N (up 0 0) (down k (N-1)) p from hp).translate (s-k)
  have hn : up s N ∉ p.map (translateTriangle (s-k)) := by
    intro h
    exact (Nat.lt_irrefl N) (ht.2.2.2.2 _ h)
  have hA : adjacent (down s (N-1)) (up s N) := by
    apply Or.inr
    exact ⟨rfl,rfl,Or.inr ⟨by change N=N-1+1; omega,rfl⟩⟩
  have ht' : PathBetween (N+1) (up (s-k) 0) (down s (N-1)) (p.map (translateTriangle (s-k))) :=
    ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,fun v hv => (ht.2.2.2.2 v hv).trans_le (Nat.le_succ _)⟩
  refine ⟨ht'.append_vertex (Nat.lt_succ_self N) hn hA,?_⟩
  intro v hv
  rcases List.mem_append.mp hv with hv|hv
  · exact Or.inl (ht.2.2.2.2 v hv)
  · have he : v=up s N := List.mem_singleton.mp hv
    rw [he]
    exact Or.inr ⟨rfl,le_rfl⟩

lemma bridgeToSide_weight {N : ℕ} (hN : 1≤N) (s k : ℤ) (p : List Triangle) :
    rho * bridgeWeight N k p ≤ stepSideWeight N s (s-k) (bridgeToSide N s k p) := by
  unfold bridgeWeight
  split_ifs with hp
  · rw [stepSideWeight,ite_eq_left (bridgeToSide_spec hN s k hp.2)]
    simp [bridgeToSide,pow_succ,mul_comm]
  · simp only [mul_zero]
    exact stepSideWeight_nonneg _ _ _ _

 

theorem stepSideMass_ge_base_bridge {N : ℕ} (hN : 1≤N) (s : ℤ)
    (h : StripSumsFinite (N+1)) (h₀ : StripSumsFinite N) :
    rho * bridgeMass N ≤ stepSideMass N s := by
  let e : (ℤ×List Triangle) → (ℤ×List Triangle) :=
    fun x => (s-x.1,bridgeToSide N s x.1 x.2)
  have he : Function.Injective e := by
    intro x y hxy
    have hi := congrArg Prod.fst hxy
    have h₁ : x.1=y.1 := by dsimp [e] at hi; omega
    have hp := congrArg Prod.snd hxy
    change bridgeToSide N s x.1 x.2=bridgeToSide N s y.1 y.2 at hp
    rw [h₁] at hp
    exact Prod.ext h₁ ((bridgeToSide_injective N s y.1) hp)
  have hb := bridge_all_paths_summable h₀
  have hs := stepSideWeight_summable s h
  have hsum : (∑' x : ℤ×List Triangle,stepSideWeight N s x.1 x.2)=stepSideMass N s :=
    hs.tsum_prod
  rw [←hsum,←bridge_all_paths_tsum h₀,←tsum_mul_left]
  exact Summable.tsum_le_tsum_of_inj e he (fun _ _ =>stepSideWeight_nonneg _ _ _ _)
    (fun x =>bridgeToSide_weight hN s x.1 x.2) (hb.mul_left rho) hs

end
 

 

noncomputable section
open scoped BigOperators Classical
open Filter Topology

lemma stepArchKernel_translate (N : ℕ) (s i j q : ℤ) :
    stepArchKernel N s (q+i) (q+j)=stepArchKernel N (s-q) i j := by
  rw [stepArchKernel,←(translatePaths q).tsum_eq]
  exact tsum_congr (stepArchWeight_translate N s i j q)

 
def stepCutKernel (N : ℕ) (s q : ℤ) (x : ℕ×ℕ) : ℝ :=
  stepArchKernel N s (q-(x.1:ℤ)) (q+(x.2:ℤ)+1)

def stepCutMass (N : ℕ) (s q : ℤ) : ℝ := ∑' x,stepCutKernel N s q x

lemma stepCutKernel_eq (N : ℕ) (s q : ℤ) (x : ℕ×ℕ) :
    stepCutKernel N s q x=(∑' p,stepCutArchWeight N (s-q) (x,p)) := by
  have ha : q-(x.1:ℤ)=q+(-(x.1:ℤ)) := by ring
  have hb : q+(x.2:ℤ)+1=q+((x.2:ℤ)+1) := by ring
  rw [stepCutKernel,ha,hb,stepArchKernel_translate]
  rfl

lemma stepCutKernel_summable {N : ℕ} (s q : ℤ) (h : StripSumsFinite (N+1)) :
    Summable (stepCutKernel N s q) := by
  exact (stepCutArchWeight_summable N (s-q) h).prod.congr
    (fun x => (stepCutKernel_eq N s q x).symm)

lemma stepCutMass_eq {N : ℕ} (s q : ℤ) (h : StripSumsFinite (N+1)) :
    stepCutMass N s q=∑' x,stepCutArchWeight N (s-q) x := by
  rw [stepCutMass,(stepCutArchWeight_summable N (s-q) h).tsum_prod]
  exact tsum_congr (stepCutKernel_eq N s q)

 
lemma tsum_prod_split_column {f : ℕ×ℕ → ℝ} (hf : Summable f) :
    (∑' x,f x)=(∑' a,f (a,0))+(∑' a,∑' b,f (a,b+1)) := by
  have h₀ : Summable (fun a : ℕ =>f (a,0)) :=
    hf.comp_injective (fun a b h =>congrArg Prod.fst h)
  have ht : Summable (fun x : ℕ×ℕ =>f (x.1,x.2+1)) :=
    hf.comp_injective (by intro a b h; apply Prod.ext <;> simp_all)
  rw [hf.tsum_prod,←h₀.tsum_add ht.prod]
  exact tsum_congr (fun a => (hf.prod_factor a).tsum_eq_zero_add)

 

lemma tsum_array_difference {f g : ℕ×ℕ → ℝ} (hf : Summable f) (hg : Summable g)
    (hfg : ∀ a b,f (a,b+1)=g (a+1,b)) :
    (∑' x,f x)-(∑' x,g x)=(∑' a,f (a,0))-(∑' b,g (0,b)) := by
  rw [tsum_prod_split_column hf,hg.tsum_prod,hg.prod.tsum_eq_zero_add]
  have ht : (∑' a,∑' b,f (a,b+1))=∑' a,∑' b,g (a+1,b) :=
    tsum_congr (fun a =>tsum_congr (fun b =>hfg a b))
  rw [ht]
  ring

def stepArchLeft (N : ℕ) (s i : ℤ) : ℝ :=
  ∑' j : ℕ,stepArchKernel N s i (i-1-(j:ℤ))

def stepArchRight (N : ℕ) (s i : ℤ) : ℝ :=
  ∑' j : ℕ,stepArchKernel N s i (i+(j:ℤ)+1)

 

theorem step_cut_divergence {N : ℕ} (s i : ℤ) (h : StripSumsFinite (N+1)) :
    stepCutMass N s (i-1)-stepCutMass N s i=stepArchLeft N s i-stepArchRight N s i := by
  have he (a b : ℕ) : stepCutKernel N s (i-1) (a,b+1)=stepCutKernel N s i (a+1,b) := by
    unfold stepCutKernel
    congr 1 <;> push_cast <;> ring
  have hh := tsum_array_difference (stepCutKernel_summable s (i-1) h)
    (stepCutKernel_summable s i h) he
  have hl : (∑' a,stepCutKernel N s (i-1) (a,0))=stepArchLeft N s i := by
    apply tsum_congr
    intro a
    simp only [stepCutKernel,Nat.cast_zero,add_zero,sub_add_cancel]
    exact stepArchKernel_reverse _ _ _ _
  have hr : (∑' b,stepCutKernel N s i (0,b))=stepArchRight N s i := by
    simp only [stepCutKernel,Nat.cast_zero,sub_zero,stepArchRight]
  rw [hl,hr] at hh
  exact hh

 

def SteppedBoundaryFlux (N : ℕ) (s : ℤ) : Prop :=
  ∀ i : ℤ, Real.sin (3*lambda)*(stepArchLeft N s i-stepArchRight N s i)+
    Real.sin lambda*stepSideKernel N s i=0

lemma stepSideKernel_summable {N : ℕ} (s : ℤ) (h : StripSumsFinite (N+1)) :
    Summable (stepSideKernel N s) := (stepSideWeight_summable s h).prod

 

theorem step_moment_identity {N : ℕ} (s : ℤ)
    (h : StripSumsFinite (N+1)) (h₀ : StripSumsFinite N)
    (hflux : SteppedBoundaryFlux N s) :
    Real.sin (3*lambda)*(moment (N+1)-moment N)=Real.sin lambda*stepSideMass N s := by
  have hfin (L : ℕ) : Real.sin (3*lambda)*
      (stepCutMass N s ((L:ℤ)-1)-stepCutMass N s (-(L:ℤ)-1)) =
      Real.sin lambda * ∑ i ∈ Finset.Ico (-(L:ℤ)) (L:ℤ),stepSideKernel N s i := by
    have hi (i : ℤ) : Real.sin lambda*stepSideKernel N s i=
        Real.sin (3*lambda)*(stepCutMass N s i-stepCutMass N s (i-1)) := by
      have hx := hflux i
      rw [←step_cut_divergence s i h] at hx
      linarith
    rw [Finset.mul_sum]
    simp_rw [hi]
    rw [←Finset.mul_sum]
    congr 1
    have hz := Finset.sum_Ico_int_sub L (fun i => stepCutMass N s (i-1))
    have hadd : ∀ i : ℤ,(i+1)-1=i := by intro i; ring
    simp only [hadd] at hz
    have hn : (∑ i ∈ Finset.Ico (-(L:ℤ)) (L:ℤ),
        (stepCutMass N s i-stepCutMass N s (i-1)))=
        -(∑ i ∈ Finset.Ico (-(L:ℤ)) (L:ℤ),
        (stepCutMass N s (i-1)-stepCutMass N s i)) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hn,hz]
    ring
  have hr : Tendsto (fun L : ℕ=>stepCutMass N s ((L:ℤ)-1)) atTop (𝓝 (moment (N+1))) := by
    have he (L : ℕ) : stepCutMass N s ((L:ℤ)-1)=∑' x,stepCutArchWeight N ((s+1)-(L:ℤ)) x := by
      rw [stepCutMass_eq s _ h]
      congr 3
      ring_nf
    simpa only [he] using step_cut_mass_tall_limit (s+1) h
  have hl : Tendsto (fun L : ℕ=>stepCutMass N s (-(L:ℤ)-1)) atTop (𝓝 (moment N)) := by
    have he (L : ℕ) : stepCutMass N s (-(L:ℤ)-1)=∑' x,stepCutArchWeight N ((s+1)+(L:ℤ)) x := by
      rw [stepCutMass_eq s _ h]
      congr 3
      ring_nf
    simpa only [he] using step_cut_mass_short_limit (s+1) h h₀
  have hz : Tendsto (fun L : ℕ=>∑ i ∈ Finset.Ico (-(L:ℤ)) (L:ℤ),stepSideKernel N s i)
      atTop (𝓝 (stepSideMass N s)) :=
    (stepSideKernel_summable s h).hasSum.comp Finset.tendsto_Ico_neg
  exact tendsto_nhds_unique ((hr.sub hl).const_mul _) ((hz.const_mul _).congr (fun L=>(hfin L).symm))

end
 

 

noncomputable section
open scoped BigOperators Classical

lemma step_sines_pos : 0 < Real.sin lambda ∧ 0 < Real.sin (3*lambda) := by
  constructor <;> apply Real.sin_pos_of_pos_of_lt_pi <;>
    dsimp [lambda] <;> linarith [Real.pi_pos]

 

theorem moment_increment_bounds_of_boundary {N : ℕ} (hN : 1≤N) (s : ℤ)
    (h : StripSumsFinite (N+1)) (h₀ : StripSumsFinite N)
    (hflux : SteppedBoundaryFlux N s)
    (hF₀ : c*archMass N+bridgeMass N=1)
    (hF₁ : c*archMass (N+1)+bridgeMass (N+1)=1) :
    ((Real.sin lambda/Real.sin (3*lambda))*rho)*bridgeMass N ≤ moment (N+1)-moment N ∧
    moment (N+1)-moment N ≤ ((Real.sin lambda/Real.sin (3*lambda))/rho)*bridgeMass N := by
  have hs := step_sines_pos
  have he := step_moment_identity s h h₀ hflux
  have hm : moment (N+1)-moment N =
      (Real.sin lambda / Real.sin (3*lambda))*stepSideMass N s := by
    apply (mul_left_cancel₀ hs.2.ne')
    calc
      Real.sin (3*lambda)*(moment (N+1)-moment N)=
        Real.sin lambda*stepSideMass N s := he
      _=Real.sin (3*lambda)*((Real.sin lambda/Real.sin (3*lambda))*stepSideMass N s) := by
        field_simp [hs.2.ne']
  have hmono : bridgeMass (N+1)≤bridgeMass N :=
    bridgeMass_le_of_finite_and_flux (Nat.le_succ N) h hF₀ hF₁
  have hupper : rho*stepSideMass N s≤bridgeMass N := (stepSideMass_le_tall_bridge s h).trans hmono
  have hlower := stepSideMass_ge_base_bridge hN s h h₀
  have hβ : 0≤Real.sin lambda/Real.sin (3*lambda) := (div_pos hs.1 hs.2).le
  constructor
  · rw [hm,mul_assoc]
    exact mul_le_mul_of_nonneg_left hlower hβ
  · have hsu : stepSideMass N s≤bridgeMass N/rho :=
      (le_div_iff₀ rho_pos).mpr (by simpa [mul_comm] using hupper)
    have hu := mul_le_mul_of_nonneg_left hsu hβ
    simpa only [hm,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hu

 

theorem increment_comparable_of_boundary
    (hfinite : ∀ N : ℕ,1≤N → StripSumsFinite N)
    (hstrip : ∀ N : ℕ,1≤N → c*archMass N+bridgeMass N=1)
    (hstep : ∀ N : ℕ,1≤N → ∃ s : ℤ,SteppedBoundaryFlux N s) :
    Comparable (fun N =>moment (N+1)-moment N) bridgeMass := by
  have hs := step_sines_pos
  refine ⟨(Real.sin lambda/Real.sin (3*lambda))*rho,
    (Real.sin lambda/Real.sin (3*lambda))/rho,
    mul_pos (div_pos hs.1 hs.2) rho_pos,div_pos (div_pos hs.1 hs.2) rho_pos,?_⟩
  intro N hN
  obtain ⟨s,h⟩ := hstep N hN
  exact moment_increment_bounds_of_boundary hN s (hfinite (N+1) (by omega))
    (hfinite N hN) h (hstrip N hN) (hstrip (N+1) (by omega))

 

theorem criticalStripMass_of_physical_identities
    (hfinite : ∀ N : ℕ,1≤N → StripSumsFinite N)
    (hstrip : ∀ N : ℕ,1≤N → c*archMass N+bridgeMass N=1)
    (hstep : ∀ N : ℕ,1≤N → ∃ s : ℤ,SteppedBoundaryFlux N s)
    (hArch : ∀ N : ℕ,1≤N → ∃ g : Polynomial ℝ,
      MonicProblem N g ∧ moment N=(N:ℝ)*C-eta*g.coeff (N-1)) :
    CriticalStripMass := by
  apply criticalStripMass_iff_four_estimates.mpr
  refine ⟨hfinite,hstrip,increment_comparable_of_boundary hfinite hstrip hstep,?_⟩
  obtain ⟨lo,hi,hl,hh,hg⟩ := homogeneous_arch_coefficient_growth
  refine ⟨lo,hi,hl,hh,?_⟩
  intro N hN
  obtain ⟨g,hgm,he⟩ := hArch N hN
  simpa only [he] using hg N hN g hgm

end
end CriticalStrip

end OAI
