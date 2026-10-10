import OAI.Analysis.DiamondDistortion.RecursiveLenses

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Midpoint
open Filter
variable {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Weak nullity in its exact scalar-functional form, over the real field. -/
def WeaklyNull (z : ℕ → X) : Prop :=
  ∀ f : X →L[ℝ] ℝ,Tendsto (fun n => f (z n)) atTop (𝓝 0)

lemma finite_dimensional_weak_null [FiniteDimensional ℝ Y] (P : X →L[ℝ] Y)
    (z : ℕ → X) (hz : WeaklyNull z) :
    Tendsto (fun n => P (z n)) atTop (𝓝 0) := by
  let e := (Module.finBasis ℝ Y).equivFunL
  have hc (i : Fin (Module.finrank ℝ Y)) :
      Tendsto (fun n => e (P (z n)) i) atTop (𝓝 0) := by
    exact hz ((ContinuousLinearMap.proj i).comp (e.toContinuousLinearMap.comp P))
  have hp : Tendsto (fun n => e (P (z n))) atTop (𝓝 0) := tendsto_pi_nhds.mpr hc
  have hh := (e.symm.continuous.tendsto 0).comp hp
  simpa only [Function.comp_def,e.symm_apply_apply,map_zero] using hh

lemma finite_rank_weak_null (P : X →L[ℝ] X)
    [FiniteDimensional ℝ (LinearMap.range P.toLinearMap)]
    (z : ℕ → X) (hz : WeaklyNull z) :
    Tendsto (fun n => ‖P (z n)‖) atTop (𝓝 0) := by
  let Q : X →L[ℝ] (LinearMap.range P.toLinearMap) :=
    P.codRestrict _ (fun x => ⟨x,rfl⟩)
  have h := (finite_dimensional_weak_null Q z hz).norm
  change Tendsto (fun n => ‖P (z n)‖) atTop (𝓝 ‖(0 : LinearMap.range P.toLinearMap)‖) at h
  simpa only [norm_zero] using h

lemma Heads.weak_pure (A : Heads ι X) {x : X} (z : ℕ → X) (hz : WeaklyNull z)
    {R ε η : ℝ} (hη : 0 < η) (hl : ∀ i,ε ≤ ‖z i‖)
    (hp : ∀ i,‖x+z i‖ ≤ R) (hm : ∀ i,‖x-z i‖ ≤ R) :
    ∃ (H : ι) (p y : X),A.projection H p=p ∧ A.projection H y=0 ∧
      ‖x‖-η ≤ ‖p‖ ∧ ε-η ≤ ‖y‖ ∧ ‖p+y‖ ≤ R+2*η ∧ ‖p-y‖ ≤ R+2*η := by
  obtain ⟨H,p,hP,hclose⟩ := A.approximation x η hη
  let := A.finite H
  have hn := finite_rank_weak_null (A.projection H) z hz
  have he : ∀ᶠ n in atTop,‖A.projection H (z n)‖ < η :=
    hn.eventually (gt_mem_nhds hη)
  obtain ⟨n,hn⟩ := he.exists
  let w := z n
  let P := A.projection H
  have hy : ε-η ≤ ‖w-P w‖ := by
    have h := norm_sub_norm_le w (P w)
    have hw := hl n
    change ε ≤ ‖w‖ at hw
    linarith
  have hpn : ‖x‖-η ≤ ‖p‖ := by linarith [norm_sub_norm_le x p]
  have hpp : ‖p+(w-P w)‖ ≤ R+2*η := by
    have heq : p+(w-P w)=(x+w)-(x-p)-P w := by module
    rw [heq]
    have h := (norm_sub_le ((x+w)-(x-p)) (P w)).trans
      (add_le_add (norm_sub_le (x+w) (x-p)) le_rfl)
    have hw := hp n
    change ‖x+w‖ ≤ R at hw
    linarith
  have hpm : ‖p-(w-P w)‖ ≤ R+2*η := by
    have heq : p-(w-P w)=(x-w)-(x-p)+P w := by module
    rw [heq]
    have h := (norm_add_le ((x-w)-(x-p)) (P w)).trans
      (add_le_add (norm_sub_le (x-w) (x-p)) le_rfl)
    have hw := hm n
    change ‖x-w‖ ≤ R at hw
    linarith
  refine ⟨H,p,w-P w,hP,?_,hpn,hy,hpp,hpm⟩
  dsimp [P]
  rw [map_sub,A.idempotent,sub_self]

end Midpoint

namespace RecursiveApplications
open Midpoint
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma weak_power_lens (A : Heads ι X) {n m : ℕ} {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (hinput : PowerInput A n m c) {x : X} (z : ℕ → X) (hz : WeaklyNull z)
    (hl : ∀ i,ε ≤ ‖z i‖) (hp : ∀ i,‖x+z i‖ ≤ 1) (hm : ∀ i,‖x-z i‖ ≤ 1) :
    ‖x‖ ≤ Real.sqrt (1-c*ε^n) := by
  have hh := positive_limit_le
    (fun η => (1+2*η)^m*(max (‖x‖-η) 0)^2+c*(max (ε-η) 0)^n)
    (fun η => (1+2*η)^(m+2)) (by fun_prop) (by fun_prop) (fun η hη => by
      obtain ⟨H,p,y,hP,hY,hpL,hyL,hpR,hmR⟩ := A.weak_pure z hz hη hl hp hm
      have h := hinput H p y (1+2*η) hP hY (by positivity) hpR hmR
      have hp' := (sq_le_sq₀ (le_max_right _ _) (norm_nonneg _)).mpr
        (max_le hpL (norm_nonneg _))
      have hy' := pow_le_pow_left₀ (le_max_right (ε-η) 0)
        (max_le hyL (norm_nonneg y)) n
      exact (add_le_add
        (mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ (1+2*η)^m))
        (mul_le_mul_of_nonneg_left hy' hc)).trans h)
  simp only [mul_zero,add_zero,sub_zero,one_pow,one_mul,
    max_eq_left (norm_nonneg x),max_eq_left hε.le] at hh
  have hrad : 0 ≤ 1-c*ε^n := by nlinarith [sq_nonneg ‖x‖]
  exact (Real.le_sqrt (norm_nonneg _) hrad).mpr (by linarith)

theorem cubic_weak_lens (A : Heads ι X) (hinput : CubicInput A) {ε : ℝ}
    (hε : 0 < ε) (_hε1 : ε ≤ 1) {x : X} (z : ℕ → X) (hz : WeaklyNull z)
    (hl : ∀ i,ε ≤ ‖z i‖) (hp : ∀ i,‖x+z i‖ ≤ 1) (hm : ∀ i,‖x-z i‖ ≤ 1) :
    ‖x‖ ≤ theta ε := by
  have h := weak_power_lens A (show 0 ≤ c3/(2*Real.sqrt 2) by have := c3_pos; positivity)
    hε (cubic_to_power A hinput) z hz hl hp hm
  have he : 1-c3/(2*Real.sqrt 2)*ε^3=1-c3*ε^3/(2*Real.sqrt 2) := by ring
  simpa only [he,theta] using h

end RecursiveApplications

namespace Midpoint
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Exactly finite-head-supported vectors. For the coordinate models, these are
    the finite coordinate vectors on the allowed ancestral heads. -/
def Heads.FiniteVector (A : Heads ι X) (x : X) : Prop := ∃ H,A.projection H x=x

/-- Coordinate projections commute even when their norms are not uniformly bounded. -/
def Heads.Commutes (A : Heads ι X) : Prop :=
  ∀ H K x,A.projection H (A.projection K x)=A.projection K (A.projection H x)

lemma Heads.finite_tail_approx (A : Heads ι X) (hcomm : A.Commutes)
    (H : ι) {y : X} (hY : A.projection H y=0) {η : ℝ} (hη : 0 < η) :
    ∃ v : X,A.FiniteVector v ∧ A.projection H v=0 ∧ ‖y-v‖ < η := by
  let P := A.projection H
  have hden : 0 < 1+‖P‖ := by positivity
  obtain ⟨K,q,hK,hq⟩ := A.approximation y (η/(1+‖P‖)) (by positivity)
  refine ⟨q-P q,⟨K,?_⟩,?_,?_⟩
  · dsimp [P]
    rw [map_sub,hcomm K H q,hK]
  · dsimp [P]
    rw [map_sub,A.idempotent,sub_self]
  · have he : y-(q-P q)=(y-q)+P (q-y) := by
      rw [map_sub]
      have h : P y=0 := hY
      rw [h]
      module
    rw [he]
    calc
      _ ≤ ‖y-q‖+‖P (q-y)‖ := norm_add_le _ _
      _ ≤ ‖y-q‖+‖P‖*‖q-y‖ := add_le_add le_rfl (P.le_opNorm _)
      _ = (1+‖P‖)*‖y-q‖ := by rw [norm_sub_rev q y]; ring
      _ < (1+‖P‖)*(η/(1+‖P‖)) := mul_lt_mul_of_pos_left hq hden
      _ = η := by field_simp

end Midpoint

namespace RecursiveApplications
open Midpoint
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def FreeRootInput (A : Heads ι X) (γ : ℝ → ℝ → ℝ) : Prop :=
  ∀ ζ : ℝ,0 < ζ → ζ ≤ 2 → 0 < γ 2 (ζ/4) ∧
    ∀ (H : ι) (p y : X),A.projection H p=p → A.projection H y=0 →
      A.FiniteVector y → ‖p+y‖ ≤ 2 → ‖p-y‖ ≤ 2 → ζ ≤ ‖y‖ →
      ‖p‖+2*γ 2 (ζ/4) ≤ (‖p+y‖+‖p-y‖)/2

/-- An admissible positive qualitative choice;
    outside the possible separation range, any number in (0,1) is allowed. -/
def sumEta (γ : ℝ → ℝ → ℝ) (ε : ℝ) : ℝ :=
  if ε ≤ 2 then min (γ 2 (ε/16)) (1/2) else 1/2

lemma sumEta_range (A : Heads ι X) {γ : ℝ → ℝ → ℝ} (hinput : FreeRootInput A γ)
    {ε : ℝ} (hε : 0 < ε) : 0 < sumEta γ ε ∧ sumEta γ ε < 1 := by
  by_cases hε2 : ε ≤ 2
  · have hg := (hinput (ε/4) (by positivity) (by linarith)).1
    have he : ε/4/4=ε/16 := by ring
    rw [he] at hg
    rw [sumEta,ite_eq_left hε2]
    constructor
    · exact lt_min hg (by norm_num)
    · exact (min_le_right _ _).trans_lt (by norm_num)
  · rw [sumEta,ite_eq_right hε2]
    norm_num

theorem free_root_lens (A : Heads ι X) (hcomm : A.Commutes)
    {γ : ℝ → ℝ → ℝ} (hinput : FreeRootInput A γ) {ε : ℝ} (hε : 0 < ε) :
    Diamond.UnitLensBound X ε (1-sumEta γ ε) := by
  intro x z hp hm hs
  by_cases hε2 : ε ≤ 2
  · have hg := hinput (ε/4) (by positivity) (by linarith)
    have heγ : ε/4/4=ε/16 := by ring
    rw [heγ] at hg
    have hcenter : ‖x‖+2*γ 2 (ε/16) ≤ 1 := by
      apply le_of_forall_pos_le_add
      intro η hη
      let δ := min (ε/8) (min (1/4:ℝ) (η/8))
      have hδ : 0 < δ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
      have hδε : δ ≤ ε/8 := min_le_left _ _
      have hδ1 : δ ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
      have hδη : δ ≤ η/8 := (min_le_right _ _).trans (min_le_right _ _)
      obtain ⟨H,p,y,hP,hY,hpL,hyL,hpR,hmR⟩ := A.pure_pair z hδ hp hm hs
      obtain ⟨v,hfinite,hvH,hclose⟩ := A.finite_tail_approx hcomm H hY hδ
      have hv : ε/4 ≤ ‖v‖ := by
        have h := norm_sub_norm_le y v
        linarith
      have hvp : ‖p+v‖ ≤ 1+3*δ := by
        have he : p+v=(p+y)-(y-v) := by module
        rw [he]
        exact (norm_sub_le _ _).trans (by linarith)
      have hvm : ‖p-v‖ ≤ 1+3*δ := by
        have he : p-v=(p-y)+(y-v) := by module
        rw [he]
        exact (norm_add_le _ _).trans (by linarith)
      have hgain := hg.2 H p v hP hvH hfinite (hvp.trans (by linarith))
        (hvm.trans (by linarith)) hv
      linarith
    rw [sumEta,ite_eq_left hε2]
    have hmin : min (γ 2 (ε/16)) (1/2) ≤ γ 2 (ε/16) := min_le_left _ _
    linarith [hg.1]
  · have h0 := Diamond.norm_deviation_le (hp 0) (hm 0)
    have h1 := Diamond.norm_deviation_le (hp 1) (hm 1)
    have hdist := (norm_sub_le (z 0) (z 1)).trans (add_le_add h0 h1)
    have hsep := hs 0 1 (by decide)
    linarith

theorem free_root_depth (A : Heads ι X) (hcomm : A.Commutes)
    {γ : ℝ → ℝ → ℝ} (hinput : FreeRootInput A γ) {D s : ℝ}
    (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    D⁻¹ ≤ (1-sumEta γ (2/D))^k := by
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) hf.1
  have hα : 0 < D⁻¹ := inv_pos.mpr hD
  have hα1 : D⁻¹ ≤ 1 := (inv_le_one₀ hD).mpr hf.1
  obtain ⟨hη,hη1⟩ := sumEta_range A hinput (show 0 < 2/D by positivity)
  have hlens : Diamond.UnitLensBound X (2*D⁻¹) (1-sumEta γ (2/D)) := by
    simpa only [div_eq_mul_inv] using free_root_lens A hcomm hinput (show 0 < 2/D by positivity)
  have hnorm := Diamond.upper_one_normalization f hf
  exact Diamond.backward hα hα1 (by linarith) (by linarith) hlens k
    (fun v => (D*s)⁻¹ • f v) (fun u v => (hnorm u v).1) (fun u v => (hnorm u v).2)

end RecursiveApplications

end DiamondDistortion

end

end OAI
