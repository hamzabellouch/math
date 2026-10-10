import OAI.Geometry.SurfaceImmersion.Atlas.CutoffFlatJetBound
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceQuadraticTaylor

namespace OAI

/-! A smooth surface map can be made equal to its actual quadratic jet
near the origin by an arbitrarily small supported C2 change. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance firstJetNormed : NormedAddCommGroup (Base →L[ℝ] ProjectionTarget 3) := inferInstance
local instance firstJetSpace : NormedSpace ℝ (Base →L[ℝ] ProjectionTarget 3) := inferInstance
local instance secondJetNormed : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) := inferInstance
local instance secondJetSpace : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) := inferInstance

theorem exists_local_quadratic_replacement {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ g : Base → ProjectionTarget 3, ContDiff ℝ ∞ g ∧
      g =ᶠ[𝓝 (0 : Base)] surfaceTaylorTwo f ∧
      (∀ x, ρ ≤ ‖x‖ → g x = f x) ∧
      tsupport (g-f) ⊆ closedBall (0 : Base) (ρ/2) ∧
      ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (g-f) x‖ ≤ ε := by
  obtain ⟨C,hC,hbound⟩ := cutoff_flat_jet_bound
  let R := f-surfaceTaylorTwo f
  have hR : ContDiff ℝ ∞ R := hf.sub (surfaceTaylorTwo_smooth f)
  obtain ⟨h0,hD0,hD20⟩ := surfaceTaylorTwo_remainder_jets hf
  let M := ε/(C+1)
  have hM : 0 < M := by dsimp [M]; positivity
  have hCM : C*M ≤ ε := by
    dsimp [M]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hc : ContinuousAt (fderiv ℝ (fderiv ℝ R)) 0 :=
    ((hR.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).continuousAt
  have hevent : ∀ᶠ x in 𝓝 (0 : Base), ‖fderiv ℝ (fderiv ℝ R) x‖ < M := by
    change fderiv ℝ (fderiv ℝ R) 0 = 0 at hD20
    have hn : ‖fderiv ℝ (fderiv ℝ R) 0‖ < M := by simpa only [hD20,norm_zero] using hM
    exact hc.norm.eventually (isOpen_Iio.mem_nhds hn)
  obtain ⟨η,hη,hηbound⟩ := Metric.eventually_nhds_iff.mp hevent
  let r := min ρ (min 1 (η/2))
  have hr : 0 < r := lt_min hρ (lt_min zero_lt_one (half_pos hη))
  have hrρ : r ≤ ρ := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrη : r < η := by
    have h := (min_le_right ρ (min 1 (η/2))).trans (min_le_right 1 (η/2))
    linarith
  have hsecond : ∀ x ∈ closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M := by
    intro x hx
    exact (hηbound ((mem_closedBall.mp hx).trans_lt hrη)).le
  let Q : Base → ProjectionTarget 3 := fun x => shrinkingJetCutoff r x • R x
  have hQ : ContDiff ℝ ∞ Q := (shrinkingJetCutoff_smooth r).smul hR
  have hqbound := hbound R hR h0 hD0 r M hr hr1 hM.le hsecond
  let g := f-Q
  refine ⟨g,hf.sub hQ,?_,?_,?_,?_⟩
  · filter_upwards [shrinkingJetCutoff_germ r] with x hx
    change f x-shrinkingJetCutoff r x • (f x-surfaceTaylorTwo f x) = surfaceTaylorTwo f x
    rw [hx]
    change f x-(1 : ℝ) • (f x-surfaceTaylorTwo f x) = surfaceTaylorTwo f x
    rw [one_smul]
    abel
  · intro x hx
    have hnot : x ∉ tsupport (shrinkingJetCutoff r) := by
      intro hs
      have hm := shrinkingJetCutoff_tsupport hr hs
      have hl : ‖x‖ ≤ r/2 := by simpa only [mem_closedBall,dist_zero_right] using hm
      linarith
    change f x-shrinkingJetCutoff r x • R x = f x
    rw [image_eq_zero_of_notMem_tsupport hnot,zero_smul,sub_zero]
  · have he : g-f = -Q := by
      funext y
      change (f y-Q y)-f y = -Q y
      abel
    rw [he,tsupport_neg]
    exact ((tsupport_smul_subset_left _ _).trans (shrinkingJetCutoff_tsupport hr)).trans
      (closedBall_subset_closedBall (div_le_div_of_nonneg_right hrρ (by norm_num)))
  · intro j hj x
    have he : g-f = -Q := by
      funext y
      change (f y-Q y)-f y = -Q y
      abel
    rw [he,iteratedFDeriv_neg_apply,norm_neg]
    exact (hqbound j hj x).trans hCM

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
