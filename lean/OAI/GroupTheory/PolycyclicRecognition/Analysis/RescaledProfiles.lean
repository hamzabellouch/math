import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledChartDistances
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileCompactness

namespace OAI

/-! # Equicontinuity of actual rescaled map profiles -/

noncomputable section

namespace PolycyclicRecognition

open Module Filter
open scoped Topology NNReal

variable {G W Z : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The map profile on an exponential chart, centered at `x` with suffix `k`. -/
def rescaledMapProfile (J : G → W) (x k : G) (r : ℝ) (φ : Z → G) (z : Z) : W :=
  (Real.exp r)⁻¹ • (J (x * k * φ z) - J x)

theorem rescaledMapProfile_dist_le {K : ℝ≥0} {J : G → W} (hJ : LipschitzWith K J)
    (x k : G) (r : ℝ) (φ : Z → G) (z w : Z) :
    dist (rescaledMapProfile J x k r φ z) (rescaledMapProfile J x k r φ w) ≤
      (K : ℝ) * (dist (φ z) (φ w) / Real.exp r) := by
  have hh := hJ.dist_le_mul (x * k * φ z) (x * k * φ w)
  rw [dist_mul_left] at hh
  have he : dist (rescaledMapProfile J x k r φ z) (rescaledMapProfile J x k r φ w) =
      dist (J (x * k * φ z)) (J (x * k * φ w)) / Real.exp r := by
    simp only [rescaledMapProfile, dist_eq_norm, ← smul_sub,
      sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (Real.exp_pos r), div_eq_mul_inv, mul_comm]
  rw [he]
  calc
    _ ≤ ((K : ℝ) * dist (φ z) (φ w)) / Real.exp r := div_le_div_of_nonneg_right hh (Real.exp_pos r).le
    _ = _ := by ring

variable [TopologicalSpace Z]

omit [IsIsometricSMul G G] in
/-- Continuity at each fixed scale is inherited from the actual chart. -/
theorem continuous_rescaledMapProfile {J : G → W} (hJ : Continuous J)
    (x k : G) (r : ℝ) {φ : Z → G} (hφ : Continuous φ)
    [IsTopologicalGroup G] : Continuous (rescaledMapProfile J x k r φ) := by
  exact continuous_const.smul
    ((hJ.comp (continuous_const.mul hφ)).sub continuous_const)

variable {L A : Type*} [LieRing L] [LieAlgebra ℝ L] {n c : ℕ}

/-- Uniformly Lipschitz maps, arbitrary centers, and arbitrary suffixes have
equicontinuous rescaled profiles once their normalized group charts have the
proved sublinear-distance property. No bound on the centers is required. -/
theorem equicontinuous_rescaled_profiles
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {C : ℝ} (hC : 0 ≤ C)
    (hmetric : ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ 1 →
        dist 1 (Exp v) ≤ C * Real.exp r)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hchart : ∀ i, Continuous (fun z : Fin n → ℝ =>
      Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm z)))
    {K : ℝ≥0} (J : ℕ → A → G → W) (hJ : ∀ i u, LipschitzWith K (J i u))
    (x k : ℕ → A → G) :
    Equicontinuous (fun p : ℕ × A => rescaledMapProfile (J p.1 p.2) (x p.1 p.2)
      (k p.1 p.2) (scale p.1)
      (fun z => Exp ((exponentialRescaleBasis b cost (scale p.1)).equivFun.symm z))) := by
  let φ := fun i z => Exp ((exponentialRescaleBasis b cost (scale i)).equivFun.symm z)
  intro z₀
  let E := fun i z => (K : ℝ) * (dist (φ i z₀) (φ i z) / Real.exp (scale i))
  apply equicontinuousAt_of_continuous_joint_error
    (fun i u => rescaledMapProfile (J i u) (x i u) (k i u) (scale i) (φ i)) E z₀
  · intro i
    exact (continuous_const.mul ((continuous_const.dist (hchart i)).div_const _)).continuousAt
  · intro i
    simp [E]
  · intro i u z
    exact rescaledMapProfile_dist_le (hJ i u) (x i u) (k i u) (scale i) (φ i) z₀ z
  · have hs : Tendsto (fun p : ℕ × (Fin n → ℝ) => scale p.1)
        (atTop ×ˢ 𝓝 z₀) atTop := hscale.comp tendsto_fst
    have hd := rescaled_chart_distance_tendsto_zero b cost hweight Exp hinj hzero hneg
      hadd a hm hC hmetric (fun p : ℕ × (Fin n → ℝ) => scale p.1) hs
      (fun _ => z₀) Prod.snd tendsto_const_nhds tendsto_snd
    simpa only [E, φ, mul_zero] using hd.const_mul (K : ℝ)

end PolycyclicRecognition

end

end OAI
