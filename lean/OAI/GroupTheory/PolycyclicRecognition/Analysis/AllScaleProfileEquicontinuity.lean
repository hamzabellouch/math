import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealParameterEquicontinuity

namespace OAI

/-! # Equicontinuity before choosing a sequence of scales -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology NNReal

theorem continuous_scaled_basis_coordinates
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] {n : ℕ}
    (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) :
    Continuous (fun p : ℝ × (Fin n → ℝ) =>
      (exponentialRescaleBasis b cost p.1).equivFun.symm p.2) := by
  simp only [Basis.equivFun_symm_apply, exponentialRescaleBasis, Basis.unitsSMul_apply,
    Units.smul_def, Units.val_mk0]
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_snd).smul
    ((Real.continuous_exp.comp (continuous_fst.mul continuous_const)).smul continuous_const)

theorem continuous_mapped_scaled_basis_coordinates
    {L V : Type*} [LieRing L] [LieAlgebra ℝ L] [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {n : ℕ}
    (e : L →ₗ[ℝ] V) (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) :
    Continuous (fun p : ℝ × (Fin n → ℝ) =>
      e ((exponentialRescaleBasis b cost p.1).equivFun.symm p.2)) := by
  simp only [Basis.equivFun_symm_apply, exponentialRescaleBasis, Basis.unitsSMul_apply,
    Units.smul_def, Units.val_mk0, map_sum, map_smul]
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_snd).smul
    ((Real.continuous_exp.comp (continuous_fst.mul continuous_const)).smul continuous_const)

/-- Uniformity of the actual metric error over all nonnegative real scales.
Compact initial scale intervals and the asymptotic chart estimate give a
single modulus, independent of the eventual sequence. -/
theorem equicontinuous_all_scale_profiles
    {L G W P : Type*} [LieRing L] [LieAlgebra ℝ L]
    [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n c : ℕ}
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
    (hchart : Continuous (fun p : ℝ × (Fin n → ℝ) =>
      Exp ((exponentialRescaleBasis b cost p.1).equivFun.symm p.2)))
    (scale : P → ℝ) (hscale : ∀ p, 0 ≤ scale p)
    {K : ℝ≥0} (J : P → G → W) (hJ : ∀ p, LipschitzWith K (J p))
    (x k : P → G) :
    Equicontinuous (fun p => rescaledMapProfile (J p) (x p) (k p) (scale p)
      (fun z => Exp ((exponentialRescaleBasis b cost (scale p)).equivFun.symm z))) := by
  let φ := fun r z => Exp ((exponentialRescaleBasis b cost r).equivFun.symm z)
  intro z₀
  let E := fun r z => (K : ℝ) * (dist (φ r z₀) (φ r z) / Real.exp r)
  have hE : Continuous (fun p : ℝ × (Fin n → ℝ) => E p.1 p.2) :=
    continuous_const.mul
      (((hchart.comp (continuous_fst.prodMk continuous_const)).dist hchart).div
        (Real.continuous_exp.comp continuous_fst) (fun p => (Real.exp_pos p.1).ne'))
  have htail : Tendsto (fun p : ℝ × (Fin n → ℝ) => E p.1 p.2)
      (atTop ×ˢ 𝓝 z₀) (𝓝 0) := by
    have hd := rescaled_chart_distance_tendsto_zero b cost hweight Exp hinj hzero hneg
      hadd a hm hC hmetric Prod.fst tendsto_fst
      (fun _ => z₀) Prod.snd tendsto_const_nhds tendsto_snd
    simpa only [E, φ, mul_zero] using hd.const_mul (K : ℝ)
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  filter_upwards [uniform_nonnegative_parameter_of_joint_limit E z₀ hE
    (fun r => by simp [E]) htail ε hε] with z hz
  intro p
  exact (rescaledMapProfile_dist_le (hJ p) (x p) (k p) (scale p) (φ (scale p)) z₀ z).trans_lt
    (hz (scale p) (hscale p))

end PolycyclicRecognition

end

end OAI
