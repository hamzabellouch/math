import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedPotential.MetricLocalization
import OAI.Geometry.PrescribedRicci.UniformFrozenEstimate

namespace OAI

/-! Uniform Coefficient Extension. -/

noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise BoundedContinuousFunction
namespace MetricLocalization
open EllipticKernel FrozenPoisson SobolevChart
variable {n : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem coefficient_extension_on_bump {U : Set (EC n)} (hU : IsOpen U)
    (H : EC n → Matrix (Fin n) (Fin n) ℂ) (hH : ContDiffOn ℝ ∞ H U)
    (hh : ∀ y ∈ U, (H y).PosDef) {x : EC n} (_hx : x ∈ U)
    (v : ι → EC n) (ψ : ContDiffBump x) (hψ : tsupport ψ ⊆ U)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ y ∈ tsupport ψ, ∀ i j,
      |traceBilin (H y) (rankTwo (v i) (v j))-traceBilin (H x) (rankTwo (v i) (v j))| ≤ ε) :
    ∃ a : ι → ι → EC n →ᵇ ℂ,
      (∀ i j, ContDiff ℝ ∞ (a i j : EC n → ℂ)) ∧
      (∀ i j, HasCompactSupport (a i j : EC n → ℂ)) ∧
      (∀ i j, ‖a i j‖ ≤ ε) ∧
      ∀ y ∈ Metric.closedBall x ψ.rIn, ∀ i j,
        a i j y = (traceBilin (H y) (rankTwo (v i) (v j)) : ℂ)-
          (traceBilin (H x) (rankTwo (v i) (v j)) : ℂ) := by
  let F : ι → ι → EC n → ℂ := fun i j y =>
    (traceBilin (H y) (rankTwo (v i) (v j)) : ℂ)-
      (traceBilin (H x) (rankTwo (v i) (v j)) : ℂ)
  let b : ι → ι → EC n → ℂ := fun i j y => ψ y • F i j y
  have hF (i j : ι) : ContDiffOn ℝ ∞ (F i j) U :=
    (trace_coefficient_smooth hH hh _).sub contDiffOn_const
  have hs (i j : ι) : ContDiff ℝ ∞ (b i j) := by
    apply smooth_bump_smul
    intro y hy
    exact (hF i j y (hψ hy)).contDiffAt (hU.mem_nhds (hψ hy))
  have hc (i j : ι) : HasCompactSupport (b i j) := ψ.hasCompactSupport.smul_right
  have hn (i j : ι) (y : EC n) : ‖b i j y‖ ≤ ε := by
    by_cases hy : y ∈ tsupport ψ
    · calc
        _ = ψ y*‖F i j y‖ := by simp [b,abs_of_nonneg ψ.nonneg]
        _ ≤ ‖F i j y‖ := by simpa using mul_le_mul_of_nonneg_right ψ.le_one (norm_nonneg (F i j y))
        _ ≤ ε := by simpa only [F,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hb y hy i j
    · simp [b,image_eq_zero_of_notMem_tsupport hy,hε]
  let a : ι → ι → EC n →ᵇ ℂ := fun i j =>
    BoundedContinuousFunction.ofNormedAddCommGroup (b i j) (hs i j).continuous ε (hn i j)
  refine ⟨a,hs,hc,fun i j => (BoundedContinuousFunction.norm_le hε).mpr (hn i j),?_⟩
  intro y hy i j
  change ψ y • F i j y = F i j y
  rw [ψ.one_of_mem_closedBall hy,one_smul]

lemma perturbationBound_le_of_norm (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    {ε : ℝ} (ha : ∀ i j, ‖a i j‖ ≤ ε) :
    perturbationBound v a ≤ ε*(∑ i, ∑ j, (2*Real.pi)^2*‖v i‖*‖v j‖) := by
  simp only [perturbationBound,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (ha i j) (by positivity)

theorem uniform_coefficient_radius (v : ι → EC n) {M P R : ℝ}
    (hM : 0 ≤ M) (hP : 0 ≤ P) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ∀ (x : EC n) (U : Set (EC n)), IsOpen U → Metric.closedBall x R ⊆ U →
      ∀ (H : EC n → Matrix (Fin n) (Fin n) ℂ), ContDiffOn ℝ ∞ H U →
      (∀ y ∈ U, (H y).PosDef) →
      (∀ y ∈ Metric.closedBall x R, ∀ i j,
        |traceBilin (H y) (rankTwo (v i) (v j))-traceBilin (H x) (rankTwo (v i) (v j))| ≤ P*‖y-x‖) →
      ∃ a : ι → ι → EC n →ᵇ ℂ,
        (∀ i j, ContDiff ℝ ∞ (a i j : EC n → ℂ)) ∧
        (∀ i j, HasCompactSupport (a i j : EC n → ℂ)) ∧
        perturbationBound v a*uniformEllipticBound n M ≤ 1/2 ∧
        ∀ y ∈ Metric.closedBall x (r/2), ∀ i j,
          a i j y = (traceBilin (H y) (rankTwo (v i) (v j)) : ℂ)-
            (traceBilin (H x) (rankTwo (v i) (v j)) : ℂ) := by
  let C := uniformEllipticBound n M
  let Q : ℝ := ∑ i, ∑ j, (2*Real.pi)^2*‖v i‖*‖v j‖
  have hC : 0 < C := uniformEllipticBound_pos hM
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let ε : ℝ := 1/(2*(1+Q*C))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  let r : ℝ := min R (ε/(P+1))
  have hr : 0 < r := lt_min hR (div_pos hε (by linarith only [hP]))
  have hrR : r ≤ R := min_le_left ..
  have hpr : P*r ≤ ε := by
    have h1 := (le_div_iff₀ (by linarith only [hP] : 0 < P+1)).mp (min_le_right R (ε/(P+1)))
    change r*(P+1) ≤ ε at h1
    nlinarith only [h1,hr]
  refine ⟨r,hr,hrR,?_⟩
  intro x U hU hsub H hH hh hosc
  let ψ : ContDiffBump x :=
    { rIn := r/2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  have hs : tsupport ψ ⊆ Metric.closedBall x R := by
    rw [ContDiffBump.tsupport_eq]
    exact Metric.closedBall_subset_closedBall hrR
  obtain ⟨a,ha,hac,han,heq⟩ := coefficient_extension_on_bump hU H hH hh
    (hsub (Metric.mem_closedBall_self hR.le)) v ψ (hs.trans hsub) hε.le (by
      intro y hy i j
      apply (hosc y (hs hy) i j).trans
      apply (mul_le_mul_of_nonneg_left _ hP).trans hpr
      simpa only [ContDiffBump.tsupport_eq,Metric.mem_closedBall,dist_eq_norm,ψ] using hy)
  refine ⟨a,ha,hac,?_,heq⟩
  apply (mul_le_mul_of_nonneg_right (perturbationBound_le_of_norm v a han) hC.le).trans
  change ε*Q*C ≤ 1/2
  have hd : 0 < 2*(1+Q*C) := by positivity
  dsimp only [ε]
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div,one_mul]
  apply (div_le_iff₀ hd).mpr
  nlinarith only [mul_nonneg hQ hC.le]
end MetricLocalization

end

end OAI
