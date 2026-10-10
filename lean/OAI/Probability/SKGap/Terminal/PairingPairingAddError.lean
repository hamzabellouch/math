import Mathlib
import OAI.Probability.SKGap.Localization.SumPoissonMass
import OAI.Probability.SKGap.Gaussian.GaussianPDFMoment
import OAI.Probability.SKGap.Localization.IntegrableMulBounded

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKGapCutoff.Clock

lemma pairing_le_pairing_add_error {f g u : ℝ → ℝ} {B : ℝ}
    (hf : Integrable f) (hg : Integrable g) (hu : AEStronglyMeasurable u)
    (hb : ∀ x, |u x| ≤ B) :
    |∫ x : ℝ, f x*u x| ≤ |∫ x : ℝ, g x*u x|+B*(∫ x : ℝ, |f x-g x|) := by
  have hh := pairing_sub_abs_le hf hg hu hb
  have htri := norm_le_norm_sub_add (∫ x : ℝ, f x*u x) (∫ x : ℝ, g x*u x)
  simp only [Real.norm_eq_abs] at htri
  linarith

lemma pairing_finite_error_bound {ρ : ℝ → ℝ} {φ : ℝ → ℝ → ℝ}
    {u : ℝ → ℝ} {B : ℝ} (hρ : Integrable ρ) (hφ : ∀ y, Integrable (φ y))
    (hu : AEStronglyMeasurable u) (hb : ∀ x, |u x| ≤ B)
    (s : Finset ℝ) (c : ℝ → ℝ) :
    |∫ x : ℝ, ρ x*u x| ≤ B*(∫ x : ℝ, |ρ x-∑ y ∈ s, c y*φ y x|)+
      ∑ y ∈ s, |c y| * |∫ x : ℝ, φ y x*u x| := by
  let F : ℝ → ℝ := fun x => ∑ y ∈ s, c y*φ y x
  have hF : Integrable F := integrable_finsetSum _ (fun y _ => (hφ y).const_mul (c y))
  have hh := pairing_le_pairing_add_error hρ hF hu hb
  have he : (∫ x : ℝ, F x*u x) = ∑ y ∈ s, c y*(∫ x : ℝ, φ y x*u x) := by
    unfold F
    simp_rw [Finset.sum_mul,mul_assoc]
    rw [integral_finsetSum s (fun y _ => (integrable_mul_bounded (hφ y) hu hb).const_mul (c y))]
    simp only [integral_const_mul]
  rw [he] at hh
  have hs := Finset.abs_sum_le_sum_abs (fun y => c y*(∫ x : ℝ, φ y x*u x)) s
  simp only [abs_mul] at hs
  linarith

theorem clock_finite_error_bound {q B : ℝ} (hq : 0 < q) (hq1 : q < 1) (hB : 0 ≤ B)
    {M : ℕ} (hM : 0 < M) (a : ℕ → ℝ) (ha : ∀ j, |a j| ≤ B)
    (s : Finset ℝ) (c : ℝ → ℝ) :
    |∑' j, binomialMass q M j*a j| ≤
      B*(∫ x : ℝ, |histogram q M (binomialMass q M) x-
        gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hq.le (by linarith)⟩ x|)+
      B*(∫ x : ℝ, |gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hq.le (by linarith)⟩ x-
        ∑ y ∈ s, c y*gaussianPDFReal (-y) ⟨q,hq.le⟩ x|)+
      ∑ y ∈ s, |c y| * (|∑' j, poissonMass (q*M+(-y)*Real.sqrt M) j*a j|+
        B*(∫ x : ℝ, |histogram q M (poissonMass (q*M+(-y)*Real.sqrt M)) x-
          gaussianPDFReal (-y) ⟨q,hq.le⟩ x|)) := by
  let u : ℝ → ℝ := testHistogram q M a
  have hu : AEStronglyMeasurable u := (measurable_testHistogram q M a).aestronglyMeasurable
  have hub : ∀ x, |u x| ≤ B := testHistogram_bound hB ha q M
  let ψ := gaussianPDFReal 0 ⟨q*(1-q),mul_nonneg hq.le (by linarith)⟩
  let φ : ℝ → ℝ → ℝ := fun y => gaussianPDFReal (-y) ⟨q,hq.le⟩
  have hψ : Integrable ψ := integrable_gaussianPDFReal _ _
  have hφ (y) : Integrable (φ y) := integrable_gaussianPDFReal _ _
  have hbin := pairing_le_pairing_add_error
    (integrable_histogram (hasSum_binomialMass q M) q hM) hψ hu hub
  rw [integral_histogram_test (hasSum_binomialMass q M).summable ha q hM] at hbin
  have hfin := pairing_finite_error_bound hψ hφ hu hub s c
  have hpoi (y : ℝ) : |∫ x : ℝ, φ y x*u x| ≤
      |∑' j, poissonMass (q*M+(-y)*Real.sqrt M) j*a j|+
      B*(∫ x : ℝ, |histogram q M (poissonMass (q*M+(-y)*Real.sqrt M)) x-φ y x|) := by
    have hp := pairing_le_pairing_add_error (hφ y)
      (integrable_histogram (hasSum_poissonMass (q*M+(-y)*Real.sqrt M)) q hM) hu hub
    rw [integral_histogram_test (hasSum_poissonMass _).summable ha q hM] at hp
    simpa only [abs_sub_comm] using hp
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ s) =>
    mul_le_mul_of_nonneg_left (hpoi y) (abs_nonneg (c y)))
  linarith

theorem finite_clock_certificate {q B ε : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hB : 0 < B) (hε : 0 < ε) :
    ∃ (s : Finset ℝ) (δ : ℝ), 0 < δ ∧ ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      ∀ a : ℕ → ℝ, (∀ j, |a j| ≤ B) →
      (∀ y ∈ s, |∑' j, poissonMass (q*M+(-y)*Real.sqrt M) j*a j| < δ) →
      |∑' j, binomialMass q M j*a j| < ε := by
  let v : ℝ≥0 := ⟨q,hq.le⟩
  let w : ℝ≥0 := ⟨q*(1-q),mul_nonneg hq.le (by linarith)⟩
  have hv : 0 < v := hq
  have hw : 0 < w := mul_pos hq (by linarith)
  have hwv : w ≤ v := by change q*(1-q) ≤ q; nlinarith [sq_nonneg q]
  have htol : 0 < ε/(4*B) := by positivity
  obtain ⟨s,c,happrox⟩ := finite_gaussianPDF_approximation hv hw hwv htol
  let A : ℝ := (∑ y ∈ s, |c y|)+1
  have hS : 0 ≤ ∑ y ∈ s, |c y| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hA : 0 < A := by dsimp [A]; linarith
  let δ := ε/(4*A*(B+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 4*A*(B+1)*δ = ε := by
    dsimp [δ]; field_simp
  have hBin : ∀ᶠ M in atTop,
      (∫ x : ℝ, |histogram q M (binomialMass q M) x-gaussianPDFReal 0 w x|) < ε/(4*B) :=
    (binomial_density_L1 hq hq1).eventually (gt_mem_nhds htol)
  have hPoi : ∀ᶠ M in atTop, ∀ y ∈ s,
      (∫ x : ℝ, |histogram q M (poissonMass (q*M+(-y)*Real.sqrt M)) x-
        gaussianPDFReal (-y) v x|) < δ := by
    apply s.eventually_all.mpr
    intro y _
    exact (poisson_density_L1 hq (-y)).eventually (gt_mem_nhds hδ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hBin.and (hPoi.and (eventually_gt_atTop 0)))
  refine ⟨s,δ,hδ,N,?_⟩
  intro M hM a ha hp
  obtain ⟨hb,hpL,hM0⟩ := hN M hM
  have hbound := clock_finite_error_bound hq hq1 hB.le hM0 a ha s c
  have hb' : B*(∫ x : ℝ, |histogram q M (binomialMass q M) x-
      gaussianPDFReal 0 w x|) < ε/4 := by
    have := (lt_div_iff₀ (by positivity : 0 < 4*B)).mp hb
    linarith
  have ha' : B*(∫ x : ℝ, |gaussianPDFReal 0 w x-
      ∑ y ∈ s, c y*gaussianPDFReal (-y) v x|) < ε/4 := by
    have := (lt_div_iff₀ (by positivity : 0 < 4*B)).mp happrox
    linarith
  have hs : (∑ y ∈ s, |c y| * (|∑' j,
      poissonMass (q*M+(-y)*Real.sqrt M) j*a j|+
        B*(∫ x : ℝ, |histogram q M (poissonMass (q*M+(-y)*Real.sqrt M)) x-
          gaussianPDFReal (-y) v x|))) ≤ (∑ y ∈ s, |c y|)*((B+1)*δ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y hy
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := hp y hy
    have := mul_lt_mul_of_pos_left (hpL y hy) hB
    nlinarith
  have hs' : (∑ y ∈ s, |c y|)*((B+1)*δ) ≤ ε/4 := by
    have hx : (∑ y ∈ s, |c y|) ≤ A := by dsimp [A]; linarith
    have := mul_le_mul_of_nonneg_right hx (show 0 ≤ (B+1)*δ by positivity)
    nlinarith [hδeq]
  change |∑' j, binomialMass q M j*a j| ≤ _ at hbound
  linarith

end SKGapCutoff.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end

end OAI
