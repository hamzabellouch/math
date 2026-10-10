import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ActualHessianForm

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma exists_aligned_unit (a : PhaseSpace) : ∃ ν : PhaseSpace, ‖ν‖ = 1 ∧ a = ‖a‖ • ν := by
  by_cases ha : a = 0
  · refine ⟨EuclideanSpace.single 0 1,by simp,?_⟩
    simp [ha]
  · refine ⟨‖a‖⁻¹ • a,?_,?_⟩
    · rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]
    · rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha),one_smul]

lemma complexPhaseVector_norm_bound (a b : PhaseSpace) :
    ‖complexPhaseVector a b‖ ≤ ‖a‖+‖b‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    _ ≤ ‖(a i : ℂ)‖+‖Complex.I*(b i : ℂ)‖ := norm_add_le _ _
    _ = ‖a i‖+‖b i‖ := by simp
    _ ≤ _ := add_le_add (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)

@[simp] lemma phaseRealVector_complexPhaseVector (a b : PhaseSpace) :
    phaseRealVector (complexPhaseVector a b) = a := by
  ext i
  simp [phaseRealVector,complexPhaseVector]

lemma three_phase_real_deviation (a ν b c d : PhaseSpace) (δ : ℝ)
    (hν : ‖ν‖ = 1) (hδ : 0 ≤ δ) :
    ∀ ℓ : Fin 3, ‖phaseRealVector
      (![complexPhaseVector a b,complexPhaseVector a c,complexPhaseVector (a+δ • ν) d] ℓ)-a‖ ≤ δ := by
  intro ℓ
  fin_cases ℓ <;> simp [norm_smul,Real.norm_of_nonneg hδ,hν,hδ]

lemma phase_length_bound (a b : PhaseSpace) (hb : ‖b‖^2 = 1+‖a‖^2) :
    ‖b‖ ≤ ‖a‖+1 := by
  nlinarith [norm_nonneg a,norm_nonneg b]

lemma shiftedPhaseImag_norm_sq (a ν b : PhaseSpace) (δ : ℝ)
    (hb : ‖b‖^2 = 1+‖a‖^2) :
    ‖shiftedPhaseImag a ν b δ‖^2 = 1+‖a+δ • ν‖^2 := by
  simp only [shiftedPhaseImag,norm_smul,Real.norm_eq_abs,sq_abs,mul_pow,div_pow,hb]
  rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
  have hn : (1 : ℝ)+‖a‖^2 ≠ 0 := by positivity
  field_simp

theorem ThreePhaseData.bounded_spec {H : RealForm PhaseSpace} {a ν : PhaseSpace}
    {δ κ η C A : ℝ} (h : ThreePhaseData H a ν δ κ η C)
    (hν : ‖ν‖ = 1) (halign : a = ‖a‖ • ν) (hA : 0 ≤ A) (ha : ‖a‖ ≤ A)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∃ b c : PhaseSpace, inner ℝ ν b = 0 ∧ inner ℝ ν c = 0 ∧
      ‖b‖^2 = 1+‖a‖^2 ∧ ‖c‖^2 = 1+‖a‖^2 ∧
      ‖b‖ ≤ A+1 ∧ ‖c‖ ≤ A+1 ∧ η ≤ transverseAngleSq b c ∧
      let z := ![complexPhaseVector a b,complexPhaseVector a c,
        complexPhaseVector (a+δ • ν) (shiftedPhaseImag a ν b δ)]
      ∃ Q : Fin 3 → ComplexPhaseMatrix, (∀ ℓ, ‖z ℓ‖ ≤ 2*A+3) ∧
        (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) ∧
        (∀ ℓ, PhaseMatrixValid H (z ℓ) κ C (Q ℓ)) := by
  obtain ⟨b,c,hb,hc,hbn,hcn,hang,⟨Q₀,hQ₀⟩,⟨Q₁,hQ₁⟩,⟨Q₂,hQ₂⟩⟩ := h
  have hbA : ‖b‖ ≤ A+1 := by
    apply (sq_le_sq₀ (norm_nonneg b) (add_nonneg hA zero_le_one)).mp
    rw [hbn]
    nlinarith [(sq_le_sq₀ (norm_nonneg a) hA).mpr ha]
  have hcA : ‖c‖ ≤ A+1 := (phase_length_bound a c hcn).trans (by linarith)
  have had : ‖a+δ • ν‖ ≤ A+1 := by
    calc
      _ ≤ ‖a‖+‖δ • ν‖ := norm_add_le _ _
      _ = ‖a‖+δ := by rw [norm_smul,Real.norm_of_nonneg hδ,hν,mul_one]
      _ ≤ _ := by linarith
  have hd : ‖shiftedPhaseImag a ν b δ‖ ≤ A+2 :=
    (phase_length_bound _ _ (shiftedPhaseImag_norm_sq a ν b δ hbn)).trans (by linarith)
  refine ⟨b,c,hb,hc,hbn,hcn,hbA,hcA,hang,![Q₀,Q₁,Q₂],?_,?_,?_⟩
  · intro ℓ
    fin_cases ℓ
    · simpa using
        (complexPhaseVector_norm_bound a b).trans (by linarith : ‖a‖+‖b‖ ≤ 2*A+3)
    · simpa using
        (complexPhaseVector_norm_bound a c).trans (by linarith : ‖a‖+‖c‖ ≤ 2*A+3)
    · simpa using
        (complexPhaseVector_norm_bound (a+δ • ν) (shiftedPhaseImag a ν b δ)).trans
          (by linarith : ‖a+δ • ν‖+‖shiftedPhaseImag a ν b δ‖ ≤ 2*A+3)
  · have hab : inner ℝ a b = 0 := by rw [halign,inner_smul_left]; simp [hb]
    have hac : inner ℝ a c = 0 := by rw [halign,inner_smul_left]; simp [hc]
    intro ℓ
    fin_cases ℓ
    · exact complexPhaseVector_square a b hab (by simpa only [real_inner_self_eq_norm_sq] using hbn)
    · exact complexPhaseVector_square a c hac (by simpa only [real_inner_self_eq_norm_sq] using hcn)
    · exact shifted_phase_square hb halign hbn δ
  · intro ℓ
    fin_cases ℓ
    · exact hQ₀
    · exact hQ₁
    · exact hQ₂

end YauCounterexamples

end

end OAI
