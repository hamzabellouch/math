import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ContinuousRealQuadraticCoerciveNear

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise
abbrev PhaseSpace := EuclideanSpace ℝ (Fin 3)
abbrev ComplexPhaseMatrix := Matrix (Fin 3) (Fin 3) ℂ

def shiftedPhaseImag (a ν b : PhaseSpace) (δ : ℝ) : PhaseSpace :=
  (Real.sqrt (1 + ‖a + δ • ν‖^2) / Real.sqrt (1 + ‖a‖^2)) • b

def transverseAngleSq (b c : PhaseSpace) : ℝ :=
  (‖b‖^2 * ‖c‖^2 - (inner ℝ b c)^2) / (‖b‖^2 * ‖c‖^2)

def PhaseMatrixValid (H : RealForm PhaseSpace) (z : Fin 3 → ℂ)
    (κ C : ℝ) (Q : ComplexPhaseMatrix) : Prop :=
  Qᵀ = Q ∧ Q *ᵥ z = 0 ∧ ‖Q‖ ≤ C ∧
    ∀ v, 4 * κ * squareSum v ≤ realQuadratic (phaseFormMatrix H - Q.map Complex.re) v

def ThreePhaseData (H : RealForm PhaseSpace) (a ν : PhaseSpace)
    (δ κ η C : ℝ) : Prop :=
  ∃ b c : PhaseSpace, inner ℝ ν b = 0 ∧ inner ℝ ν c = 0 ∧
    ‖b‖^2 = 1 + ‖a‖^2 ∧ ‖c‖^2 = 1 + ‖a‖^2 ∧
    η ≤ transverseAngleSq b c ∧
    (∃ Q, PhaseMatrixValid H (complexPhaseVector a b) κ C Q) ∧
    (∃ Q, PhaseMatrixValid H (complexPhaseVector a c) κ C Q) ∧
    (∃ Q, PhaseMatrixValid H
      (complexPhaseVector (a + δ • ν) (shiftedPhaseImag a ν b δ)) κ C Q)

lemma PhaseMatrixValid.mono {H : RealForm PhaseSpace} {z : Fin 3 → ℂ}
    {κ κ' C C' : ℝ} {Q : ComplexPhaseMatrix} (h : PhaseMatrixValid H z κ C Q)
    (hk : κ' ≤ κ) (hC : C ≤ C') : PhaseMatrixValid H z κ' C' Q := by
  refine ⟨h.1, h.2.1, h.2.2.1.trans hC, fun v => ?_⟩
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num))
    (squareSum_nonneg v)).trans (h.2.2.2 v)

lemma ThreePhaseData.mono {H : RealForm PhaseSpace} {a ν : PhaseSpace}
    {δ κ κ' η η' C C' : ℝ} (h : ThreePhaseData H a ν δ κ η C)
    (hk : κ' ≤ κ) (hη : η' ≤ η) (hC : C ≤ C') :
    ThreePhaseData H a ν δ κ' η' C' := by
  obtain ⟨b, c, hb, hc, hbn, hcn, ha, ⟨Q₀, h₀⟩, ⟨Q₁, h₁⟩, ⟨Q₂, h₂⟩⟩ := h
  exact ⟨b, c, hb, hc, hbn, hcn, hη.trans ha,
    ⟨Q₀, h₀.mono hk hC⟩, ⟨Q₁, h₁.mono hk hC⟩, ⟨Q₂, h₂.mono hk hC⟩⟩

lemma squareSum_pos {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : v ≠ 0) :
    0 < squareSum v := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv (funext hn)
  have hi' : 0 < v i * v i := mul_self_pos.mpr hi
  exact hi'.trans_le (Finset.single_le_sum (fun j _ => mul_self_nonneg (v j))
    (Finset.mem_univ i))

lemma complexPhaseVector_continuousAt {T : Type*} [TopologicalSpace T]
    (a b : T → PhaseSpace) (t : T) (ha : ContinuousAt a t) (hb : ContinuousAt b t) :
    ContinuousAt (fun s => complexPhaseVector (a s) (b s)) t := by
  apply continuousAt_pi.mpr
  intro i
  apply ContinuousAt.add
  · exact Complex.continuous_ofReal.continuousAt.comp
      ((EuclideanSpace.proj i).continuous.continuousAt.comp ha)
  · exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
      ((EuclideanSpace.proj i).continuous.continuousAt.comp hb))

lemma aligned_phase_square {a ν b : PhaseSpace} (hνb : inner ℝ ν b = 0)
    (ha : a = ‖a‖ • ν) (hb : ‖b‖^2 = 1 + ‖a‖^2) :
    complexPhaseVector a b ⬝ᵥ complexPhaseVector a b = -1 := by
  apply complexPhaseVector_square
  · rw [ha, inner_smul_left, conj_trivial, hνb, mul_zero]
  · simpa only [real_inner_self_eq_norm_sq] using hb

lemma shiftedPhaseImag_zero (a ν b : PhaseSpace) : shiftedPhaseImag a ν b 0 = b := by
  have hp : 0 < Real.sqrt (1 + ‖a‖^2) := Real.sqrt_pos.mpr (by positivity)
  simp [shiftedPhaseImag, hp.ne']

lemma shiftedPhaseImag_eq_normalized (a ν b : PhaseSpace) (δ : ℝ) :
    shiftedPhaseImag a ν (normalizedTransverse a ν b) δ =
      normalizedTransverse (a + δ • ν) ν b := by
  have hp : Real.sqrt (1 + ‖a‖^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  dsimp [shiftedPhaseImag, normalizedTransverse]
  rw [smul_smul]
  congr 1
  field_simp

lemma shifted_phase_square {a ν b : PhaseSpace} (hνb : inner ℝ ν b = 0)
    (ha : a = ‖a‖ • ν) (hb : ‖b‖^2 = 1 + ‖a‖^2) (δ : ℝ) :
    complexPhaseVector (a + δ • ν) (shiftedPhaseImag a ν b δ) ⬝ᵥ
      complexPhaseVector (a + δ • ν) (shiftedPhaseImag a ν b δ) = -1 := by
  apply complexPhaseVector_square
  · simp only [shiftedPhaseImag, inner_smul_right, inner_add_left,
      inner_smul_left, conj_trivial, hνb, mul_zero, add_zero]
    rw [ha, inner_smul_left, conj_trivial, hνb, mul_zero, mul_zero]
  · simp only [real_inner_self_eq_norm_sq, shiftedPhaseImag, norm_smul,
      Real.norm_eq_abs, sq_abs, mul_pow, div_pow, hb]
    rw [Real.sq_sqrt (show 0 ≤ 1 + ‖a + δ • ν‖^2 by positivity),
      Real.sq_sqrt (show 0 ≤ 1 + ‖a‖^2 by positivity)]
    have hn : (1 : ℝ) + ‖a‖^2 ≠ 0 := by positivity
    field_simp


end

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
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι]

lemma real_phase_linear (a b v : EuclideanSpace ℝ ι) :
    (∑ i, (v i : ℂ) * complexPhaseVector a b i).re = inner ℝ v a := by
  simp only [complexPhaseVector, Complex.re_sum, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, add_zero, sub_zero, mul_comm, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Pi.star_apply, star_trivial]

lemma real_phase_quadratic (Q : Matrix ι ι ℂ) (hQ : Qᵀ = Q)
    (v : EuclideanSpace ℝ ι) :
    (∑ i, ∑ j, (v i : ℂ) * (v j : ℂ) * Q j i).re =
      realQuadratic (Q.map Complex.re) (fun i => v i) := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, mul_zero, zero_mul, add_zero, sub_zero, realQuadratic, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : Q j i = Q i j := congrFun (congrFun hQ i) j
  rw [hs]
  ring

lemma phase_squareSum (v : EuclideanSpace ℝ ι) :
    squareSum (fun i => v i) = ‖v‖^2 := by
  simpa only [squareSum, sq] using (EuclideanSpace.real_norm_sq_eq v).symm

lemma phase_linear_perturbation (a b ν v : EuclideanSpace ℝ ι)
    {δ : ℝ} (hδ : 0 ≤ δ) (hν : ‖ν‖ = 1) :
    (∑ i, (v i : ℂ) * complexPhaseVector (a + δ • ν) b i).re - inner ℝ v a ≤
      δ * ‖v‖ := by
  rw [real_phase_linear, inner_add_right, real_inner_smul_right]
  have hh : inner ℝ v ν ≤ ‖v‖ := by
    simpa only [hν, mul_one] using real_inner_le_norm v ν
  nlinarith [mul_le_mul_of_nonneg_left hh hδ]

lemma phase_matrix_gaussian_gap (H : RealForm PhaseSpace) (z : Fin 3 → ℂ)
    {κ C : ℝ} (Q : ComplexPhaseMatrix) (hQ : PhaseMatrixValid H z κ C Q)
    (v : PhaseSpace) :
    (∑ i, ∑ j, (v i : ℂ) * (v j : ℂ) * Q j i).re - H v v ≤ -4*κ*‖v‖^2 := by
  rw [real_phase_quadratic Q hQ.1]
  have hg := hQ.2.2.2 (fun i => v i)
  erw [phase_squareSum, realQuadratic_sub, realQuadratic_phaseFormMatrix] at hg
  change 4 * κ * ‖v‖ ^ 2 ≤ H v v - realQuadratic (Q.map Complex.re) (fun i => v i) at hg
  linarith

lemma phase_vector_ne_zero (z : ι → ℂ) (hz : ∑ i, z i*z i = -1) : z ≠ 0 := by
  intro he
  simp [he] at hz

lemma phase_matrix_annihilation (Q : Matrix ι ι ℂ) (z : ι → ℂ)
    (h : Q *ᵥ z = 0) (k : ι) : ∑ i, z i * Q k i = 0 := by
  simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using congrFun h k



end YauCounterexamples
end

end OAI
