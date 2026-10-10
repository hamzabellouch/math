import Mathlib
import OAI.Probability.SKGap.Brownian.PathAgreement

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def logPath (q : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) (z : ℝ) : Matrix ι ι ℝ :=
  1+(z^2*q) • diagonal a-z • (diagonal a*M)

lemma pathDiagonal_square_at {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {z : ℝ} (hz : 0 ≤ z) :
    pathDiagonal a z*pathDiagonal a z=z • diagonal a := by
  simp only [pathDiagonal,diagonal_mul_diagonal]
  ext i k
  by_cases hik : i=k
  · subst k
    simp only [diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul]
    rw [mul_mul_mul_comm,mul_self_sqrt hz,mul_self_sqrt (ha i)]
  · simp [hik]

omit [Fintype ι] in
lemma pathShift_eq (z q : ℝ) : pathShift (ι := ι) z q=(z*q) • 1 := by
  ext i k
  by_cases hik : i=k <;> simp [pathShift,hik]

lemma logPath_eq {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {z : ℝ} (hz : 0 ≤ z)
    (q : ℝ) (M : Matrix ι ι ℝ) :
    logPath q a M z=1-pathDiagonal a z*pathDiagonal a z*(M-pathShift z q) := by
  rw [pathDiagonal_square_at ha hz,pathShift_eq]
  simp only [logPath,mul_sub,Matrix.smul_mul,Matrix.mul_smul,mul_one,smul_smul]
  module

lemma hasDerivAt_logPath (q : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) (z : ℝ) (i k : ι) :
    HasDerivAt (fun t => logPath q a M t i k)
      (((2*z*q) • diagonal a-diagonal a*M) i k) z := by
  have hh := (((hasDerivAt_pow 2 z).mul_const q).mul_const (diagonal a i k)).const_add ((1:Matrix ι ι ℝ) i k)
  have h := hh.sub ((hasDerivAt_id z).mul_const ((diagonal a*M) i k))
  convert h using 1 <;> try rfl
  simp only [Nat.cast_ofNat,show 2-1=1 by rfl,pow_one,one_mul,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]

lemma pathK_agrees_at [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) {z : ℝ} (hz : 0 ≤ z)
    (M : Matrix ι ι ℝ) (hM : Mᵀ=M) (hMR : opNorm M ≤ R)
    (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)))
    (hu : -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z))) :
    IsUnit (logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M z) ∧
    pathK f R hR j a z M=(logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M z)⁻¹ := by
  have hsym : (1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z)ᵀ=
      1-pathDiagonal a z*(M-pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a z := by
    simp only [transpose_sub,transpose_one,transpose_mul,hM,
      show (pathDiagonal a z)ᵀ=pathDiagonal a z from diagonal_transpose _,
      show (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))ᵀ=pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b) from diagonal_transpose _,mul_assoc]
  have hS := symmetric_isUnit_of_lower _ hsym hlo hl
  constructor
  · rw [logPath_eq ha hz]
    exact ResolventIdentity.inverse_one_sub_square_mul_unit _ _ hS
  · change realTruncatedK f R hR _ _ M=_
    rw [logPath_eq ha hz]
    exact realTruncatedK_eq_inverse f hlo hf hR _ _ M
      (diagonal_transpose _) (diagonal_transpose _) hM hMR hl hu

def logPathCutoffDerivative (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (j : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) (z : ℝ) : ℝ :=
  (2*z*((j/(Fintype.card ι:ℝ))*∑ b,a b)*(pathK f R hR j a z M*diagonal a).trace-
    (realProject R hR M*pathK f R hR j a z M*diagonal a).trace)/(Fintype.card ι:ℝ)

lemma logPath_trace_derivative (q z : ℝ) (a : ι → ℝ) (M K : Matrix ι ι ℝ) :
    (((2*z*q) • diagonal a-diagonal a*M)*K).trace=
      2*z*q*(K*diagonal a).trace-(M*K*diagonal a).trace := by
  rw [sub_mul,Matrix.smul_mul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul,
    Matrix.trace_mul_comm (diagonal a) K,mul_assoc (diagonal a) M K,
    Matrix.trace_mul_comm (diagonal a) (M*K)]

lemma continuous_logPathCutoffDerivative (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) (a : ι → ℝ) :
    Continuous (fun p : ℝ × Matrix ι ι ℝ => logPathCutoffDerivative f R hR j a p.2 p.1) := by
  have hc : Continuous (fun p : ℝ × Matrix ι ι ℝ => pathK f R hR j a p.1 p.2) := by
    apply continuous_realTruncatedK_comp
    · dsimp [pathDiagonal]; fun_prop
    · dsimp [pathShift]; fun_prop
    · exact continuous_snd
    · intro p; exact diagonal_transpose _
    · intro p; exact diagonal_transpose _
  have hp : Continuous (fun p : ℝ × Matrix ι ι ℝ => realProject R hR p.2) :=
    (realProject_lipschitz hR).continuous.comp continuous_snd
  unfold logPathCutoffDerivative
  exact ((continuous_const.mul continuous_fst |>.mul continuous_const).mul
      ((hc.mul continuous_const).matrix_trace)).sub
      (((hp.mul hc).mul continuous_const).matrix_trace) |>.div_const _
end SKGap
end
end

end OAI
