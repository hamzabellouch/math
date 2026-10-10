import OAI.NumberTheory.CubicMoment.Estimates.CoprimeSquarefreeMass
import OAI.NumberTheory.CubicMoment.Estimates.DispersionAbsoluteModel

namespace OAI

/-! The literal Type-I product model becomes the factored squarefree
model after a proved rough-prime coprimality error. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def mixedMassModel (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  (cStar:ℂ)*∑ b ∈ S, β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)*
    coprimeSquarefreeModelMass b W A

lemma mixedMassModel_sub_factor (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    mixedMassModel S β u W A-(cStar:ℂ)*dispersionModel S β u*squarefreeModelMass W A =
      (cStar:ℂ)*∑ b ∈ S, β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)*
        (coprimeSquarefreeModelMass b W A-squarefreeModelMass W A) := by
  unfold mixedMassModel dispersionModel
  rw [mul_assoc,Finset.sum_mul,←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem UniformLogWeights.mixedMassModel_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (u A D : ℝ) (n : ℕ), 0 < A → 0 < D →
      (∀ b ∈ S, primary b ∧ Squarefree b) →
      (∀ b ∈ S, (primaryPrimeFactors b).card ≤ n) →
      (∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b, D ≤ norm p) →
      ‖mixedMassModel S β u (W i) A-
        (cStar:ℂ)*dispersionModel S β u*squarefreeModelMass (W i) A‖ ≤
        K*n*A^(2/3:ℝ)/D*dispersionAbsoluteModel S β := by
  obtain ⟨K,hK,hbound⟩ := h.coprimeSquarefreeModelMass_error
  refine ⟨cStar*K,mul_nonneg cStar_pos.le hK,?_⟩
  intro i S β u A D n hA hD hS hn hrough
  rw [mixedMassModel_sub_factor,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos]
  have hterm (b : Eisenstein) (hb : b ∈ S) :
      ‖β b*normTwist u b*((norm b^(-1/6:ℝ):ℝ):ℂ)*
        (coprimeSquarefreeModelMass b (W i) A-squarefreeModelMass (W i) A)‖ ≤
      (‖β b‖*norm b^(-1/6:ℝ))*(K*n*A^(2/3:ℝ)/D) := by
    rw [norm_mul,norm_mul,norm_mul,norm_normTwist,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg b) _)]
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (_root_.norm_nonneg _) (Real.rpow_nonneg (norm_nonneg b) _))
    apply (hbound i b A D (hS b hb).1 (hS b hb).2 hA hD (hrough b hb)).trans
    have hn' : ((primaryPrimeFactors b).card:ℝ) ≤ n := Nat.cast_le.mpr (hn b hb)
    calc
      _ ≤ K*A^(2/3:ℝ)*n/D := by gcongr
      _ = _ := by ring
  calc
    _ ≤ cStar*(∑ b ∈ S, (‖β b‖*norm b^(-1/6:ℝ))*(K*n*A^(2/3:ℝ)/D)) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) cStar_pos.le
    _ = _ := by rw [←Finset.sum_mul]; unfold dispersionAbsoluteModel; ring

end CubicFirstMoment

end

end OAI
