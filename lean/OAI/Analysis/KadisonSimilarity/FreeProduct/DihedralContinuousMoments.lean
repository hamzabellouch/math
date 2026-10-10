import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralPolynomialMoments
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

namespace OAI

/-! Uniform polynomial approximation transfers the dihedral polynomial
moments to the continuous functional calculus of the real rotation. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A : Type*} [CStarAlgebra A]

/-- Polynomial approximation on the exact interval used for a selfadjoint
contraction, in the source algebra norm. -/
theorem exists_polynomial_near_cfc (a : A) (ha : IsSelfAdjoint a) (han : ‖a‖ ≤ 1)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-1) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ‖cfc f a - Polynomial.aeval a p‖ ≤ ε ∧
      ∀ x ∈ Set.Icc (-1) 1, |p.eval x - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f hf ε hε
  refine ⟨p, ?_, hp⟩
  by_cases hA : Subsingleton A
  · have hz : cfc f a - Polynomial.aeval a p = 0 := hA.elim _ _
    rw [hz, norm_zero]
    exact hε.le
  let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  have hs : spectrum ℝ a ⊆ Set.Icc (-1) 1 := by
    intro x hx
    exact abs_le.mp ((spectrum.norm_le_norm_of_mem hx).trans han)
  rw [← cfc_polynomial p a ha,
    ← cfc_sub f p.eval a (hf.mono hs) p.continuous.continuousOn]
  apply norm_cfc_le hε.le
  intro x hx
  simpa only [Real.norm_eq_abs, abs_sub_comm] using (hp x (hs hx)).le

/-- The zero reflection-coset functional extends from polynomials to every
continuous function of the real part. -/
theorem trace_cfc_realPart_rotation_reflection (τ : A →L[ℂ] ℂ) (w : Aˣ) (d : A)
    (hw : star (w : A) = (↑w⁻¹ : A)) (hwn : ‖(w : A)‖ ≤ 1)
    (hcoset : ∀ l : ℤ, τ ((↑(w ^ l) : A) * d) = 0)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-1) 1)) (l : ℤ) :
    τ ((cfc f (realPart (w : A) : A) * (↑(w ^ l) : A)) * d) = 0 := by
  let a : A := realPart (w : A)
  let b : A := (↑(w ^ l) : A) * d
  have han : ‖a‖ ≤ 1 := (realPart.norm_le (w : A)).trans hwn
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let M : ℝ := ‖τ‖ * ‖b‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨p, hp, _⟩ := exists_polynomial_near_cfc a (realPart (w : A)).property han f hf
    (div_pos hε hM)
  have hz : τ (Polynomial.aeval a p * b) = 0 := by
    simpa only [a, b, ← mul_assoc, ContinuousLinearMap.coe_coe] using
      trace_realPart_polynomial_rotation_reflection τ.toLinearMap w d hw hcoset p l
  have heq : τ ((cfc f a - Polynomial.aeval a p) * b) = τ (cfc f a * b) := by
    rw [sub_mul, map_sub, hz, sub_zero]
  rw [mul_assoc]
  change ‖τ (cfc f a * b)‖ ≤ 0 + ε
  rw [← heq, zero_add]
  calc
    _ ≤ ‖τ‖ * ‖(cfc f a - Polynomial.aeval a p) * b‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * (‖cfc f a - Polynomial.aeval a p‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖τ‖ * ((ε / M) * ‖b‖) := by gcongr
    _ ≤ ε := by
      have hle : ‖τ‖ * ‖b‖ ≤ M := by dsimp [M]; linarith
      calc
        _ = (ε / M) * (‖τ‖ * ‖b‖) := by ring
        _ ≤ (ε / M) * M := mul_le_mul_of_nonneg_left hle (div_pos hε hM).le
        _ = ε := div_mul_cancel₀ _ hM.ne'

end KadisonSimilarity

end

end OAI
