import OAI.NumberTheory.CubicMoment.Estimates.OrdinaryMixedSieve
import OAI.NumberTheory.CubicGram.FullCubeExtraction

namespace OAI

/-! The ordinary-sieve orientation on actual ramified/cube frequency blocks. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def coprimeResidualSupport (R J : Finset Eisenstein)
    (P : Finset (Eisenstein × Eisenstein)) : Finset Eisenstein :=
  ((R.product J).product P).image (fun t => t.1.1*t.2.1*t.2.2^2*t.1.2^3)

lemma residual_mixedCubic_identity {b p q : Eisenstein}
    (hb : primary b) (hp : primary p) (hq : primary q) (r j : Eisenstein) :
    cubicSymbol b (r*p*q^2*j^3) = cubicSymbol b (r*j^3)*mixedCubic p q b := by
  have he : cubicSymbol b (p*q^2) = mixedCubic p q b := by
    rw [cubicSymbol_mul_upper hb,cubicSymbol_pow_upper hb,cubicSymbol_sq_eq_star hb,
      cubic_reciprocity hb hp,cubic_reciprocity hb hq]
    rfl
  rw [show r*p*q^2*j^3 = (r*j^3)*(p*q^2) by ring,cubicSymbol_mul_upper hb,he]

/-- Huxley's inequality controls the third noncube orientation. The ramified
and cube variables contribute only their explicit finite cardinalities. -/
theorem coprimeResidual_ordinary_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B R J : Finset Eisenstein)
      (P : Finset (Eisenstein × Eisenstein)) (Q Z : ℝ), 1 ≤ Q → 1 ≤ Z →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, primary b ∧ norm b ≤ Z) → ∀ v : Eisenstein → ℂ,
      (∑ h ∈ coprimeResidualSupport R J P, ‖∑ b ∈ B, v b*cubicSymbol b h‖^2) ≤
        (R.card:ℝ)*J.card*C*Q^ε*(Q^2+Z)*∑ b ∈ B, ‖v b‖^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_finite hHuxley hε
  refine ⟨C,hC,?_⟩
  intro B R J P Q Z hQ hZ hP hB v
  have hrow (r j : Eisenstein) :
      (∑ p ∈ P, ‖∑ b ∈ B, v b*cubicSymbol b (r*p.1*p.2^2*j^3)‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ b ∈ B, ‖v b‖^2 := by
    have hh := hbound Q Z hQ hZ P B hP
      (fun b hb => ⟨primary_ne_zero (hB b hb).1,(hB b hb).2⟩)
      (fun b => v b*cubicSymbol b (r*j^3))
    have he : (∑ p ∈ P, ‖∑ b ∈ B, v b*cubicSymbol b (r*p.1*p.2^2*j^3)‖^2) =
        ∑ p ∈ P, ‖∑ b ∈ B, (v b*cubicSymbol b (r*j^3))*mixedCubic p.1 p.2 b‖^2 := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 2
      apply Finset.sum_congr rfl
      intro b hb
      rw [residual_mixedCubic_identity (hB b hb).1 (hP p hp).1.1 (hP p hp).1.2.1]
      ring
    rw [he]
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro b hb
    rw [norm_mul,mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (by
      simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hB b hb).1 _) 2)
  calc
    _ ≤ ∑ t ∈ (R.product J).product P,
        ‖∑ b ∈ B, v b*cubicSymbol b (t.1.1*t.2.1*t.2.2^2*t.1.2^3)‖^2 :=
      Finset.sum_image_le_of_nonneg (s := (R.product J).product P)
        (g := fun t => t.1.1*t.2.1*t.2.2^2*t.1.2^3)
        (f := fun h => ‖∑ b ∈ B, v b*cubicSymbol b h‖^2) (fun _ _ => sq_nonneg _)
    _ = ∑ r ∈ R, ∑ j ∈ J, ∑ p ∈ P,
        ‖∑ b ∈ B, v b*cubicSymbol b (r*p.1*p.2^2*j^3)‖^2 := by
      exact (Finset.sum_product (R.product J) P _).trans (Finset.sum_product R J _)
    _ ≤ ∑ _r ∈ R, ∑ _j ∈ J,
        C*Q^ε*(Q^2+Z)*∑ b ∈ B, ‖v b‖^2 :=
      Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ => hrow r j))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end CubicFirstMoment

end

end OAI
