import OAI.NumberTheory.CubicMoment.Estimates.PrimaryHeckeCharacter
import OAI.NumberTheory.CubicMoment.Estimates.IdealMixedMoments

namespace OAI

/-! Sieve moments of the actual primary-normalized ideal character.
The primary representative and the ramified zero are retained explicitly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryMixedIdealChar_eq (a b : Eisenstein) (ν : EisensteinIdealExponent) :
    primaryMixedIdealChar a b ν =
      if primary (idealPrimaryGenerator ν) then
        mixedCubic a b (idealPrimaryGenerator ν) else 0 := by
  unfold primaryMixedIdealChar primaryMixedLift idealPrimaryGenerator
  by_cases h : IsUnit (Ideal.Quotient.mk (modulus 3) (idealExponentGenerator ν))
  · rw [ite_eq_left h,ite_eq_left (primaryNormalize_primary h)]
  · rw [ite_eq_right h,ite_eq_right]
    intro hp
    exact h (unit_residue_of_dvd_primary hp (primaryNormalize_associated _).dvd)

/-- The normalized ideal character is sieved with the exact primary
representative. A fixed mixed factor and any fixed bounded coefficient
twist are allowed, including the ramified local factors. -/
theorem normalized_primary_ideal_cubic_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (S : Finset EisensteinIdealExponent)
      (b : Eisenstein) (ξ : EisensteinIdealExponent → ℂ) (N Y J u : ℝ),
      primary b → (∀ ν ∈ S, ‖ξ ν‖ ≤ 1) → 1 ≤ N → 1 ≤ Y → 0 < J →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ Y) →
      (∑ a ∈ P, ‖normalizedDualPolynomial S
        (fun ν => ξ ν*primaryMixedIdealChar a b ν) idealExponentNorm J u‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := bounded_cubic_moment hε
  refine ⟨C,hC,?_⟩
  intro P S b ξ N Y J u hb hξ hN hY hJ hP hS
  let T := S.image idealPrimaryGenerator
  let v : Eisenstein → ℂ := fun n => if primary n then
    ξ (idealExponentOf n)*(((J/norm n)^(1/2:ℝ):ℝ)*mellinPhase u (norm n))*
      star (cubicSymbol b n) else 0
  have hT : ∀ n ∈ T, n ≠ 0 ∧ norm n ≤ Y := by
    intro n hn
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨(primaryNormalize_associated _).ne_zero_iff.mp (idealExponentGenerator_ne_zero ν),
      (idealPrimaryGenerator_norm ν).trans_le (hS ν hν).2⟩
  have hv : ∀ n ∈ T, ‖v n‖ ≤ 1 := by
    intro n hn
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hn
    dsimp only [v]
    split
    · rw [idealExponentOf_primaryGenerator,idealPrimaryGenerator_norm,norm_mul,norm_mul,
        norm_mul,norm_star,mellinPhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (div_nonneg hJ.le (idealExponentNorm_pos ν).le) _)]
      have hw := dual_dyad_weight_le_one hJ (hS ν hν).1
      have hc := norm_cubicSymbol_le_one hb (idealPrimaryGenerator ν)
      have hx := hξ ν hν
      have hxw : ‖ξ ν‖*(J/idealExponentNorm ν)^(1/2:ℝ) ≤ 1 := by
        simpa using mul_le_mul hx hw (Real.rpow_nonneg (div_nonneg hJ.le (idealExponentNorm_pos ν).le) _) zero_le_one
      exact (mul_le_mul hxw hc (_root_.norm_nonneg _) zero_le_one).trans_eq (by norm_num)
    · simp
  have heq (a : Eisenstein) :
      normalizedDualPolynomial S (fun ν => ξ ν*primaryMixedIdealChar a b ν)
        idealExponentNorm J u = ∑ n ∈ T, v n*cubicSymbol a n := by
    rw [Finset.sum_image (fun ν _ κ _ h => idealPrimaryGenerator_injective h)]
    unfold normalizedDualPolynomial
    apply Finset.sum_congr rfl
    intro ν hν
    dsimp only [v]
    rw [idealExponentOf_primaryGenerator,idealPrimaryGenerator_norm,primaryMixedIdealChar_eq]
    split_ifs
    · unfold mixedCubic
      ring
    · simp
  simp_rw [heq]
  simpa only [one_pow,mul_one] using hbound P T N Y 1 hN hY zero_le_one hP hT v hv

end CubicFirstMoment

end

end OAI
