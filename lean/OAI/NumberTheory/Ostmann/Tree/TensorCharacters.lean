import OAI.NumberTheory.Ostmann.Tree.MellinTransform

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]
local instance tensorCharactersFintype : Fintype (MulChar F ℂ) := Fintype.ofFinite _

def tensorCharacter (ρ : I → MulChar F ℂ) (t : I → Fˣ) : ℂ := ∏ i,ρ i (t i)

def tensorCoefficient (f : I → Fˣ → ℂ) (ρ : I → MulChar F ℂ) : ℂ :=
  ∏ i,mellin (f i) (ρ i)

theorem tensorCharacter_kernel (ρ τ : I → MulChar F ℂ) :
    (∑ t : I → Fˣ,tensorCharacter ρ t*conj (tensorCharacter τ t)) =
      if ρ=τ then (Fintype.card (I → Fˣ):ℂ) else 0 := by
  classical
  simp only [tensorCharacter,map_prod,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (u : Fˣ) => ρ i u*conj (τ i u))]
  simp_rw [sum_units_character_kernel]
  by_cases h : ρ=τ
  · subst τ
    simp
  · rw [ite_eq_right h]
    have hi : ∃ i,ρ i≠τ i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i,hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem tensor_mellin_expansion (f : I → Fˣ → ℂ) (t : I → Fˣ) :
    (∏ i,f i (t i)) =
      ∑ ρ : I → MulChar F ℂ,tensorCoefficient f ρ*tensorCharacter ρ t := by
  classical
  calc
    _ = ∏ i,∑ χ : MulChar F ℂ,mellin (f i) χ*χ (t i) := by
      simp_rw [mellin_inversion]
    _ = ∑ ρ : I → MulChar F ℂ,∏ i,mellin (f i) (ρ i)*ρ i (t i) :=
      Fintype.prod_sum _
    _ = _ := by simp only [Finset.prod_mul_distrib,tensorCoefficient,tensorCharacter]

def characterUnitEvaluation (u : Fˣ) : MulChar F ℂ →* ℂ where
  toFun χ := χ u
  map_one' := by simp
  map_mul' χ ψ := MulChar.mul_apply χ ψ u

omit [Fintype F] [DecidableEq F] [DecidableEq I] in
theorem character_product_apply (ρ : I → MulChar F ℂ) (u : Fˣ) :
    (∏ i,ρ i) u = ∏ i,ρ i u := map_prod (characterUnitEvaluation u) _ _

end
end Ostmann.FiniteField

end OAI
