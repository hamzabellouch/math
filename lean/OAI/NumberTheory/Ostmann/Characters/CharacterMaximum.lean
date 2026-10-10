import OAI.NumberTheory.Ostmann.Characters.QuadraticClassification

namespace OAI

noncomputable section
namespace Ostmann.Characters
variable {p : ℕ} [Fact p.Prime]

def higherBias (S : Finset (ZMod p)) : NNReal :=
  Finset.univ.sup (fun z : MulChar (ZMod p) ℂ × ZMod p =>
    if 2<orderOf z.1 then ‖translatedMean S z.1 z.2‖₊ else 0)

theorem translatedBias_le_higherBias (S : Finset (ZMod p))
    (χ : MulChar (ZMod p) ℂ) (hχ : 2<orderOf χ) (a : ZMod p) :
    translatedBias S χ a ≤ (higherBias S:ℝ) := by
  have h := Finset.le_sup (s:=Finset.univ)
    (f:=fun z:MulChar (ZMod p) ℂ × ZMod p =>
      if 2<orderOf z.1 then ‖translatedMean S z.1 z.2‖₊ else (0:NNReal))
    (Finset.mem_univ (χ,a))
  have hh : ‖translatedMean S χ a‖₊ ≤ higherBias S := by
    simpa only [higherBias, hχ, ite_true] using h
  exact_mod_cast hh

theorem nonprincipalBias_le_quadratic_add_higher (S : Finset (ZMod p)) (hp : p≠2) :
    nonprincipalBias S ≤ maxTranslatedBias S (quadraticCharacter p)+higherBias S := by
  classical
  unfold nonprincipalBias
  apply Finset.sup_le
  intro z hz
  by_cases he : z.1=1
  · simp only [he, ite_true]
    positivity
  · simp only [he, ite_false]
    by_cases hh : 2<orderOf z.1
    · have hv : ‖translatedMean S z.1 z.2‖₊ ≤ higherBias S := by
        exact_mod_cast translatedBias_le_higherBias S z.1 hh z.2
      exact hv.trans (le_add_of_nonneg_left (by positivity))
    · have hpos := z.1.orderOf_pos
      have hone : orderOf z.1≠1 := fun h => he (orderOf_eq_one_iff.mp h)
      have hord : orderOf z.1=2 := by omega
      have hsq : z.1^2=1 := by rw [← hord]; exact pow_orderOf_eq_one _
      have hquad := eq_quadraticCharacter p hp z.1 he hsq
      rw [hquad]
      have hv : ‖translatedMean S (quadraticCharacter p) z.2‖₊ ≤
          maxTranslatedBias S (quadraticCharacter p) :=
        Finset.le_sup (f:=fun a=>‖translatedMean S (quadraticCharacter p) a‖₊)
          (Finset.mem_univ z.2)
      exact hv.trans (le_add_of_nonneg_right (by positivity))

theorem correlationBound_le_quadratic_add_higher (S : Finset (ZMod p)) (hp : p≠2)
    (hlo : 1/4≤Supply.density S) (hhi : Supply.density S≤3/4) :
    (FiniteField.correlationBound (Supply.additiveTransform S):ℝ) ≤
      4*((maxTranslatedBias S (quadraticCharacter p):ℝ)+(higherBias S:ℝ))+
        4/Real.sqrt p := by
  apply (correlationBound_le S hlo hhi).trans
  have h : (nonprincipalBias S:ℝ) ≤
      (maxTranslatedBias S (quadraticCharacter p):ℝ)+(higherBias S:ℝ) := by
    exact_mod_cast nonprincipalBias_le_quadratic_add_higher S hp
  linarith
end Ostmann.Characters

end

end OAI
