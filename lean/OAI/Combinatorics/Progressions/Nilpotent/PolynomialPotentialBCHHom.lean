import OAI.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem lie_eq_zero_of_potential (V : MvPolynomial σ ℚ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hV : ∀ x ∈ U, scalarDirectionalDerivative x.base V = x.polynomial)
    (x y : U) : ⁅x,y⁆ = 0 := by
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · rfl
  · change scalarDirectionalDerivative x.val.base y.val.polynomial -
      scalarDirectionalDerivative y.val.base x.val.polynomial = 0
    rw [← hV x.val x.property, ← hV y.val y.property,
      scalarDirectionalDerivative_commute, sub_self]

theorem potential_lowerCentralSeries_eq_bot (V : MvPolynomial σ ℚ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hV : ∀ x ∈ U, scalarDirectionalDerivative x.base V = x.polynomial) :
    LieModule.lowerCentralSeries ℚ U U 1 = ⊥ := by
  rw [LieModule.lowerCentralSeries_succ]
  apply bot_unique
  rw [LieSubmodule.lie_le_iff]
  intro x _ y _
  change ⁅x,y⁆ = 0
  exact lie_eq_zero_of_potential V U hV x y

noncomputable def potentialExponentialHom (V : MvPolynomial σ ℚ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hV : ∀ x ∈ U, scalarDirectionalDerivative x.base V = x.polynomial) :
    NilpotentLieBCHGroup U 1 (potential_lowerCentralSeries_eq_bot V U hV) →*
      PolynomialTranslationGroup σ where
  toFun g := PolynomialTranslationGroup.exponentialElement g.coord.val.base g.coord.val.polynomial
  map_one' := by
    change PolynomialTranslationGroup.exponentialElement 0 0 = 1
    rw [show (0 : MvPolynomial σ ℚ) = scalarDirectionalDerivative (0 : σ → ℚ) V by simp]
    rw [PolynomialTranslationGroup.exponentialElement_potential,
      PolynomialTranslationGroup.potentialElement_zero]
  map_mul' g h := by
    have hb := lieBCH_eq_add_of_lie_eq_zero
      (potential_lowerCentralSeries_eq_bot V U hV) (lie_eq_zero_of_potential V U hV g.coord h.coord)
    change PolynomialTranslationGroup.exponentialElement (lieBCH 1 g.coord h.coord).val.base
      (lieBCH 1 g.coord h.coord).val.polynomial = _
    rw [hb]
    have he (x : U) : PolynomialTranslationGroup.exponentialElement x.val.base x.val.polynomial =
        PolynomialTranslationGroup.potentialElement V x.val.base := by
      rw [← hV x.val x.property, PolynomialTranslationGroup.exponentialElement_potential]
    rw [he, he, he]
    exact PolynomialTranslationGroup.potentialElement_add V _ _

@[simp] theorem potentialExponentialHom_mem (V : MvPolynomial σ ℚ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hV : ∀ x ∈ U, scalarDirectionalDerivative x.base V = x.polynomial)
    (g : NilpotentLieBCHGroup U 1 (potential_lowerCentralSeries_eq_bot V U hV)) :
    potentialExponentialHom V U hV g ∈ PolynomialTranslationGroup.potentialSubgroup V := by
  change PolynomialTranslationGroup.exponentialElement g.coord.val.base g.coord.val.polynomial ∈ _
  rw [← hV g.coord.val g.coord.property, PolynomialTranslationGroup.exponentialElement_potential]
  exact (PolynomialTranslationGroup.mem_potentialSubgroup V _).mpr rfl

theorem potentialExponentialHom_injective (V : MvPolynomial σ ℚ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hV : ∀ x ∈ U, scalarDirectionalDerivative x.base V = x.polynomial) :
    Function.Injective (potentialExponentialHom V U hV) := by
  intro x y h
  have hb : x.coord.val.base = y.coord.val.base :=
    congrArg PolynomialTranslationGroup.base h
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  apply PolynomialTranslationLie.ext hb
  rw [← hV x.coord.val x.coord.property, ← hV y.coord.val y.coord.property, hb]

end Erdos3.PolynomialTranslationLie

end

end OAI
