import OAI.Analysis.KadisonKastler.RegularLocalizationReconstruction

namespace OAI

/-! # The dual characters act on the actual regular core

The commutant theorem identifies the core with its fixed-algebra
description. Character normalization therefore gives automorphisms
of the represented algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace.SeparableSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)
  (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)

include hM in
theorem regularCoreDual_mem (a : ℝ)
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularCoreAlgebra U hU M) :
    unitaryConj (regularCharacterUnitary (H := H) a) T ∈ regularCoreAlgebra U hU M := by
  rw [regularCoreAlgebra_eq_fixed_of_published publishedRegularCommutant U hU M hM] at hT ⊢
  exact regularCharacter_normalizes_coreFixed U M (Multiplicative.ofAdd a) hT

def regularCoreDualHom (a : ℝ) :
    Algebra (regularCoreAlgebra U hU M) →⋆ₐ[ℂ] Algebra (regularCoreAlgebra U hU M) :=
  ((Unitary.conjStarAlgAut ℂ _ (regularCharacterUnitary (H := H) a)).toStarAlgHom.comp
    (regularCoreAlgebra U hU M).toStarSubalgebra.subtype).codRestrict
      (regularCoreAlgebra U hU M).toStarSubalgebra
      (fun x => regularCoreDual_mem U hU M hM a x.property)

@[simp] theorem regularCoreDualHom_apply (a : ℝ)
    (x : Algebra (regularCoreAlgebra U hU M)) :
    (regularCoreDualHom U hU M hM a x).val =
      unitaryConj (regularCharacterUnitary (H := H) a) x.val := rfl

theorem regularCoreDualHom_bijective (a : ℝ) :
    Function.Bijective (regularCoreDualHom U hU M hM a) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact (Unitary.conjStarAlgAut ℂ _ (regularCharacterUnitary (H := H) a)).injective
      (congrArg Subtype.val h)
  · intro y
    refine ⟨regularCoreDualHom U hU M hM (-a) y, ?_⟩
    apply Subtype.ext
    simp only [regularCoreDualHom_apply, regularCharacterUnitary_neg]
    simpa only [star_star] using
      unitaryConj_star_unitaryConj (star (regularCharacterUnitary (H := H) a)) y.val

def regularCoreDualEquiv (a : ℝ) :
    Algebra (regularCoreAlgebra U hU M) ≃⋆ₐ[ℂ] Algebra (regularCoreAlgebra U hU M) :=
  StarAlgEquiv.ofBijective (regularCoreDualHom U hU M hM a)
    (regularCoreDualHom_bijective U hU M hM a)

@[simp] theorem regularCoreDualEquiv_apply (a : ℝ)
    (x : Algebra (regularCoreAlgebra U hU M)) :
    (regularCoreDualEquiv U hU M hM a x).val =
      unitaryConj (regularCharacterUnitary (H := H) a) x.val := rfl

end

end KadisonKastler

end OAI
