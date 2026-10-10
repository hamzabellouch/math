import OAI.Analysis.ModularTheory.DualUnitary

namespace OAI

/-! The concrete dual character unitaries preserve the generated von Neumann
algebra. This supplies its actual dual action; it does not assert the existence
or properties of a dual weight. -/

noncomputable section
open MeasureTheory
open scoped Pointwise

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ) [Measure.IsAddRightInvariant μ]
  (S : BoundedRecovery.StandardModularData H)

def modularDualConjugation (r : ℝ) :
    (Lp H 2 μ →L[ℂ] Lp H 2 μ) ≃⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  (modularDualUnitary μ r).conjStarAlgEquiv

omit [Measure.IsAddRightInvariant μ] in
lemma modularDualConjugation_coeff (r : ℝ) (T : H →L[ℂ] H) :
    modularDualConjugation (H := H) μ r (modularLpRepresentation μ S.D T) =
      modularLpRepresentation μ S.D T := by
  apply ContinuousLinearMap.ext
  intro f
  change modularDual μ r
    (modularLpRepresentation μ S.D T (modularDual μ (-r) f)) = _
  rw [modularDual_coefficient, modularDual_comp, add_neg_cancel, modularDual_zero]

lemma modularDualConjugation_translate (r t : ℝ) :
    modularDualConjugation (H := H) μ r
        (modularLpTranslateEquiv (H := H) μ t : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      BoundedRecovery.spectralCharacter r t •
        (modularLpTranslateEquiv (H := H) μ t : Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  change modularDual μ r (modularLpTranslate μ t (modularDual μ (-r) f)) =
    BoundedRecovery.spectralCharacter r t • modularLpTranslate μ t f
  exact modularDual_translation μ r t f

private lemma modularDualConjugation_coeff_mem (r : ℝ) (a : S.M.toStarSubalgebra) :
    modularDualConjugation μ r
      (modularLpRepresentation μ S.D (a : H →L[ℂ] H)) ∈ modularCrossedProduct μ S := by
  rw [modularDualConjugation_coeff]
  exact modularCrossedProduct_coeff μ S a

private lemma modularDualConjugation_translate_mem (r t : ℝ) :
    modularDualConjugation μ r
      (modularLpTranslateEquiv (H := H) μ t : Lp H 2 μ →L[ℂ] Lp H 2 μ) ∈
        modularCrossedProduct μ S := by
  rw [modularDualConjugation_translate]
  exact (modularCrossedProduct μ S).toStarSubalgebra.smul_mem
    (modularCrossedProduct_translate μ S t) _

private lemma modularDualConjugation_generators (r : ℝ) :
    ∀ T ∈ modularCoreGenerators μ S,
      modularDualConjugation μ r T ∈ modularCrossedProduct μ S := by
  rintro T (⟨a, rfl⟩ | ⟨t, rfl⟩)
  · exact modularDualConjugation_coeff_mem μ S r a
  · exact modularDualConjugation_translate_mem μ S r t

private def modularDualPreimage (r : ℝ) :
    StarSubalgebra ℂ (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  (modularCrossedProduct μ S).toStarSubalgebra.comap
    (modularDualConjugation (H := H) μ r).toStarAlgHom

private lemma modularDualConjugation_algebraic (r : ℝ) :
    ∀ T ∈ algebraicModularCore μ S,
      modularDualConjugation μ r T ∈ modularCrossedProduct μ S := by
  have hgen : modularCoreGenerators μ S ⊆ modularDualPreimage μ S r :=
    modularDualConjugation_generators μ S r
  have hle : algebraicModularCore μ S ≤ modularDualPreimage μ S r :=
    StarAlgebra.adjoin_le hgen
  exact hle

lemma modularDualConjugation_mem (r : ℝ) {T : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hT : T ∈ modularCrossedProduct μ S) :
    modularDualConjugation μ r T ∈ modularCrossedProduct μ S := by
  let α := modularDualConjugation (H := H) μ r
  rw [← (modularCrossedProduct μ S).commutant_commutant,
    VonNeumannAlgebra.mem_commutant_iff]
  intro b hb
  have hb₀ : α.symm b ∈ Set.centralizer
      (algebraicModularCore μ S : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := by
    intro a ha
    apply α.injective
    rw [map_mul, map_mul]
    change α a * α (α.symm b) = α (α.symm b) * α a
    rw [α.apply_symm_apply]
    exact VonNeumannAlgebra.mem_commutant_iff.mp hb _
      (modularDualConjugation_algebraic μ S r a ha)
  have hb' : α.symm b ∈ (modularCrossedProduct μ S).commutant := by
    rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_commutant,
      modularCrossedProduct_carrier, Set.centralizer_centralizer_centralizer]
    exact hb₀
  have he := VonNeumannAlgebra.mem_commutant_iff.mp hb' T hT
  have hα := congrArg α he
  simpa only [map_mul, α.apply_symm_apply] using hα.symm

end WeakPureInfiniteness

end

end OAI
