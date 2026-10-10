import OAI.Analysis.KadisonKastler.RegularCoreCommutant
import OAI.Analysis.KadisonKastler.RegularCoreCentralField
import OAI.Analysis.KadisonKastler.SpectralCommutant
import OAI.Analysis.KadisonKastler.DiagonalDecomposition
import OAI.Analysis.KadisonKastler.PreparedPairCorrection

namespace OAI

/-! # Concrete Fourier reductions for the regular commutant theorem

Translation commutation gives an actual bounded measurable Fourier field.
Adjoining the character multipliers to the regular core generates the
whole constant-commutant tensor algebra. These conclusions use the proved
spectral and diagonal decomposition theorems, not a crossed-product
commutant assumption.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Fourier transformation sends translation commutation to character commutation. -/
theorem fourier_commute_characters_of_translations
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ s : Multiplicative ℝ, Commute T
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) (a : ℝ) :
    Commute ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T)
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  let s : ℝ := a / (2 * Real.pi)
  have hs : 2 * Real.pi * s = a := by dsimp [s]; field_simp
  have he := congrArg (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
    (hT (Multiplicative.ofAdd s)).eq
  change _ * _ = _ * _
  simpa only [map_mul, fourierConj_regularTranslation, hs] using he

/-- Every translation-commuting operator has a bounded measurable Fourier field. -/
theorem exists_fourierField_of_commute_translations
    [TopologicalSpace.SeparableSpace H]
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ s : Multiplicative ℝ, Commute T
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) :
    ∃ F : ℝ → H →L[ℂ] H,
      (∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume) ∧
      (∀ᵐ t ∂volume, ‖F t‖ ≤ ‖T‖) ∧
      RepresentsOperatorField volume F ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T) := by
  obtain ⟨F, hm, hn, hF⟩ := publishedRealDiagonalDecomposition H
    ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T)
    (publishedRealSpectralCommutant H _ (fourier_commute_characters_of_translations T hT))
  refine ⟨F, hm, ?_, hF⟩
  have he : ‖(Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T‖ = ‖T‖ :=
    StarAlgEquiv.norm_map (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T
  rwa [he] at hn

/-- A translation-commuting operator in the tensor algebra has Fourier fibers in
that same algebra. -/
theorem exists_fourierField_mem_of_commute_translations
    [TopologicalSpace.SeparableSpace H]
    (P : VonNeumannAlgebra H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ s : Multiplicative ℝ, Commute T
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hP : T ∈ regularTensorAlgebra P) :
    ∃ F : ℝ → H →L[ℂ] H,
      (∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume) ∧
      (∀ᵐ t ∂volume, ‖F t‖ ≤ ‖T‖) ∧ (∀ᵐ t ∂volume, F t ∈ P) ∧
      RepresentsOperatorField volume F ((Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv T) := by
  obtain ⟨F, hm, hn, hF⟩ := exists_fourierField_of_commute_translations T hT
  refine ⟨F, hm, hn, hF.mem_algebra_ae P ?_, hF⟩
  apply (mem_regularTensorAlgebra_iff P _).mpr
  intro b hb
  have he := congrArg (Lp.fourierTransformₗᵢ ℝ H).conjStarAlgEquiv
    ((mem_regularTensorAlgebra_iff P T).mp hP b hb)
  simpa only [map_mul, fourierConj_regularConstantHom] using he

/-- Commutation with both the translations and the character multipliers forces
an operator to be constant on the real variable. -/
theorem exists_constant_of_commute_translations_characters
    [TopologicalSpace.SeparableSpace H]
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (htrans : ∀ s : Multiplicative ℝ, Commute T
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hchar : ∀ a : ℝ, Commute T
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) :
    ∃ A : H →L[ℂ] H, T = regularConstantHom volume A := by
  obtain ⟨F, hm, _, hF⟩ := publishedRealDiagonalDecomposition H T
    (publishedRealSpectralCommutant H T hchar)
  obtain ⟨A, _, hA⟩ := constant_of_regularField_translation_fixed hF hm
    (fun s => (commute_unitary_iff_star_right_conjugate
      (regularRightTranslation (H := H) s).property).mp (htrans s).symm)
  exact ⟨A, hA⟩

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
  (P : VonNeumannAlgebra H)

/-- Adjoin the full scalar diagonal to the actual regular core. -/
def regularCoreDiagonalAlgebra : VonNeumannAlgebra (RegularCoreHilbert H) :=
  generatedVonNeumannAlgebra (StarAlgebra.adjoin ℂ
    ((regularCoreAlgebra U hU P : Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) ∪
      Set.range (fun a : ℝ => (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))))

theorem regularCore_le_diagonalAlgebra :
    regularCoreAlgebra U hU P ≤ regularCoreDiagonalAlgebra U hU P := by
  intro T hT
  exact subset_generatedVonNeumannAlgebra _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inl hT))

theorem regularCharacter_mem_diagonalAlgebra (a : ℝ) :
    (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) ∈
      regularCoreDiagonalAlgebra U hU P :=
  subset_generatedVonNeumannAlgebra _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨a, rfl⟩))

/-- The commutant of the core together with the scalar diagonal consists only of
constant operators from the original commutant. -/
theorem exists_constant_of_mem_regularCoreDiagonal_commutant
    [TopologicalSpace.SeparableSpace H]
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ (regularCoreDiagonalAlgebra U hU P).commutant) :
    ∃ A ∈ P.commutant, T = regularConstantHom volume A := by
  have htrans (s : Multiplicative ℝ) : Commute T
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _
      (regularCore_le_diagonalAlgebra U hU P (regularTranslation_mem_core U hU P s))).symm
  have hchar (a : ℝ) : Commute T
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _
      (regularCharacter_mem_diagonalAlgebra U hU P a)).symm
  obtain ⟨A, rfl⟩ := exists_constant_of_commute_translations_characters T htrans hchar
  refine ⟨A, ?_, rfl⟩
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro x hx
  have hc : Commute (regularConstantHom volume A) (regularCoreEmbedding U hU x) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _
      (regularCore_le_diagonalAlgebra U hU P (regularCoreEmbedding_mem_core U hU P hx))).symm
  exact (constant_commutes_regularEmbedding U hU A x hc).eq.symm

/-- The scalar diagonal and the core generate the entire regular tensor algebra.
This is the concrete dual-generation step, proved without the regular commutant input. -/
theorem regularCoreDiagonalAlgebra_eq_tensor [TopologicalSpace.SeparableSpace H]
    (hP : ∀ s x, x ∈ P → unitaryConj (U s) x ∈ P) :
    regularCoreDiagonalAlgebra U hU P = regularTensorAlgebra P := by
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    apply StarAlgebra.adjoin_le
    rintro T (hT | ⟨a, rfl⟩)
    · exact regularCoreAlgebra_le_tensor U hU P hP hT
    · apply (mem_regularTensorAlgebra_iff P _).mpr
      intro b _
      exact (regularCharacter_commute_constant a b).symm.eq
  · intro T hT
    have hdouble : T ∈ (regularCoreDiagonalAlgebra U hU P).commutant.commutant := by
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro S hS
      obtain ⟨A, hA, rfl⟩ := exists_constant_of_mem_regularCoreDiagonal_commutant U hU P S hS
      exact (mem_regularTensorAlgebra_iff P T).mp hT A hA
    simpa only [VonNeumannAlgebra.commutant_commutant] using hdouble

end

end KadisonKastler

end OAI
