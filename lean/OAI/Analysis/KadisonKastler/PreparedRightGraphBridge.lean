import OAI.Analysis.KadisonKastler.PreparedGraphComparison
import OAI.Analysis.KadisonKastler.PreparedPairState
import OAI.Analysis.KadisonKastler.PublishedLocalizedEmbedding

namespace OAI

/-! # Prepared graph comparison from common right actions

The vector and conjugation identities are imposed only on the
shared increasing matrix algebra. In particular, no tracial state on either
ambient algebra is needed. The relative right-action data imply the required
centralizer identities, and matrix averaging transfers relative irreducibility
to the nearby algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedRightGraphOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightGraphStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance preparedRightGraphOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightGraphOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Right multiplication on the common algebra implies centralization of
the vector functional, without any trace hypothesis on the ambient algebra. -/
theorem vector_functional_centralizes_of_commonRight
    (R N : VonNeumannAlgebra H) (hRN : R ≤ N)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H)
    (hright : ∀ r ∈ R, conjugationOperator J r ∈ N.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    (r : Algebra R) (x : Algebra N) :
    inner ℂ Ω ((r.val * x.val) Ω) = inner ℂ Ω ((x.val * r.val) Ω) := by
  apply vector_functional_centralizes_of_conjugate_right R N hRN J hJ Ω
  · intro a
    exact hright a.val a.property
  · intro a
    exact (hvector a.val a.property).symm

/-- The source right algebra commutes with the common left algebra. -/
theorem commonRightAlgebra_le_commutant
    (M R S : VonNeumannAlgebra H) (hRM : R ≤ M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hS : (S : Set (H →L[ℂ] H)) =
      conjugationOperator J '' (R : Set (H →L[ℂ] H))) :
    S ≤ R.commutant := by
  intro s hs
  change s ∈ (S : Set (H →L[ℂ] H)) at hs
  rw [hS] at hs
  obtain ⟨r, hr, rfl⟩ := hs
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  exact VonNeumannAlgebra.mem_commutant_iff.mp (hrightM r hr) a (hRM ha)

/-- Common right-action data on `R` suffice for uniform rescaled graph
comparison. The ambient algebras need not carry tracial vector states. -/
theorem norm_preparedRight_graphProjection_sub_le
    (M N R : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hirr : ∀ A ∈ M, (∀ a ∈ R, a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hgap : kkDistance M N < 1 / 2)
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hrightN : ∀ r ∈ R, conjugationOperator J r ∈ N.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H)) (G : Algebra N →ₗ[ℂ] (H →L[ℂ] H))
    (hFN : ∀ x, F x ∈ N) (hGM : ∀ x, G x ∈ M) {γ : ℝ} (hγ : 0 ≤ γ)
    (hF : CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ)
    (hG : CompletelyBoundedBy (N.toStarSubalgebra.subtype.toAlgHom.toLinearMap - G) γ)
    {c : ℝ} (hc : 0 < c) :
    ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤
      (32 * Real.sqrt 2 * 131072) * γ := by
  have hER (n : ℕ) : (E n).algebra ≤ R.toStarSubalgebra := by
    intro a ha
    rw [hR]
    exact subset_generatedVonNeumannAlgebra _
      ((le_iSup (fun n => (E n).algebra) n) ha)
  have hEM (n : ℕ) : (E n).algebra ≤ M.toStarSubalgebra :=
    fun _ ha => hRM (hER n ha)
  have hEN (n : ℕ) : (E n).algebra ≤ N.toStarSubalgebra :=
    fun _ ha => hRN (hER n ha)
  have hirrM : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H) := by
    intro A hAM hA
    apply hirr A hAM
    rw [hR]
    exact commute_generated_of_commute_matrix_stages d E A hA
  have hirrNg := relative_irreducibility_of_near_increasing_matrices M N d E hmono hEM
    (by simpa only [← hR] using hirr) hgap
  have hirrN : ∀ A ∈ N, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H) := by
    intro A hAN hA
    exact hirrNg A hAN (commute_generated_of_commute_matrix_stages d E A hA)
  have hcommM : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant := by
    intro j a ha
    exact hrightM (star a) (R.toStarSubalgebra.star_mem' (hER j ha))
  have hcommN : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ N.commutant := by
    intro j a ha
    exact hrightN (star a) (R.toStarSubalgebra.star_mem' (hER j ha))
  have hvectorE : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω := by
    intro j a ha
    exact hvector a (hER j ha)
  have hcentralM : ∀ j a, a ∈ (E j).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω) := by
    intro j a ha z hz
    exact vector_functional_centralizes_of_commonRight R M hRM J hJ Ω hrightM hvector
      ⟨a, hER j ha⟩ ⟨z, hz⟩
  have hcentralN : ∀ j a, a ∈ (E j).algebra → ∀ z ∈ N,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω) := by
    intro j a ha z hz
    exact vector_functional_centralizes_of_commonRight R N hRN J hJ Ω hrightN hvector
      ⟨a, hER j ha⟩ ⟨z, hz⟩
  exact norm_prepared_rescaledGraphProjection_sub_le M N Ω hΩ d E hmono
    hEM hEN hirrM hirrN hcentralM hcentralN J hJ hcommM hcommN hvectorE
    F G hFN hGM hγ hF hG hc

/-- Literal containment of the common right algebra is the only neighbor
right-action premise needed for the graph estimate. -/
theorem norm_preparedRight_graphProjection_sub_le_of_right_algebra
    (M N R S : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hirr : ∀ A ∈ M, (∀ a ∈ R, a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hgap : kkDistance M N < 1 / 2)
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    (hS : (S : Set (H →L[ℂ] H)) =
      conjugationOperator J '' (R : Set (H →L[ℂ] H)))
    (hSN : S ≤ N.commutant)
    (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H)) (G : Algebra N →ₗ[ℂ] (H →L[ℂ] H))
    (hFN : ∀ x, F x ∈ N) (hGM : ∀ x, G x ∈ M) {γ : ℝ} (hγ : 0 ≤ γ)
    (hF : CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ)
    (hG : CompletelyBoundedBy (N.toStarSubalgebra.subtype.toAlgHom.toLinearMap - G) γ)
    {c : ℝ} (hc : 0 < c) :
    ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤
      (32 * Real.sqrt 2 * 131072) * γ := by
  apply norm_preparedRight_graphProjection_sub_le M N R J hJ Ω hΩ d E hmono hR
    hRM hRN hirr hgap hrightM ?_ hvector F G hFN hGM hγ hF hG hc
  intro r hr
  apply hSN
  change conjugationOperator J r ∈ (S : Set (H →L[ℂ] H))
  rw [hS]
  exact ⟨r, hr, rfl⟩

/-- A supplied localized correction gives the generic, possibly nontracial,
prepared graph estimate with its exact ordinary-gap cost. -/
theorem norm_corrected_preparedRight_graphProjection_sub_le
    (M N R S : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hirr : ∀ A ∈ M, (∀ a ∈ R, a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    (hS : (S : Set (H →L[ℂ] H)) =
      conjugationOperator J '' (R : Set (H →L[ℂ] H)))
    (w : unitary (H →L[ℂ] H))
    (hw : (w : H →L[ℂ] H) ∈ generatedVonNeumannAlgebra
      (S.toStarSubalgebra ⊔ N.commutant.toStarSubalgebra))
    (hmove : ∀ s ∈ S, unitaryConj w s ∈ N.commutant)
    (hgap : kkDistance M N + 2 * ‖(w : H →L[ℂ] H) - 1‖ < 1 / 2)
    (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H))
    (G : Algebra (unitaryConjugateAlgebra (star w) N) →ₗ[ℂ] (H →L[ℂ] H))
    (hFN : ∀ x, F x ∈ unitaryConjugateAlgebra (star w) N) (hGM : ∀ x, G x ∈ M)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hF : CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ)
    (hG : CompletelyBoundedBy
      ((unitaryConjugateAlgebra (star w) N).toStarSubalgebra.subtype.toAlgHom.toLinearMap - G) γ)
    {c : ℝ} (hc : 0 < c) :
    ‖rescaledGraphProjection M J Ω c -
      rescaledGraphProjection (unitaryConjugateAlgebra (star w) N) J Ω c‖ ≤
        (32 * Real.sqrt 2 * 131072) * γ := by
  obtain ⟨hleft, hright⟩ := preparedPair_second_correction R S N hRN
    (commonRightAlgebra_le_commutant M R S hRM J hrightM hS) w hw hmove
  exact norm_preparedRight_graphProjection_sub_le_of_right_algebra M
    (unitaryConjugateAlgebra (star w) N) R S J hJ Ω hΩ d E hmono hR hRM hleft hirr
    ((preparedPair_second_correction_gap M N w).trans_lt hgap) hrightM hvector hS hright
    F G hFN hGM hγ hF hG hc

/-- The localized embedding chooses the second correction from the genuine
relative right-action data. No trace on `M` or `N` is assumed. -/
theorem exists_preparedRight_graph_comparison
    (hpub : PublishedLocalizedAmenableEmbedding (H := H))
    (M N R S : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hirr : ∀ A ∈ M, (∀ a ∈ R, a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hvector : ∀ r ∈ R, conjugationOperator J (star r) Ω = r Ω)
    (hS : (S : Set (H →L[ℂ] H)) =
      conjugationOperator J '' (R : Set (H →L[ℂ] H)))
    (hSinj : IsInjective S) {ρ : ℝ}
    (hnear : NearInclusion S N.commutant ρ) (hρ : ρ < 1 / 100)
    (hgap : kkDistance M N + 300 * ρ < 1 / 2) :
    ∃ w : unitary (H →L[ℂ] H),
      R ≤ unitaryConjugateAlgebra (star w) N ∧
      S ≤ (unitaryConjugateAlgebra (star w) N).commutant ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 150 * ρ ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) ≤ kkDistance M N + 300 * ρ ∧
      ∀ (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H))
        (G : Algebra (unitaryConjugateAlgebra (star w) N) →ₗ[ℂ] (H →L[ℂ] H))
        (γ : ℝ),
        (∀ x, F x ∈ unitaryConjugateAlgebra (star w) N) → (∀ x, G x ∈ M) →
        0 ≤ γ →
        CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ →
        CompletelyBoundedBy
          ((unitaryConjugateAlgebra (star w) N).toStarSubalgebra.subtype.toAlgHom.toLinearMap - G) γ →
        ∀ c : ℝ, 0 < c →
          ‖rescaledGraphProjection M J Ω c -
            rescaledGraphProjection (unitaryConjugateAlgebra (star w) N) J Ω c‖ ≤
              (32 * Real.sqrt 2 * 131072) * γ := by
  obtain ⟨w, hleft, hright, hnorm, hdist⟩ := exists_prepared_right_correction hpub
    M N R S hRN (commonRightAlgebra_le_commutant M R S hRM J hrightM hS) hSinj hnear hρ
  refine ⟨w, hleft, hright, hnorm, hdist, ?_⟩
  intro F G γ hFN hGM hγ hF hG c hc
  exact norm_preparedRight_graphProjection_sub_le_of_right_algebra M
    (unitaryConjugateAlgebra (star w) N) R S J hJ Ω hΩ d E hmono hR hRM hleft hirr
    (hdist.trans_lt hgap) hrightM hvector hS hright F G hFN hGM hγ hF hG hc

end

end KadisonKastler

end OAI
