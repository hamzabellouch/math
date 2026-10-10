import OAI.Analysis.KadisonKastler.ExpectedCentralizer
import OAI.Analysis.KadisonKastler.IncreasingMatrixPreparation
import OAI.Analysis.KadisonKastler.ConjugateMatrixStages
import OAI.Analysis.KadisonKastler.ModularConjugationData

namespace OAI

/-! # Modular preparation from an expected finite subalgebra

The trace used here is only on the finite subalgebra. Its composition with
an actual bimodular expectation is represented by the supplied vector.
The modular conjugation data then give precisely the common right-vector
identity used by matrix averaging and graph comparison. The corrected
neighbor is proved cyclic and separating when the two ordinary gaps are
small; these properties are not supplied as preparation assumptions.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ModularConjugationData

variable {M R : VonNeumannAlgebra H} {Ω : H}

/-- Bimodularity of an expectation onto a finite algebra supplies the
centralizer hypothesis required by modular conjugation. -/
theorem common_vector_of_expectation
    (d : ModularConjugationData M Ω) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (r : Algebra R) :
    conjugationOperator d.conjugation (star r.val) Ω = r.val Ω :=
  d.common_vector hRM
    (vector_functional_centralizes_of_expectation M R hRM τ P hleft hright Ω hΩ) r

/-- The expected-state vector has unit norm, and its common right action
has the exact membership and vector identities needed in preparation. -/
theorem expected_right_data
    (d : ModularConjugationData M Ω) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R) (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω)) :
    ‖Ω‖ = 1 ∧
      (∀ r ∈ R, conjugationOperator d.conjugation r ∈ M.commutant) ∧
      (∀ r ∈ R, conjugationOperator d.conjugation (star r) Ω = r Ω) := by
  refine ⟨norm_vector_of_expectedTrace M R τ P hP Ω hΩ, ?_, ?_⟩
  · intro r hr
    exact d.right_mem hRM ⟨r, hr⟩
  · intro r hr
    exact d.common_vector_of_expectation hRM τ P hleft hright hΩ ⟨r, hr⟩

end ModularConjugationData

/-- Conjugation transports the actual commutant, so the same elementary
movement bound applies to the second gap in preparation. -/
theorem unitaryConjugateAlgebra_commutant
    (w : unitary (H →L[ℂ] H)) (N : VonNeumannAlgebra H) :
    (unitaryConjugateAlgebra w N).commutant =
      unitaryConjugateAlgebra w N.commutant := by
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w
  apply SetLike.coe_injective
  rw [VonNeumannAlgebra.coe_commutant]
  change Set.centralizer (e '' (N : Set (H →L[ℂ] H))) =
    e '' (N.commutant : Set (H →L[ℂ] H))
  rw [VonNeumannAlgebra.coe_commutant]
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    rw [map_mul, map_mul]
    change e y * e (e.symm x) = e (e.symm x) * e y
    rw [e.apply_symm_apply]
    exact hx (e y) ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩ z ⟨v, hv, rfl⟩
    simpa only [map_mul] using congrArg e (hy v hv)

theorem preparedPair_second_correction_commutant_gap
    (M N : VonNeumannAlgebra H) (w : unitary (H →L[ℂ] H)) :
    kkDistance M.commutant (unitaryConjugateAlgebra (star w) N).commutant ≤
      kkDistance M.commutant N.commutant + 2 * ‖(w : H →L[ℂ] H) - 1‖ := by
  rw [unitaryConjugateAlgebra_commutant]
  exact preparedPair_second_correction_gap M.commutant N.commutant w

local instance expectedModularOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance expectedModularStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _
local instance expectedModularOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance expectedModularOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- An expected finite common algebra and actual modular conjugation
supply the graph estimate without separate right-action assumptions. -/
theorem exists_expected_modular_graph_comparison
    (hpub : PublishedLocalizedAmenableEmbedding (H := H))
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R) (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (Ω : H) (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (d : ModularConjugationData M Ω)
    (s : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (s n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hRinj : IsInjective R)
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    {ρ : ℝ}
    (hnear : NearInclusion (conjugateRightAlgebra d.conjugation d.involutive R)
      N.commutant ρ)
    (hρ : ρ < 1 / 100) (hgap : kkDistance M N + 300 * ρ < 1 / 2) :
    ∃ w : unitary (H →L[ℂ] H),
      R ≤ unitaryConjugateAlgebra (star w) N ∧
      conjugateRightAlgebra d.conjugation d.involutive R ≤
        (unitaryConjugateAlgebra (star w) N).commutant ∧
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
          ‖rescaledGraphProjection M d.conjugation Ω c -
            rescaledGraphProjection (unitaryConjugateAlgebra (star w) N) d.conjugation Ω c‖ ≤
              (32 * Real.sqrt 2 * 131072) * γ := by
  obtain ⟨hnorm, hmem, hvector⟩ := d.expected_right_data hRM τ P hP hleft hright hΩ
  exact exists_preparedRight_graph_comparison_of_injective hpub M N R
    d.conjugation d.involutive Ω hnorm s E hmono hR hRM hRN hRinj hirr
    hmem hvector hnear hρ hgap

/-- The same expected vector is cyclic and separating for the corrected
neighbor. Smallness of the commutant gap is stated independently of the
left gap and transported through the actual chosen correction. -/
theorem expected_modular_corrected_cyclic_separating
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R) (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (Ω : H) (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (d : ModularConjugationData M Ω)
    (s : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (s n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    (w : unitary (H →L[ℂ] H))
    (hRN : R ≤ unitaryConjugateAlgebra (star w) N)
    (hSN : conjugateRightAlgebra d.conjugation d.involutive R ≤
      (unitaryConjugateAlgebra (star w) N).commutant)
    (hgap : kkDistance M N + 2 * ‖(w : H →L[ℂ] H) - 1‖ < 1 / 2)
    (hgap' : kkDistance M.commutant N.commutant +
      2 * ‖(w : H →L[ℂ] H) - 1‖ < 1 / 2) :
    DenseRange (algebraVectorMap (unitaryConjugateAlgebra (star w) N) Ω) ∧
      Function.Injective (algebraVectorMap (unitaryConjugateAlgebra (star w) N) Ω) ∧
      DenseRange (algebraVectorMap (unitaryConjugateAlgebra (star w) N).commutant Ω) ∧
      Function.Injective (algebraVectorMap (unitaryConjugateAlgebra (star w) N).commutant Ω) := by
  obtain ⟨hnorm, _, hvector⟩ := d.expected_right_data hRM τ P hP hleft hright hΩ
  have hΩ0 : Ω ≠ 0 := by
    intro hz
    simp only [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨hc, hc', hs, hs'⟩ := preparedRight_cyclic_separating_of_matrix_gaps
    M (unitaryConjugateAlgebra (star w) N) R d.conjugation d.involutive d.commutant
    s E hmono hR hRM hRN hSN hirr
    ((preparedPair_second_correction_gap M N w).trans_lt hgap)
    ((preparedPair_second_correction_commutant_gap M N w).trans_lt hgap') Ω hΩ0 hvector
  refine ⟨hc, ?_, hc', ?_⟩
  · intro x y hxy
    have hz : (x - y).val Ω = 0 := by
      change (algebraVectorMap (unitaryConjugateAlgebra (star w) N) Ω) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hs (x - y) hz)
  · intro x y hxy
    have hz : (x - y).val Ω = 0 := by
      change (algebraVectorMap (unitaryConjugateAlgebra (star w) N).commutant Ω) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hs' (x - y) hz)

end

end KadisonKastler

end OAI
