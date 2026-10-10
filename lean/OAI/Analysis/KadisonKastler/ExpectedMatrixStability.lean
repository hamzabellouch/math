import OAI.Analysis.KadisonKastler.MatrixStagePairPreparation
import OAI.Analysis.KadisonKastler.PreparedMatrixStability
import OAI.Analysis.KadisonKastler.NormalTypeIII1Transport
import OAI.Analysis.KadisonKastler.NormalUnitaryConjugation
import OAI.Analysis.KadisonKastler.NormalStarEquivComposition

namespace OAI

/-! # Stability from an expected irreducible increasing matrix algebra

The actual two amenable corrections prepare the common left and right
matrix algebras. The corrected neighbor remains type III₁ by core
isomorphism, and its cyclic separating vector supplies the modular data
for prepared matrix stability. All tolerances precede the algebras and
the expectation data; no trace is required on either ambient factor.
-/

namespace KadisonKastler

open Generator

noncomputable section

universe u

local instance expectedStabilityOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance expectedStabilityStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

section Transport

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

private theorem corrected_neighbor_typeIII1
    (N : VonNeumannAlgebra H) (hN : TypeIII1Factor N)
    (Ω : H) (hΩ : ‖Ω‖ = 1) (hc : DenseRange (algebraVectorMap N Ω))
    (hs : Function.Injective (algebraVectorMap N Ω))
    (m : ModularSpectralResolution N Ω) (a b : unitary (H →L[ℂ] H)) :
    TypeIII1Factor (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)) := by
  let e := unitaryConjugateEquiv (star a) N
  let f := unitaryConjugateEquiv (star b) (unitaryConjugateAlgebra (star a) N)
  exact hN.of_normalStarAlgEquiv (e.trans f)
    (boundedWeakNormal_starEquiv_trans e f
      (unitaryConjugateEquiv_boundedWeakNormal N (star a))
      (unitaryConjugateEquiv_boundedWeakNormal (unitaryConjugateAlgebra (star a) N) (star b)))
    Ω hΩ hc hs m

private theorem corrected_neighbor_core
    (N : VonNeumannAlgebra H) (hN : TypeIII1Factor N)
    (ΩN : H) (hΩN : ‖ΩN‖ = 1) (hcN : DenseRange (algebraVectorMap N ΩN))
    (hsN : Function.Injective (algebraVectorMap N ΩN))
    (mN : ModularSpectralResolution N ΩN) (a b : unitary (H →L[ℂ] H))
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (hc : DenseRange (algebraVectorMap
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)) Ω))
    (hs : Function.Injective (algebraVectorMap
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)) Ω))
    (n : ModularSpectralResolution
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)) Ω) :
    TypeIIInfinityFactor (regularCoreAlgebra n.group n.continuous
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N))) := by
  apply (corrected_neighbor_typeIII1 N hN ΩN hΩN hcN hsN mN a b).core_type
    Ω hΩ hc hs n.group n.continuous
  · intro t x hx
    change unitaryConj (n.group t) x ∈
      (unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N) :
        Set (H →L[ℂ] H))
    rw [← n.normalizes t]
    exact Set.mem_image_of_mem _ hx
  · exact n.isModular

end Transport

/-- Two type III₁ factors are strongly close when the source has the
specified expected irreducible increasing matrix algebra and the pair
is close on all matrix unit balls. The tolerance is independent of all
representation, vector and expectation data. -/
theorem uniform_expected_matrix_typeIII1_stability
    (h : ModularCorePublishedInputs.{u})
    (hModular : PublishedModularSpectralResolution.{u})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N : VonNeumannAlgebra H), TypeIII1Factor M → TypeIII1Factor N →
      ∀ (A : ℕ → FiniteMatrixStage M),
        Monotone (fun n => (A n).units.concreteAlgebra) →
      ∀ (τ : FaithfulTracialState (Algebra (FiniteMatrixStage.generatedVonNeumann A)))
        (P : Algebra M →L[ℂ] Algebra (FiniteMatrixStage.generatedVonNeumann A)), P 1 = 1 →
      (∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann A)) (x : Algebra M),
        P (StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le A) r * x) =
          r * P x) →
      (∀ (r : Algebra (FiniteMatrixStage.generatedVonNeumann A)) (x : Algebra M),
        P (x * StarSubalgebra.inclusion (FiniteMatrixStage.generatedVonNeumann_le A) r) =
          P x * r) →
      ∀ (Ω : H), (∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω)) →
        DenseRange (algebraVectorMap M Ω) → Function.Injective (algebraVectorMap M Ω) →
      (∀ T ∈ M, (∀ r ∈ FiniteMatrixStage.generatedVonNeumann A, r * T = T * r) →
        ∃ z : ℂ, T = z • (1 : H →L[ℂ] H)) →
      ∀ (ΩN : H), ‖ΩN‖ = 1 → DenseRange (algebraVectorMap N ΩN) →
        Function.Injective (algebraVectorMap N ΩN) →
      ∀ γ : ℝ, 0 < γ → γ < δ → kkDistance M N < γ →
        MatrixNearInclusion M N γ → MatrixNearInclusion N M γ → NearConjugacy M N ε := by
  obtain ⟨t, ht, hstable⟩ := uniform_prepared_matrix_strong_stability h (half_pos hε)
  refine ⟨min (1 / 200000) (min (t / 90902) (ε / 90900)),
    lt_min (by norm_num) (lt_min (div_pos ht (by norm_num))
      (div_pos hε (by norm_num))), ?_⟩
  intro H _ _ _ _ _ M N hM hN A hA τ P hP hleft hright Ω hstate hcM hsM hirr
    ΩN hΩN hcN hsN γ hγ hsmall hgap hMN hNM
  have hprepare : γ < 1 / 200000 := hsmall.trans_le (min_le_left _ _)
  have hscale : 90902 * γ < t := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hx' := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 90902)).mp hx
    linarith
  have hcost : 45450 * γ + ε / 2 < ε := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    have hx' := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 90900)).mp hx
    linarith
  obtain ⟨d, m⟩ := (hModular H M Ω hcM hsM).some
  let mN : ModularSpectralResolution N ΩN := (hModular H N ΩN hcN hsN).some.2
  obtain ⟨a, b, ha, hb, hRN, hSN, hMN₂, hN₂M, hgap₂, hc₂, hs₂, _, _⟩ :=
    exists_matrixStagePair_preparation
      (fun M => publishedBlockCommutantApproximation (Algebra M) H)
      M N A hA τ P hP hleft hright Ω hstate d hirr
      hγ hprepare hgap hMN hNM
  let N₂ := unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)
  obtain ⟨hnorm, hrightM, hvector⟩ := d.expected_right_data
    (FiniteMatrixStage.generatedVonNeumann_le A) τ P hP hleft hright hstate
  let n : ModularSpectralResolution N₂ Ω := (hModular H N₂ Ω hc₂ hs₂).some.2
  have hNcore : TypeIIInfinityFactor (regularCoreAlgebra n.group n.continuous N₂) :=
    corrected_neighbor_core N hN ΩN hΩN hcN hsN mN a b Ω hnorm hc₂ hs₂ n
  have hrightN : ∀ r ∈ FiniteMatrixStage.generatedVonNeumann A,
      conjugationOperator d.conjugation r ∈ N₂.commutant := by
    intro r hr
    apply hSN
    change conjugationOperator d.conjugation r ∈
      (conjugateRightAlgebra d.conjugation d.involutive
        (FiniteMatrixStage.generatedVonNeumann A) : Set (H →L[ℂ] H))
    rw [conjugateRightAlgebra_coe]
    exact ⟨r, hr, rfl⟩
  have hmonotone : 90901 * γ ≤ 90902 * γ := by nlinarith
  have hv : NearConjugacy M N₂ (ε / 2) :=
    hstable H M N₂ (FiniteMatrixStage.generatedVonNeumann A) hM.toTypeIIIFactor
      Ω m n d.conjugation d.involutive hnorm hNcore
      (fun i => (A i).size) (matrixStageConcreteUnits A)
      (by simpa only [matrixStageConcreteUnits_algebra] using hA)
      (generated_matrixStages_eq A hA) (FiniteMatrixStage.generatedVonNeumann_le A) hRN
      hirr hrightM hrightN hvector (90902 * γ) (by positivity) hscale hgap₂
      (hMN₂.mono hmonotone) (hN₂M.mono hmonotone)
  obtain ⟨v, hv, hnormv⟩ := nearConjugacy_of_matrixPair_preparation M N a b ha hb hv
  exact ⟨v, hv, hnormv.trans hcost⟩

end

end KadisonKastler

end OAI
