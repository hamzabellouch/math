import OAI.Analysis.KadisonKastler.SimpleProductStateExtension
import OAI.Analysis.KadisonKastler.ConjugateAlgebraSimplicity
import OAI.Analysis.KadisonKastler.ModularSpectralConstruction
import OAI.Analysis.KadisonKastler.TypeIIISmallNormalizer
import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison
import OAI.Analysis.KadisonKastler.VonNeumannSpectralCut

namespace OAI

/-! # A strongly invariant state with the two modular product marginals

For the actual cyclic separating representation of a type III factor, the
left and right algebras are simple and conjugate. The constructed product
state therefore has a strongly invariant extension to all ambient operators.
This is the product-state step of Marrakchi, arXiv:1811.10253v2, Section 6.
-/

namespace KadisonKastler

open NaimarkZFC MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem ModularConjugationData.commutant_simple
    {M : VonNeumannAlgebra H} {Ω : H} (d : ModularConjugationData M Ω)
    (hM : CStarSimple (Algebra M)) : CStarSimple (Algebra M.commutant) := by
  rw [← d.commutant]
  exact cstarSimple_conjugateAlgebra d.conjugation d.involutive M hM

theorem unitaryConj_mem_commutant_of_normalizes
    (M : VonNeumannAlgebra H) (u : unitary (H →L[ℂ] H))
    (hu : Conjugates u M M) {b : H →L[ℂ] H} (hb : b ∈ M.commutant) :
    unitaryConj u b ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have himage : a ∈ unitaryConj u '' (M : Set (H →L[ℂ] H)) := by rwa [hu]
  rcases himage with ⟨c,hc,rfl⟩
  have he := congrArg (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u)
    (VonNeumannAlgebra.mem_commutant_iff.mp hb c hc)
  rw [map_mul,map_mul] at he
  exact he

theorem exists_modular_product_state_of_simple
    (M : VonNeumannAlgebra H) (Ω : H) (hunit : ‖Ω‖=1)
    (hM : CStarSimple (Algebra M))
    (d : ModularConjugationData M Ω) (S : ModularSpectralResolution M Ω) :
    ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : H →L[ℂ] H),
        ψ (stateActionAverage S.group S.continuous μ a)=ψ a) ∧
      ∀ a ∈ M, ∀ b ∈ M.commutant,
        ψ (a*b)=productVectorState Ω a*productVectorState Ω b := by
  apply exists_strongly_invariant_product_of_simple S.group S.continuous M M.commutant
    hM (d.commutant_simple hM)
    (fun a ha b hb => VonNeumannAlgebra.mem_commutant_iff.mp hb a ha)
  · intro t a ha
    change unitaryConj (S.group (Multiplicative.ofAdd t)) a ∈ (M : Set (H →L[ℂ] H))
    rw [← S.normalizes (Multiplicative.ofAdd t)]
    exact ⟨a,ha,rfl⟩
  · intro t b hb
    exact unitaryConj_mem_commutant_of_normalizes M _ (S.normalizes _) hb
  · exact hunit
  · exact fun t => S.isModular.fixes_vector (Multiplicative.ofAdd t)

theorem exists_typeIII_modular_product_state
    [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (hM : TypeIIIFactor M)
    (Ω : H) (hunit : ‖Ω‖=1)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    ∃ (S : ModularSpectralResolution M Ω) (ψ : (H →L[ℂ] H) →L[ℂ] ℂ), IsState ψ ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : H →L[ℂ] H),
        ψ (stateActionAverage S.group S.continuous μ a)=ψ a) ∧
      ∀ a ∈ M, ∀ b ∈ M.commutant,
        ψ (a*b)=productVectorState Ω a*productVectorState Ω b := by
  obtain ⟨d,S⟩ := publishedModularSpectralResolution H M Ω hcyc hsep
  obtain ⟨ψ,hψ,hstrong,hprod⟩ := exists_modular_product_state_of_simple M Ω hunit
    (typeIII_algebra_simple publishedVonNeumannSpectralCut publishedTypeIIIProjectionComparison M hM) d S
  exact ⟨S,ψ,hψ,hstrong,hprod⟩

end

end KadisonKastler

end OAI
