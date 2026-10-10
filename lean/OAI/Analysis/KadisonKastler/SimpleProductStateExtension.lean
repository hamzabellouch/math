import OAI.Analysis.KadisonKastler.SimpleCommutingProductState
import OAI.Analysis.KadisonKastler.StrongProductStateExtension

namespace OAI

/-! # Strongly invariant product states on commuting simple algebras

The initial product state is constructed by cyclic compression, then
extended with normal marginals and strong invariance.
-/

namespace KadisonKastler

open NaimarkZFC MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem exists_ambient_product_state_of_simple
    (M N : VonNeumannAlgebra H) (hM : CStarSimple (Algebra M))
    (hN : CStarSimple (Algebra N))
    (hcomm : ∀ a ∈ M, ∀ b ∈ N, Commute a b)
    (Ω : H) (hunit : ‖Ω‖=1) :
    ∃ φ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState φ ∧
      ∀ a ∈ M, ∀ b ∈ N,
        φ (a*b)=productVectorState Ω a*productVectorState Ω b := by
  let : Nontrivial H := ⟨⟨Ω,0,by
    intro h
    rw [h,norm_zero] at hunit
    exact zero_ne_one hunit⟩⟩
  let ι := M.toStarSubalgebra.subtype
  let κ := N.toStarSubalgebra.subtype
  let f := NaimarkZFC.vectorFunctional ι.toNonUnitalStarAlgHom Ω
  let g := NaimarkZFC.vectorFunctional κ.toNonUnitalStarAlgHom Ω
  have hf : IsState f := isState_vectorFunctional ι.toNonUnitalStarAlgHom (map_one ι) Ω hunit
  have hg : IsState g := isState_vectorFunctional κ.toNonUnitalStarAlgHom (map_one κ) Ω hunit
  obtain ⟨φ,hφ,hprod⟩ := exists_product_state_of_commuting_simple hM hN ι
    Subtype.val_injective κ (fun a b => hcomm a a.property b b.property) f hf g hg
  exact ⟨φ,hφ,fun a ha b hb => hprod ⟨a,ha⟩ ⟨b,hb⟩⟩

theorem exists_strongly_invariant_product_of_simple
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M N : VonNeumannAlgebra H) (hMs : CStarSimple (Algebra M))
    (hNs : CStarSimple (Algebra N))
    (hcomm : ∀ a ∈ M, ∀ b ∈ N, Commute a b)
    (hM : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (hN : ∀ t a, a ∈ N → stateActionOrbit U a t ∈ N)
    (Ω : H) (hunit : ‖Ω‖=1)
    (hfix : ∀ t : ℝ, (U (Multiplicative.ofAdd t) : H →L[ℂ] H) Ω=Ω) :
    ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : H →L[ℂ] H),
        ψ (stateActionAverage U hU μ a)=ψ a) ∧
      ∀ a ∈ M, ∀ b ∈ N,
        ψ (a*b)=productVectorState Ω a*productVectorState Ω b := by
  obtain ⟨φ,hφ,hprod⟩ := exists_ambient_product_state_of_simple M N hMs hNs hcomm Ω hunit
  exact exists_strongly_invariant_product_state U hU M N hM hN Ω hunit hfix φ hφ hprod

end

end KadisonKastler

end OAI
