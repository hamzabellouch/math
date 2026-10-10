import OAI.Analysis.KadisonKastler.PositiveOrbitDensity
import OAI.Analysis.KadisonKastler.PositiveStateRepresentative
import OAI.Analysis.KadisonKastler.CornerHomogeneityApplication

namespace OAI

/-! # Faithful state homogeneity from the constructed modular coisometries

This is the state homogeneity needed by the two-ratio product application;
no homogeneity theorem for arbitrary type III₁ factors is assumed.
-/

namespace KadisonKastler
open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance coisometryHomogeneityReal : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem stateHomogeneity_of_modular_coisometries
    (Ω : H) (hΩs : Function.Injective (algebraVectorMap M Ω))
    (hΩc : DenseRange (algebraVectorMap M Ω)) (L : H ≃ₗᵢ⋆[ℂ] H)
    (hIII : TypeIIIFactor M)
    (hremote : UniversalModularCoisometries M (tomitaPolarConjugation L Ω hΩs hΩc)) :
    FaithfulVectorStateHomogeneity M := by
  let d := constructedModularConjugationData L Ω hΩs hΩc
    (tomitaPolarConjugation_commutant_eq L Ω hΩs hΩc)
  have hpos : ∀ a : Algebra M, 0 ≤ inner ℝ Ω (modularQuadratic d.conjugation a Ω) :=
    fun a => (tomitaPolarConjugation_quadratic_nonneg L Ω hΩs hΩc a).1
  intro ξ ζ hξ hζ hsξ hsζ ε hε
  obtain ⟨x,hx,hxn,hxs,_,hxstate⟩ :=
    hIII.exists_positive_unit_state_representative Ω hΩc hΩs L ζ hζ hsζ
  obtain ⟨y,hy,hyn,_,_,hystate⟩ :=
    hIII.exists_positive_unit_state_representative Ω hΩc hΩs L ξ hξ hsξ
  obtain ⟨u,hu⟩ := positive_unitary_orbit_dense d.conjugation d.involutive
    (d.right_mem le_rfl) d.left_mem Ω d.fixes_vector hpos hIII hremote
    x y hx hy hxn hyn hxs (ε/2) (by positivity)
  refine ⟨u,?_⟩
  have hb := vectorFunctional_norm_sub_le (M := M)
    ((modularUnitary d.conjugation d.involutive u : H →L[ℂ] H) y) x
  rw [modularUnitary_vectorFunctional d.conjugation d.involutive (d.right_mem le_rfl),
    hxstate,hystate,Unitary.norm_map,hxn,hyn] at hb
  have hd : ‖(modularUnitary d.conjugation d.involutive u : H →L[ℂ] H) y-x‖<ε/2 := by
    rw [norm_sub_rev]
    exact hu
  linarith

end
end KadisonKastler

end OAI
