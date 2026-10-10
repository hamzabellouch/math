import OAI.Analysis.KadisonKastler.CommutingKMSActions
import OAI.Analysis.KadisonKastler.StateGroupDetermination
import OAI.Analysis.KadisonKastler.ConstructedModularData
import OAI.Analysis.KadisonKastler.ModularNormalization

namespace OAI

/-! # Uniqueness of a KMS implementation for a faithful cyclic vector

State-preserving symmetries commute with the constructed modular group.
The Gaussian strip argument then identifies their actions, and cyclicity
identifies the implementations themselves.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem kmsGroup_eq_constructed (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : U = modularStrongGroup J Ω hsep hcyc := by
  let m := constructedModularSpectralResolution J Ω hsep hcyc
    (modularStrongGroup_normalizes J Ω hsep hcyc)
  have hnV : ∀ t a, a ∈ M → unitaryConj (m.group t) a ∈ M := by
    intro t a ha
    change unitaryConj (m.group t) a ∈ (M : Set (H →L[ℂ] H))
    rw [← m.normalizes t]
    exact Set.mem_image_of_mem _ ha
  have he : ∀ t a, a ∈ M → unitaryConj (U t) a = unitaryConj (m.group t) a := by
    intro t a ha
    exact commuting_kms_actions_eq Ω U m.group hU m.continuous hsep hnU hnV
      (stateGroup_commutes_modular Ω U hnU hm.fixes_vector hcyc hsep J)
      hm.kms m.isModular.kms a ha t.toAdd
  exact stateGroups_eq_of_actions Ω hcyc U m.group hnU hnV hm.fixes_vector
    m.isModular.fixes_vector he

end

end KadisonKastler

end OAI
