import OAI.Analysis.KadisonKastler.StateModularTransport
import OAI.Analysis.KadisonKastler.ModularStateAction

namespace OAI

/-! # State-preserving spatial symmetries commute with the modular group -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (u : unitary (H →L[ℂ] H)) (hu : Conjugates u M M)
  (hfix : (u : H →L[ℂ] H) Ω = Ω)

include u hu in
private def stateSymmetryHom : Algebra M →⋆ₐ[ℂ] Algebra M :=
  (((Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u).toStarAlgHom).comp
    M.toStarSubalgebra.subtype).codRestrict M.toStarSubalgebra (fun a => by
      change unitaryConj u a.val ∈ (M : Set (H →L[ℂ] H))
      rw [← hu]
      exact Set.mem_image_of_mem _ a.property)

include u hu in
def stateSymmetryAut : Algebra M ≃⋆ₐ[ℂ] Algebra M := by
  apply StarAlgEquiv.ofBijective (stateSymmetryHom u hu)
  constructor
  · intro a b h
    apply Subtype.ext
    apply (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u).injective
    exact congrArg Subtype.val h
  · intro a
    have ha : a.val ∈ unitaryConj u '' (M : Set (H →L[ℂ] H)) := by
      rw [hu]
      exact a.property
    obtain ⟨b, hb, he⟩ := ha
    exact ⟨⟨b, hb⟩, Subtype.ext he⟩

theorem stateSymmetryAut_coe (a : Algebra M) :
    (stateSymmetryAut u hu a).val = unitaryConj u a.val := rfl

include hfix in
theorem stateSymmetryAut_vector (a : Algebra M) :
    (stateSymmetryAut u hu a).val Ω = (u : H →L[ℂ] H) (a.val Ω) := by
  have hs : star (u : H →L[ℂ] H) Ω = Ω := by
    have hh := congrArg (fun A : H →L[ℂ] H => A Ω) (Unitary.star_mul_self_of_mem u.property)
    change star (u : H →L[ℂ] H) ((u : H →L[ℂ] H) Ω) = Ω at hh
    rwa [hfix] at hh
  change (u : H →L[ℂ] H) (a.val (star (u : H →L[ℂ] H) Ω)) = _
  rw [hs]

include hfix in
theorem stateSymmetryAut_state (a : Algebra M) :
    inner ℂ Ω (a.val Ω) = inner ℂ Ω ((stateSymmetryAut u hu a).val Ω) := by
  exact (productVectorState_unitaryConj_of_fixes Ω u hfix a.val).symm

variable (hcyc : DenseRange (algebraVectorMap M Ω))

include hfix in
theorem stateSymmetry_spatial :
    statePreservingUnitary (stateSymmetryAut u hu) Ω Ω hcyc hcyc
      (stateSymmetryAut_state Ω u hu hfix) = Unitary.linearIsometryEquiv u := by
  apply LinearIsometryEquiv.ext
  intro x
  apply hcyc.induction_on (p := fun x =>
    statePreservingUnitary (stateSymmetryAut u hu) Ω Ω hcyc hcyc
      (stateSymmetryAut_state Ω u hu hfix) x = (u : H →L[ℂ] H) x) x
  · exact isClosed_eq (map_continuous _) u.val.continuous
  · intro a
    change statePreservingUnitary (stateSymmetryAut u hu) Ω Ω hcyc hcyc
      (stateSymmetryAut_state Ω u hu hfix) (a.val Ω) = (u : H →L[ℂ] H) (a.val Ω)
    rw [statePreservingUnitary_algebraVector, stateSymmetryAut_vector Ω u hu hfix]

include hu hfix hcyc in
theorem stateSymmetry_resolvent (J : H ≃ₗᵢ⋆[ℂ] H) (c : ℝ) (x : H) :
    (u : H →L[ℂ] H) (graphResolvent M J Ω c x) =
      graphResolvent M J Ω c ((u : H →L[ℂ] H) x) := by
  have h := statePreservingUnitary_resolvent_apply (stateSymmetryAut u hu) Ω Ω hcyc hcyc
    (stateSymmetryAut_state Ω u hu hfix) J J c x
  rw [stateSymmetry_spatial Ω u hu hfix hcyc] at h
  exact h

variable [TopologicalSpace.SeparableSpace H]
  (hsep : Function.Injective (algebraVectorMap M Ω))

include hu hfix in
theorem stateSymmetry_modular (J : H ≃ₗᵢ⋆[ℂ] H) (t : Multiplicative ℝ) (x : H) :
    (u : H →L[ℂ] H) ((modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) x) =
      (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) ((u : H →L[ℂ] H) x) := by
  have h := statePreservingUnitary_modular (stateSymmetryAut u hu) Ω Ω hcyc hcyc
    (stateSymmetryAut_state Ω u hu hfix) J J hsep hsep t x
  rw [stateSymmetry_spatial Ω u hu hfix hcyc] at h
  exact h

end

end KadisonKastler

end OAI
