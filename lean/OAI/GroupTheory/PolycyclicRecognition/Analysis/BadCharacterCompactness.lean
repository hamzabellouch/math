import OAI.GroupTheory.PolycyclicRecognition.Algebra.InwardVectorCharacters

namespace OAI

/-! # Compactness of the bad unit-character set

The full positive-identity criterion makes the good region open. Its complement
on the unit sphere is the compact set used in the convex tameness argument.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {Q M E : Type} [CommGroup Q] [AddCommGroup M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : Representation ℤ Q M) [Module.Finite ℤ[Q] ρ.asModule]
  (e : Q →* Multiplicative E)

def positiveIdentityRegion : Set E := {v | ∃ a : ℤ[Q], ρ.asAlgebraHom a = 1 ∧
  ∀ q ∈ a.coeff.support, 0 < (inwardVectorCharacter e v q).toAdd}

def badUnitCharacters : Set E := {v | ‖v‖ = 1 ∧
  ¬Module.Finite ℤ[characterNonnegativeMonoid (inwardVectorCharacter e v)]
    (characterMonoidRepresentation ρ (inwardVectorCharacter e v)).asModule}

omit [Module.Finite ℤ[Q] ρ.asModule] in
theorem positiveIdentityRegion_open : IsOpen (positiveIdentityRegion ρ e) := by
  have he : positiveIdentityRegion ρ e = ⋃ a : ℤ[Q], ⋃ (_h : ρ.asAlgebraHom a = 1),
      {v : E | ∀ q ∈ a.coeff.support, 0 < (inwardVectorCharacter e v q).toAdd} := by
    ext v
    simp only [positiveIdentityRegion, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [he]
  exact isOpen_iUnion fun a => isOpen_iUnion fun _ =>
    isOpen_positiveIdentitySupport (inwardVectorCharacter e) (inwardVectorCharacter_continuous e) a 0

theorem badUnitCharacters_eq_sdiff
    (hspan : Submodule.span ℝ (Set.range (fun q => (e q).toAdd)) = ⊤) :
    badUnitCharacters ρ e = {v : E | ‖v‖ = 1} \ positiveIdentityRegion ρ e := by
  ext v
  constructor
  · rintro ⟨hv, hbad⟩
    refine ⟨hv, ?_⟩
    rintro ⟨a, hid, hpos⟩
    exact hbad (finite_characterMonoidModule_of_positive_identity ρ
      (inwardVectorCharacter e v) a hpos hid)
  · rintro ⟨hv, hbad⟩
    refine ⟨hv, ?_⟩
    intro hfinite
    let := hfinite
    obtain ⟨q, hq⟩ := inwardVectorCharacter_exists_positive e hspan v (by
      intro hz
      simp [hz] at hv)
    obtain ⟨a, hpos, hid⟩ := positive_identity_of_finite_characterMonoidModule ρ
      (inwardVectorCharacter e v) q hq
    exact hbad ⟨a, hid, hpos⟩

theorem badUnitCharacters_compact [ProperSpace E]
    (hspan : Submodule.span ℝ (Set.range (fun q => (e q).toAdd)) = ⊤) :
    IsCompact (badUnitCharacters ρ e) := by
  rw [badUnitCharacters_eq_sdiff ρ e hspan]
  have hs : IsCompact {v : E | ‖v‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using (isCompact_sphere (0 : E) 1)
  exact hs.inter_right (positiveIdentityRegion_open ρ e).isClosed_compl

end PolycyclicRecognition

end

end OAI
