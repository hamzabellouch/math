import OAI.GroupTheory.PolycyclicRecognition.Algebra.InwardVectorCharacters
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RayBoundedRepresentatives
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WellFoundedModuleRelations

namespace OAI

/-! # From a character hemisphere to a single contracting direction

Compact positive identities decrease the squared distance to the negative ray.
Integral translates of a bounded layer have finitely many representatives.
Together these prove finite generation over the inverse cyclic action.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra InnerProductSpace
variable {Q M E : Type} [CommGroup Q] [AddCommGroup M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

theorem finite_cyclicMonoidModule_of_character_hemisphere
    (ρ : Representation ℤ Q M) [Module.Finite ℤ[Q] ρ.asModule]
    (e : Q →* Multiplicative E)
    (hspan : Submodule.span ℝ (Set.range (fun q => (e q).toAdd)) = ⊤)
    (hbounded : ∀ R : ℝ, Set.Finite {q : Q | ‖(e q).toAdd‖ ≤ R}) (t : Q)
    (hfinite : ∀ v : E, ‖v‖ = 1 → 0 ≤ ⟪v, (e t).toAdd⟫_ℝ →
      Module.Finite ℤ[characterNonnegativeMonoid (inwardVectorCharacter e v)]
        (characterMonoidRepresentation ρ (inwardVectorCharacter e v)).asModule) :
    Module.Finite ℤ[Submonoid.powers t⁻¹]
      (Representation.asModule (ρ.comp (Submonoid.powers t⁻¹).subtype)) := by
  classical
  let K := inwardRayHemisphere (e t).toAdd
  obtain ⟨A, hA, δ, hδ, hcover⟩ := compact_positiveIdentity_certificates ρ
    (inwardVectorCharacter e) (inwardVectorCharacter_continuous e) K
    (inwardRayHemisphere_compact _) (fun v hv =>
      inwardVectorCharacter_exists_positive e hspan v (by
        intro hz
        have hh : ‖v‖ = 1 := hv.1
        simp [hz] at hh))
    (fun v hv => hfinite v hv.1 hv.2)
  let S := A.biUnion (fun a => a.coeff.support)
  obtain ⟨C, hC⟩ := (S.finite_toSet.image (fun g => ‖(e g).toAdd‖ ^ 2 + 1)).bddAbove
  obtain ⟨r, hr⟩ := exists_nat_gt (C / (2 * δ))
  have hδ2 : 0 < 2 * δ := by positivity
  have hCr : C < (r : ℝ) * (2 * δ) := (div_lt_iff₀ hδ2).mp hr
  obtain ⟨B, hB⟩ := bounded_ray_layer_representatives e t hbounded (r * r)
  apply finite_submonoidModule_of_decreasing_relations ρ (Submonoid.powers t⁻¹)
    (rayLatticeHeight e t) (r * r) B hB
  intro q hq
  let v := negativeRayResidual (e t).toAdd (e q).toAdd
  have hnorm : (r : ℝ) < ‖v‖ := by
    have hsq : ((r * r : ℕ) : ℝ) < ‖v‖ ^ 2 := (Nat.lt_ceil).mp hq
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
    push_cast at hsq
    nlinarith
  have hv : v ≠ 0 := by
    intro hz
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    simp [hz] at hnorm
    linarith
  have hvK : ‖v‖⁻¹ • v ∈ K := normalized_residual_mem_inwardRayHemisphere _ _ hv
  obtain ⟨a, ha, hpos⟩ := hcover (‖v‖⁻¹ • v) hvK
  refine ⟨a, hA a ha, ?_⟩
  intro g hg
  have hgS : g ∈ S := Finset.mem_biUnion.mpr ⟨a, ha, hg⟩
  have hgC : ‖(e g).toAdd‖ ^ 2 + 1 ≤ C :=
    hC (Set.mem_image_of_mem _ hgS)
  have hlarge : ‖(e g).toAdd‖ ^ 2 + 1 ≤ 2 * δ * ‖v‖ := by
    have hmul := mul_lt_mul_of_pos_right hnorm hδ2
    nlinarith
  change ⌈‖negativeRayResidual (e t).toAdd (e (q * g)).toAdd‖ ^ 2⌉₊ < _
  rw [map_mul, toAdd_mul]
  exact negativeRayResidual_ceil_drop _ _ _ hv δ (hpos g hg) hlarge

end PolycyclicRecognition

end

end OAI
