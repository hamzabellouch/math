import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CyclicInvariantTopHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InvariantTopTwist
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalLineProperties
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NestedNormalHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyBoundTransport

namespace OAI

/-! # Raising invariant top homology along a normal cyclic step -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
variable {G : Type} [Group G]

theorem exists_normalCyclicTopStep (N K : Subgroup G) [N.Normal] [K.Normal]
    (hNK : N ≤ K) (q : K →* Multiplicative ℤ) (t : K)
    (ht : q t = Multiplicative.ofAdd 1) (hker : q.ker = N.subgroupOf K)
    (d : ℕ) (hbound : ∀ R : Rep ℤ N, ∀ j, d < j → IsZero (groupHomology R j))
    (A : Rep ℤ G) (eN : groupHomology (Rep.res N.subtype A) d ≃ₗ[ℤ] ℚ)
    (hA : ∀ g, normalHomologyMap ℤ N A d g = 𝟙 _) :
    ∃ B : Rep ℤ G,
      Nonempty (groupHomology (Rep.res K.subtype B) (d + 1) ≃ₗ[ℤ] ℚ) ∧
      ∀ g, normalHomologyMap ℤ K B (d + 1) g = 𝟙 _ := by
  let e : q.ker ≃* N := (MulEquiv.subgroupCongr hker).trans (Subgroup.subgroupOfEquivOfLe hNK)
  have he : ∀ a : q.ker, ((e a : N) : G) = ((a : K) : G) := by intro a; rfl
  let E := embeddedSubgroupHomologyIso N K A q.ker e he d
  have ha : normalHomologyMap ℤ q.ker (Rep.res K.subtype A) d t⁻¹ = 𝟙 _ := by
    apply (cancel_mono E.hom).mp
    have h := embeddedSubgroupHomologyIso_conjugation N K A q.ker e he d t⁻¹
    rw [hA] at h
    simpa only [Category.comp_id, Category.id_comp] using h
  have hb := homology_bound_of_equiv e.symm d hbound
  have hv := hb (Rep.res q.ker.subtype (Rep.res K.subtype A)) (d + 1) (by omega)
  let F := cyclicInvariantTopHomologyIso q t ht (Rep.res K.subtype A) d hv ha
  let eK : groupHomology (Rep.res K.subtype A) (d + 1) ≃ₗ[ℤ] ℚ :=
    F.toLinearEquiv.trans (E.toLinearEquiv.trans eN)
  obtain ⟨⟨x, hx⟩, htor, hcomm⟩ := rationalLine_properties _ eK
  obtain ⟨η, _, hB, hinv⟩ := exists_invariantTopTwist K A (d + 1) x hx htor hcomm
  exact ⟨rationalScalarTwist A η, hB, hinv⟩

end PolycyclicRecognition

end

end OAI
