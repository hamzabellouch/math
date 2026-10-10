import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentRootGenerators
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentUniqueRoots

namespace OAI

/-! # Homomorphisms determined by finitely many root generators -/

noncomputable section
namespace PolycyclicRecognition

variable {G N : Type} [Group G] [Group N] [Group.IsNilpotent N]

theorem hom_ext_of_subgroup_containing_powers
    (hN : HasNoNontrivialTorsion N) (H : Subgroup G)
    (hH : ∀ g : G, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H)
    {f g : G →* N} (heq : ∀ x ∈ H, f x = g x) : f = g := by
  let := nilpotent_isMulTorsionFree hN
  apply MonoidHom.ext
  intro x
  obtain ⟨n, hn, hx⟩ := hH x
  apply pow_left_injective (Nat.ne_of_gt hn)
  simpa only [map_pow] using heq (x ^ n) hx

theorem nilpotent_exists_finite_hom_determining_set
    [Group.IsNilpotent G] (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ S : Set G, S.Finite ∧ ∀ {N : Type} [Group N] [Group.IsNilpotent N],
      HasNoNontrivialTorsion N → ∀ f g : G →* N, Set.EqOn f g S → f = g := by
  obtain ⟨H, hH, hroots⟩ := nilpotent_exists_fg_subgroup_containing_powers hG
  obtain ⟨S, hS, hfinite⟩ := (Subgroup.fg_iff H).mp hH
  refine ⟨S, hfinite, ?_⟩
  intro N _ _ hN f g heq
  apply hom_ext_of_subgroup_containing_powers hN H hroots
  rw [← hS]
  exact MonoidHom.eqOn_closure heq

end PolycyclicRecognition

end

end OAI
