import OAI.GroupTheory.PolycyclicRecognition.Finiteness.VirtuallyMetabelianFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoarseFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SolvablePoincareFiniteness

namespace OAI

/-! # The cohomological recognition endgame for virtually metabelian groups

The virtually metabelian finiteness theorem supplies finite cohomological
dimension, so duality transfer proves virtual polycyclicity.
-/

namespace PolycyclicRecognition

theorem virtuallyPolycyclic_of_coarse_PD_virtually_metabelian
    (Γ G : Type) [Group Γ] [Group G] [Group.FG Γ] [Group.FG G]
    (e : GroupCoarseEquivalence Γ G) (n : ℕ)
    (hΓ : IsIntegralPoincareDualityGroup Γ n)
    (H : Subgroup G) [H.FiniteIndex] [IsMulCommutative (commutator H)] :
    IsVirtuallyPolycyclic G := by
  have hFP : TypeFPInfinity G := fun i =>
    liFinitenessInput Γ G e i (hΓ.typeFPInfinity Γ i)
  obtain ⟨V, hVi, hVs, hVd⟩ := virtually_metabelian_virtual_finite_dimension H hFP
  let := hVi
  let := hVs
  let eV : GroupCoarseEquivalence Γ V := e.trans (finiteIndexCoarseEquivalence V).symm
  have hVPD := liDualityInput Γ V eV (hΓ.finiteCohomologicalDimension Γ) hVd n hΓ
  exact ⟨V, hVi, bieriDualityInput V n hVPD⟩

end PolycyclicRecognition

end OAI
