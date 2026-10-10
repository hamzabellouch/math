import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalSolvableDimension
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteKernelCoarseEquivalence
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.VirtualPolycyclicDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SolvablePoincareFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoarseFiniteness

namespace OAI

/-! # Recognition from virtual solvability and the proved rational bounds

A finite normal subgroup is removed before duality transfer. Polycyclicity
then lifts across that finite kernel. No virtual integral dimension of the
original group is assumed in this argument.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {P G : Type} [Group P] [Group G] [Group.FG P] [Group.FG G]

theorem virtuallyPolycyclic_of_coarse_rational_bounds
    (e : GroupCoarseEquivalence P G) (hP : IsVirtuallyPolycyclic P)
    (d : ℕ) (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hs : ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H) :
    IsVirtuallyPolycyclic G := by
  obtain ⟨H, hHi, hHs⟩ := hs
  let := hHi
  let := hHs
  obtain ⟨T, hTn, hTf, V, hVi, hVs, hVdim⟩ :=
    solvable_rational_mod_finite_radical_dimension d
      (RationalQuotient.rational_dimension_subgroup H d hd) (hb.subgroup H)
  let := hTn
  let := hTf
  let := hVi
  let := hVs
  let : Finite (QuotientGroup.mk' T).ker := by
    simpa only [QuotientGroup.ker_mk'] using hTf
  let eQ : GroupCoarseEquivalence P (H ⧸ T) :=
    (e.trans (finiteIndexCoarseEquivalence H).symm).trans
      (finiteKernelCoarseEquivalence (QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T))
  obtain ⟨K, Γ, _, _, hΓfg, ⟨eΓ⟩, n, hΓPD⟩ :=
    exists_coarse_poincareDuality_comparison_proved P (H ⧸ T) hP eQ
  let := hΓfg
  have hVPD := liDualityInput Γ V (eΓ.trans (finiteIndexCoarseEquivalence V).symm)
    (hΓPD.finiteCohomologicalDimension Γ) hVdim n hΓPD
  have hQ : IsPolycyclic (H ⧸ T) :=
    (show IsVirtuallyPolycyclic (H ⧸ T) from
      ⟨V, hVi, hVPD.polycyclic⟩).polycyclic_of_solvable
  exact ⟨H, hHi, isPolycyclic_of_normal_subgroup T isPolycyclic_of_finite_solvable hQ⟩

end PolycyclicRecognition

end

end OAI
