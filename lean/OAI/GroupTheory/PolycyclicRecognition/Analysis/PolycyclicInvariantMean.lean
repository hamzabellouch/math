import OAI.GroupTheory.PolycyclicRecognition.Analysis.ExtensionInvariantMean
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CyclicInvariantMean
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Polycyclic
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteFolnerMean
import OAI.GroupTheory.Thompson.MeanToFolner

namespace OAI

/-! # Concrete invariant means for virtually polycyclic groups

The finite cyclic subnormal series gives the mean by successive kernel and
quotient averages. Thus amenability in the model reduction is proved from
polycyclicity, rather than retained as an extra premise.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability ChromaticCyclic

variable {G : Type*} [Group G]

theorem invariantMean_of_cyclicStep {H K : Subgroup G} (s : CyclicStep H K)
    (hH : Nonempty (InvariantMean H)) : Nonempty (InvariantMean K) := by
  let := s.normal
  let := s.cyclic
  let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
  exact invariantMean_of_normal_subgroup (H.subgroupOf K)
    ⟨imageInvariantMean e.toMonoidHom e.surjective hH.some⟩ invariantMean_of_isCyclic

theorem invariantMean_of_cyclicSeries {H K : Subgroup G} {n : ℕ}
    (c : CyclicSeries H K n) (hH : Nonempty (InvariantMean H)) :
    Nonempty (InvariantMean K) := by
  have hm : ∀ i, i ≤ n → Nonempty (InvariantMean (c.group i)) := by
    intro i
    induction i with
    | zero => intro _; rw [c.first]; exact hH
    | succ i ih =>
      intro hi
      exact invariantMean_of_cyclicStep (c.step i (by omega)) (ih (by omega))
  rw [← c.last]
  exact hm n le_rfl

theorem invariantMean_of_isPolycyclic (hG : IsPolycyclic G) :
    Nonempty (InvariantMean G) := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  have htop := invariantMean_of_cyclicSeries c ⟨finiteInvariantMean⟩
  exact ⟨imageInvariantMean (⊤ : Subgroup G).subtype
    (by intro g; exact ⟨⟨g, trivial⟩, rfl⟩) htop.some⟩

theorem invariantMean_of_isVirtuallyPolycyclic (hG : IsVirtuallyPolycyclic G) :
    Nonempty (InvariantMean G) := by
  obtain ⟨K, hindex, hK⟩ := hG
  let := hindex
  exact invariantMean_of_finiteIndex K (invariantMean_of_isPolycyclic hK)

/-- The existing finite coarea argument converts the constructed mean to
the finite Følner sets used in the metric comparison. -/
theorem finiteFolnerSets_of_invariantMean [DecidableEq G] (M : InvariantMean G) :
    HasFiniteFolnerSets G := by
  intro S ε hε
  obtain ⟨A, hA, hsmall⟩ := M.exists_folner S hε
  refine ⟨A, hA, fun g hg => ?_⟩
  unfold boundaryRatio
  exact (div_lt_iff₀ (by exact_mod_cast hA.card_pos)).mpr (hsmall g hg)

theorem finiteFolnerSets_of_isVirtuallyPolycyclic [DecidableEq G]
    (hG : IsVirtuallyPolycyclic G) : HasFiniteFolnerSets G :=
  finiteFolnerSets_of_invariantMean (invariantMean_of_isVirtuallyPolycyclic hG).some

end PolycyclicRecognition

end

end OAI
