import OAI.Probability.FreeIsing.Trees.ConnectedHull
import OAI.Probability.FreeIsing.Trees.Shells

namespace OAI

noncomputable section

namespace Problem367

namespace ConnectedHull

theorem hull_mono {d : ℕ} : Monotone (@hull d) := by
  classical
  intro D E hDE v hv
  rcases Finset.mem_insert.mp hv with hroot | hv
  · exact Finset.mem_insert.mpr (Or.inl hroot)
  · obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨w, hDE hw, hvw⟩))

end ConnectedHull

def connectedExhaustion {d : ℕ} (v : TreeVertex d) (n : ℕ) : Finset (TreeVertex d) := by
  classical
  exact ConnectedHull.hull (insert v (treeBallFinset d n))

theorem connectedExhaustion_connected {d : ℕ} (v : TreeVertex d) (n : ℕ) :
    ConnectedFinset (connectedExhaustion v n) :=
  ConnectedHull.connected_hull _

theorem mem_connectedExhaustion {d : ℕ} (v : TreeVertex d) (n : ℕ) :
    v ∈ connectedExhaustion v n := by
  classical
  exact ConnectedHull.subset_hull _ (Finset.mem_insert_self _ _)

theorem connectedExhaustion_monotone {d : ℕ} (v : TreeVertex d) :
    Monotone (connectedExhaustion v) := by
  classical
  intro n m hnm
  exact ConnectedHull.hull_mono (Finset.insert_subset_insert v
    (monotone_treeBallFinset d hnm))

theorem eventually_mem_connectedExhaustion {d : ℕ} (v w : TreeVertex d) :
    ∀ᶠ n in Filter.atTop, w ∈ connectedExhaustion v n := by
  classical
  filter_upwards [Filter.eventually_ge_atTop w.1.length] with n hn
  exact ConnectedHull.subset_hull _ (Finset.mem_insert_of_mem
    ((mem_treeBallFinset d n w).mpr hn))

theorem eventually_subset_connectedExhaustion {d : ℕ} (v : TreeVertex d)
    (D : Finset (TreeVertex d)) :
    ∀ᶠ n in Filter.atTop, D ⊆ connectedExhaustion v n := by
  classical
  obtain ⟨N, hN⟩ := exists_subset_treeBallFinset D
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro w hw
  exact ConnectedHull.subset_hull _ (Finset.mem_insert_of_mem
    (monotone_treeBallFinset d hn (hN hw)))

theorem exists_connected_exhaustion {d : ℕ} (v : TreeVertex d) :
    ∃ D : ℕ → Finset (TreeVertex d), Monotone D ∧
      (∀ n, ConnectedFinset (D n) ∧ v ∈ D n) ∧
      ∀ w, ∃ n, w ∈ D n := by
  refine ⟨connectedExhaustion v, connectedExhaustion_monotone v,
    fun n => ⟨connectedExhaustion_connected v n, mem_connectedExhaustion v n⟩, ?_⟩
  intro w
  exact (eventually_mem_connectedExhaustion v w).exists

end Problem367

end

end OAI
