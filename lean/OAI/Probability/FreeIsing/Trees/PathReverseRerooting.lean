import OAI.Probability.FreeIsing.Trees.PathRerooting
import OAI.Probability.FreeIsing.Trees.WordCancellation

namespace OAI

noncomputable section

namespace Problem367

open ConnectedHull

namespace TreeKoopman

theorem wordAut_reverse_apply_prefix {d : ℕ} (v : TreeVertex d) (k : ℕ) :
    (wordAut v.1.reverse).toEquiv (takeVertex v k) =
      takeVertex (reverseVertex v) (v.1.length - k) := by
  have h := wordAut_apply_reverse_prefix (reverseVertex v) k
  rw [reverseVertex_twice] at h
  simpa only [reverseVertex, List.length_reverse] using h

end TreeKoopman

theorem exists_treeAut_reverse_subsegment {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      ∀ k : ℕ, i ≤ k → k ≤ j + 1 →
        g.toEquiv (takeVertex v k) = takeVertex w (j + 1 - k) := by
  obtain ⟨u, g, hlen, hmap⟩ := exists_treeAut_reroot_subsegment v hij hj
  let w := TreeKoopman.reverseVertex u
  let h := TreeKoopman.wordAut u.1.reverse
  refine ⟨w, g.trans h, ?_, ?_⟩
  · simpa only [w, TreeKoopman.reverseVertex, List.length_reverse] using hlen
  · intro k hik hkj
    change h.toEquiv (g.toEquiv (takeVertex v k)) = _
    rw [hmap k hik hkj]
    change (TreeKoopman.wordAut u.1.reverse).toEquiv (takeVertex u (k - i)) = _
    rw [TreeKoopman.wordAut_reverse_apply_prefix]
    have hindex : u.1.length - (k - i) = j + 1 - k := by omega
    rw [hindex]

theorem exists_treeAut_reroot_reverse_edge_pair {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      g.toEquiv (takeVertex v (j + 1)) = root d ∧
      g.toEquiv (takeVertex v j) = takeVertex w 1 ∧
      g.toEquiv (takeVertex v (i + 1)) = takeVertex w (j - i) ∧
      g.toEquiv (takeVertex v i) = w := by
  obtain ⟨w, g, hlen, hmap⟩ := exists_treeAut_reverse_subsegment v hij hj
  refine ⟨w, g, hlen, ?_, ?_, ?_, ?_⟩
  · simpa using hmap (j + 1) (by omega) le_rfl
  · simpa using hmap j hij (by omega)
  · have h := hmap (i + 1) (by omega) (by omega)
    have hindex : j + 1 - (i + 1) = j - i := by omega
    simpa only [hindex] using h
  · have h := hmap i le_rfl (by omega)
    have hindex : j + 1 - i = w.1.length := by omega
    rw [hindex, prefix_length] at h
    exact h

end Problem367

end

end OAI
