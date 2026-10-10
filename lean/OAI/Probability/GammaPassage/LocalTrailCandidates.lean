import OAI.Probability.GammaPassage.CheapPathCounting
import OAI.Probability.GammaPassage.LoopErasure
import OAI.Probability.FirstPassage.CoordinateTails
import Lean.Elab.Tactic.Omega

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP

/-- A path with unit edge weights has cost equal to its number of steps. -/
lemma pathCost_one_eq_length (p : Vertex) (ds : List Step) :
    pathCost (fun _ : Edge => (1 : ℝ)) p ds = (ds.length : ℝ) := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih =>
      simp [pathCost, ih, Nat.cast_add, Nat.cast_one, add_comm]

/-- The coordinate path has length equal to the lattice distance. -/
private lemma coordinatePath_length (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

/-- Loop erasure at unit weights produces a trail of at most the lattice distance. -/
lemma exists_short_trail (p q : Vertex) :
    ∃ ds : List Step, p + displacement ds = q ∧
      ((trace p ds).map traversalEdge).Nodup ∧ ds.length ≤ latticeDistance p q := by
  obtain ⟨ds, he, hn, hc⟩ := LoopErase.erase_path_loops
    (fun _ : Edge => (1 : ℝ)) (fun _ => zero_le_one) p (coordinatePath p q)
  have hend : p + displacement ds = q := by
    rw [he, coordinatePath_endpoint]
  rw [pathCost_one_eq_length, pathCost_one_eq_length, coordinatePath_length] at hc
  have hlen : ds.length ≤ latticeDistance p q := by exact_mod_cast hc
  exact ⟨ds, hend, hn, hlen⟩

/-- Trails with fewer than `R` steps connecting the specified endpoints. -/
noncomputable def candidates (p q : Vertex) (R : ℕ) : Finset (List Step) := by
  classical
  exact ((Finset.range R).biUnion (fixedTrailLists p)).filter
    (fun ds => p + displacement ds = q)

lemma mem_candidates (p q : Vertex) (R : ℕ) (ds : List Step) :
    ds ∈ candidates p q R ↔ p + displacement ds = q ∧
      ((trace p ds).map traversalEdge).Nodup ∧ ds.length < R := by
  classical
  constructor
  · intro h
    obtain ⟨hunion, hend⟩ := Finset.mem_filter.mp h
    obtain ⟨n, hn, htrail⟩ := Finset.mem_biUnion.mp hunion
    obtain ⟨hlen, hnodup⟩ := (mem_fixedTrailLists p n ds).mp htrail
    refine ⟨hend, hnodup, ?_⟩
    simpa only [hlen] using (Finset.mem_range.mp hn)
  · rintro ⟨hend, hnodup, hlen⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hend⟩
    exact Finset.mem_biUnion.mpr ⟨ds.length, Finset.mem_range.mpr hlen,
      (mem_fixedTrailLists p ds.length ds).mpr ⟨rfl, hnodup⟩⟩

lemma candidates_nonempty (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) : (candidates p q R).Nonempty := by
  obtain ⟨ds, hend, hnodup, hlen⟩ := exists_short_trail p q
  exact ⟨ds, (mem_candidates p q R ds).mpr ⟨hend, hnodup, hlen.trans_lt hR⟩⟩

end GammaFPP.FiniteLocal

end OAI
