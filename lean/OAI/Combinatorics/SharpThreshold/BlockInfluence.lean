import OAI.Combinatorics.SharpThreshold.BlockSymmetry
import OAI.Combinatorics.SharpThreshold.InfluenceReindex
import OAI.Combinatorics.SharpThreshold.BlockRestrictionSymmetry
import OAI.Combinatorics.SharpThreshold.Permutation
import OAI.Combinatorics.SharpThreshold.BlockOrbitSubtype

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Pivotal influences of a conditioned function are invariant under every
coordinate permutation that preserves the free set and fixes its complement. -/
theorem restrictCube_influence_reindex {α : Type u} [Fintype α]
    (P : α → Prop) [DecidablePred P]
    (π : Equiv.Perm α) (hP : ∀ i, P i ↔ P (π i))
    (hfix : ∀ i, ¬ P i → π i = i) (f : (α → Bool) → Bool)
    (hf : ∀ z, f (fun i => z (π.symm i)) = f z)
    (p : ℝ) (y : {i // ¬ P i} → Bool) (i : {i // P i}) :
    Reindex.influence p (restrictCube P f y) ((π.subtypeEquiv hP) i) =
      Reindex.influence p (restrictCube P f y) i := by
  apply Reindex.influence_config (π.subtypeEquiv hP)
  intro x
  exact restrictCube_invariant P π hP hfix f hf x y

/-- Conditional edge influences respect vertex permutations supported on the block. -/
theorem restrictCube_influence_permEdge {n : ℕ}
    (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (π : Equiv.Perm (Fin n)) (hπ : SupportedOnBlock B π)
    (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p : ℝ) (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool)
    (e : {e : GraphEdge n // EdgeTouches B e}) :
    Reindex.influence p (restrictCube (EdgeTouches B) f y)
        ⟨permEdge π e.val, (edgeTouches_permEdge_iff hπ e.val).mpr e.property⟩ =
      Reindex.influence p (restrictCube (EdgeTouches B) f y) e := by
  let hP : ∀ i, EdgeTouches B i ↔ EdgeTouches B ((permEdgeEquiv π) i) :=
    fun i => (edgeTouches_permEdge_iff hπ i).symm
  exact restrictCube_influence_reindex (EdgeTouches B) (permEdgeEquiv π) hP
    (fun i hi => permEdge_eq_self_of_not_touches hπ i hi) f (hf π) p y e

/-- Quantitative conditional influence bound from a finite collection of edges in
one block orbit.  The collection may be supplied on the original edge type. -/
theorem restrictCube_influence_le_of_orbit {n : ℕ}
    (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool)
    (e : {e : GraphEdge n // EdgeTouches B e}) (S : Finset (GraphEdge n))
    {m : ℝ} (hm : 0 < m) (hcard : m ≤ (S.card : ℝ))
    (horbit : ∀ d ∈ S, ∃ π : Equiv.Perm (Fin n),
      SupportedOnBlock B π ∧ permEdge π e.val = d) :
    Reindex.influence p (restrictCube (EdgeTouches B) f y) e ≤
      (∑ d, Reindex.influence p (restrictCube (EdgeTouches B) f y) d) / m := by
  classical
  have htouch : ∀ d ∈ S, EdgeTouches B d := by
    intro d hd
    obtain ⟨π, hπ, hmap⟩ := horbit d hd
    rw [← hmap]
    exact (edgeTouches_permEdge_iff hπ e.val).mpr e.property
  have hcard' : m ≤ ((S.subtype (EdgeTouches B)).card : ℝ) := by
    simpa only [Finset.card_subtype, Finset.filter_true_of_mem htouch] using hcard
  apply Reindex.influence_le_total_div hp0 hp1 _ e
    (S.subtype (EdgeTouches B)) hm hcard'
  intro d hd
  obtain ⟨π, hπ, hmap⟩ := horbit d.val (Finset.mem_subtype.mp hd)
  simpa only [hmap] using restrictCube_influence_permEdge B π hπ f hf p y e

/-- Every conditional influence on edges touching a block is at most the total
conditional influence divided by the number of block vertices. -/
theorem block_restricted_influence_le {n : ℕ}
    (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)] (hB : 3 ≤ B.card)
    (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (y : {e : GraphEdge n // ¬ EdgeTouches B e} → Bool)
    (e : {e : GraphEdge n // EdgeTouches B e}) :
    Reindex.influence p (restrictCube (EdgeTouches B) f y) e ≤
      (∑ d, Reindex.influence p (restrictCube (EdgeTouches B) f y) d) /
        (B.card : ℝ) := by
  classical
  obtain ⟨S, hcard, horbit⟩ := exists_freeEdge_orbit_family B hB e
  have hm : (0 : ℝ) < B.card := by exact_mod_cast (by omega : 0 < B.card)
  apply Reindex.influence_le_total_div hp0 hp1 _ e S hm (by exact_mod_cast hcard)
  intro d hd
  obtain ⟨π, hπ, hmap⟩ := horbit d hd
  simpa only [hmap] using restrictCube_influence_permEdge B π hπ f hf p y e

end Problem313

end

end OAI
