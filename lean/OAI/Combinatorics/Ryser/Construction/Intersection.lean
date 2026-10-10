import OAI.Combinatorics.Ryser.Construction.LabelAction
import OAI.Combinatorics.Ryser.Geometry.AffineJoins

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

private theorem exists_equal_projection {K : Type*} [Field K] [DecidableEq K]
    (p q : Point K) : ∃ d : Direction K, projection d p = projection d q := by
  refine ⟨(joinLine p q).1, ?_⟩
  have hp : projection (joinLine p q).1 p = (joinLine p q).2 :=
    incidence_joinLine_left p q
  have hq : projection (joinLine p q).1 q = (joinLine p q).2 :=
    incidence_joinLine_right p q
  exact hp.trans hq.symm

theorem ordinaryEdge_inter_ordinaryEdge (data : ConfigurationData k F G)
    (x y : Point F) : (ordinaryEdge data x ∩ ordinaryEdge data y).Nonempty := by
  refine ⟨ordinaryVertex data (joinLine x y), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact (ordinaryVertex_mem_ordinaryEdge_iff data x _).2
      (incidence_joinLine_left x y)
  · exact (ordinaryVertex_mem_ordinaryEdge_iff data y _).2
      (incidence_joinLine_right x y)

theorem exceptionalEdge_inter_of_projection_eq (data : ConfigurationData k F G)
    (i j : G) (w z : Point k) (d : Direction F)
    (hi : d ∉ data.altered i) (hj : d ∉ data.altered j)
    (heq : projection d (data.base i w) = projection d (data.base j z)) :
    (exceptionalEdge data i w ∩ exceptionalEdge data j z).Nonempty := by
  refine ⟨ordinaryVertex data (lineThrough d (data.base i w)),
    Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact (ordinaryVertex_mem_exceptionalEdge_iff data i w _).2 ⟨hi, rfl⟩
  · exact (ordinaryVertex_mem_exceptionalEdge_iff data j z _).2 ⟨hj, heq.symm⟩

theorem ordinaryEdge_inter_exceptionalEdge (data : ConfigurationData k F G)
    (x : Point F) (i : G) (w : Point k)
    (havoid : ∀ d ∈ data.altered i,
      projection d x ≠ projection d (data.base i w)) :
    (ordinaryEdge data x ∩ exceptionalEdge data i w).Nonempty := by
  obtain ⟨d, hd⟩ := exists_equal_projection x (data.base i w)
  have hnot : d ∉ data.altered i := fun hm => havoid d hm hd
  refine ⟨ordinaryVertex data (lineThrough d x), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact ordinaryVertex_mem_ordinaryEdge data x d
  · exact (ordinaryVertex_mem_exceptionalEdge_iff data i w _).2 ⟨hnot, hd.symm⟩

theorem exceptionalEdge_inter_of_separated (data : ConfigurationData k F G)
    (i j : G) (w z : Point k)
    (hi : ∀ d ∈ data.altered i,
      projection d (data.base i w) ≠ projection d (data.base j z))
    (hj : ∀ d ∈ data.altered j,
      projection d (data.base j z) ≠ projection d (data.base i w)) :
    (exceptionalEdge data i w ∩ exceptionalEdge data j z).Nonempty := by
  obtain ⟨d, hd⟩ := exists_equal_projection (data.base i w) (data.base j z)
  exact exceptionalEdge_inter_of_projection_eq data i j w z d
    (fun hm => hi d hm hd) (fun hm => hj d hm hd.symm) hd

theorem exceptionalEdge_inter_sameGroup (data : ConfigurationData k F G) (i : G)
    (directions : Direction k → Direction F)
    (hmem : ∀ t : k, t ≠ 0 → directions (some t) ∈ data.altered i)
    (hinverse : ∀ (t : k) (ht : t ≠ 0),
      data.inverseSlope i ⟨directions (some t), hmem t ht⟩ = t)
    (haxisOutside : ∀ a : Direction k, a = none ∨ a = some 0 →
      directions a ∉ data.altered i)
    (haxisTransport : ∀ a : Direction k, a = none ∨ a = some 0 →
      ∀ p q : Point k,
        projection a (data.transform p) = projection a (data.transform q) →
        projection (directions a) (data.base i p) =
          projection (directions a) (data.base i q))
    (w z : Point k) :
    (exceptionalEdge data i w ∩ exceptionalEdge data i z).Nonempty := by
  obtain ⟨a, ha⟩ := exists_equal_projection (data.transform w) (data.transform z)
  cases a with
  | none =>
      exact exceptionalEdge_inter_of_projection_eq data i i w z (directions none)
        (haxisOutside none (Or.inl rfl)) (haxisOutside none (Or.inl rfl))
        (haxisTransport none (Or.inl rfl) w z ha)
  | some t =>
      by_cases ht : t = 0
      · subst t
        exact exceptionalEdge_inter_of_projection_eq data i i w z (directions (some 0))
          (haxisOutside (some 0) (Or.inr rfl))
          (haxisOutside (some 0) (Or.inr rfl))
          (haxisTransport (some 0) (Or.inr rfl) w z ha)
      · let d : {d : Direction F // d ∈ data.altered i} :=
          ⟨directions (some t), hmem t ht⟩
        have hinv : data.inverseSlope i d = t := hinverse t ht
        let c := projection (some (data.inverseSlope i d)) (data.transform w)
        refine ⟨specialVertex data i d c, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · exact (specialVertex_mem_exceptionalEdge_iff data i w d c).2 rfl
        · apply (specialVertex_mem_exceptionalEdge_iff data i z d c).2
          change projection (some (data.inverseSlope i d)) (data.transform z) =
            projection (some (data.inverseSlope i d)) (data.transform w)
          rw [hinv]
          exact ha.symm

theorem ordinaryEdge_injective (data : ConfigurationData k F G) :
    Function.Injective (ordinaryEdge data) := by
  intro x y hxy
  have hproj (d : Direction F) : projection d x = projection d y := by
    have hv : ordinaryVertex data (lineThrough d x) ∈ ordinaryEdge data y := by
      rw [← hxy]
      exact ordinaryVertex_mem_ordinaryEdge data x d
    exact ((ordinaryVertex_mem_ordinaryEdge_iff data y _).1 hv).symm
  exact point_eq_of_projection_axes (hproj none) (hproj (some 0))

theorem exceptionalEdge_injective (data : ConfigurationData k F G) (i : G)
    (htransform : Function.Injective data.transform)
    (d e : {d : Direction F // d ∈ data.altered i})
    (hde : data.inverseSlope i d ≠ data.inverseSlope i e) :
    Function.Injective (exceptionalEdge data i) := by
  intro w z hwz
  have hproj (a : {d : Direction F // d ∈ data.altered i}) :
      projection (some (data.inverseSlope i a)) (data.transform w) =
        projection (some (data.inverseSlope i a)) (data.transform z) := by
    let c := projection (some (data.inverseSlope i a)) (data.transform w)
    have hv : specialVertex data i a c ∈ exceptionalEdge data i z := by
      rw [← hwz]
      exact (specialVertex_mem_exceptionalEdge_iff data i w a c).2 rfl
    exact ((specialVertex_mem_exceptionalEdge_iff data i z a c).1 hv).symm
  apply htransform
  exact point_eq_of_projection_eq_of_ne_direction
    (fun h => hde (Option.some.inj h)) (hproj d) (hproj e)

theorem ordinaryEdge_ne_exceptionalEdge (data : ConfigurationData k F G)
    (x : Point F) (i : G) (w : Point k) (hi : (data.altered i).Nonempty) :
    ordinaryEdge data x ≠ exceptionalEdge data i w := by
  obtain ⟨d, hd⟩ := hi
  let a : {d : Direction F // d ∈ data.altered i} := ⟨d, hd⟩
  let c := projection (some (data.inverseSlope i a)) (data.transform w)
  intro heq
  apply specialVertex_notMem_ordinaryEdge data i a c x
  rw [heq]
  exact (specialVertex_mem_exceptionalEdge_iff data i w a c).2 rfl

theorem exceptionalEdge_ne_of_group_ne (data : ConfigurationData k F G)
    (i j : G) (hij : i ≠ j) (w z : Point k) (hi : (data.altered i).Nonempty) :
    exceptionalEdge data i w ≠ exceptionalEdge data j z := by
  obtain ⟨d, hd⟩ := hi
  let a : {d : Direction F // d ∈ data.altered i} := ⟨d, hd⟩
  let c := projection (some (data.inverseSlope i a)) (data.transform w)
  intro heq
  apply specialVertex_notMem_exceptionalEdge_of_ne data i j hij z a c
  rw [← heq]
  exact (specialVertex_mem_exceptionalEdge_iff data i w a c).2 rfl

variable [Fintype G]

theorem hypergraph_intersecting_of_geometric_data (data : ConfigurationData k F G)
    (directions : G → Direction k → Direction F)
    (hmem : ∀ (i : G) (t : k), t ≠ 0 → directions i (some t) ∈ data.altered i)
    (hinverse : ∀ (i : G) (t : k) (ht : t ≠ 0),
      data.inverseSlope i ⟨directions i (some t), hmem i t ht⟩ = t)
    (haxisOutside : ∀ (i : G) (a : Direction k), a = none ∨ a = some 0 →
      directions i a ∉ data.altered i)
    (haxisTransport : ∀ (i : G) (a : Direction k), a = none ∨ a = some 0 →
      ∀ p q : Point k,
        projection a (data.transform p) = projection a (data.transform q) →
        projection (directions i a) (data.base i p) =
          projection (directions i a) (data.base i q))
    (havoid : ∀ x ∈ data.ordinaryPoints, ∀ i, ∀ w ∈ data.retained,
      ∀ d ∈ data.altered i, projection d x ≠ projection d (data.base i w))
    (hseparate : ∀ i j : G, i ≠ j → ∀ w ∈ data.retained, ∀ z ∈ data.retained,
      ∀ d ∈ data.altered i,
        projection d (data.base i w) ≠ projection d (data.base j z)) :
    Intersecting (hypergraph data) := by
  intro e he f hf _
  rcases (mem_hypergraph data e).mp he with ⟨x, hx, rfl⟩ | ⟨i, w, hw, rfl⟩
  · rcases (mem_hypergraph data f).mp hf with ⟨y, _, rfl⟩ | ⟨j, z, hz, rfl⟩
    · exact ordinaryEdge_inter_ordinaryEdge data x y
    · exact ordinaryEdge_inter_exceptionalEdge data x j z (havoid x hx j z hz)
  · rcases (mem_hypergraph data f).mp hf with ⟨y, hy, rfl⟩ | ⟨j, z, hz, rfl⟩
    · simpa only [Finset.inter_comm] using
        ordinaryEdge_inter_exceptionalEdge data y i w (havoid y hy i w hw)
    · by_cases hij : i = j
      · subst j
        exact exceptionalEdge_inter_sameGroup data i (directions i) (hmem i)
          (hinverse i) (haxisOutside i) (haxisTransport i) w z
      · exact exceptionalEdge_inter_of_separated data i j w z
          (hseparate i j hij w hw z hz) (hseparate j i (fun h => hij h.symm) z hz w hw)

end RyserCoveringCounterexample.Construction

end OAI
