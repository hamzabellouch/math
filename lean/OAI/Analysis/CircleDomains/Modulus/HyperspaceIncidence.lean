import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Maps.Proper.Basic

namespace OAI

/-!
# Closed continuum incidences in compact level graphs

The compatibility condition quantifies over subcontinua of a finite
level union. The hyperspace of nonempty compact sets is compact, and
connectedness, point membership and containment in a closed level graph
are closed conditions. Projection therefore preserves closedness for
continuum incidences with a fixed positive size witness.
-/

open Set TopologicalSpace Metric

namespace CircleDomainRigidity

theorem isClosed_connected_nonemptyCompacts {X : Type*} [MetricSpace X] :
    IsClosed {K : NonemptyCompacts X | IsConnected (K : Set X)} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro K hK
  have hn : ¬ IsPreconnected (K : Set X) := fun h => hK ⟨K.nonempty, h⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed K.isCompact.isClosed] at hn
  push Not at hn
  obtain ⟨A, B, hA, hB, hcover, hdisj, hnA, hnB⟩ := hn
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hA hB hdisj
  have hKU : ((K : Set X) ∩ U).Nonempty := by
    obtain ⟨x, hx, hxB⟩ := not_subset.mp hnB
    exact ⟨x, hx, hAU ((hcover hx).resolve_right hxB)⟩
  have hKV : ((K : Set X) ∩ V).Nonempty := by
    obtain ⟨x, hx, hxA⟩ := not_subset.mp hnA
    exact ⟨x, hx, hBV ((hcover hx).resolve_left hxA)⟩
  let N : Set (NonemptyCompacts X) :=
    {L | (L : Set X) ⊆ U ∪ V} ∩
      ({L | ((L : Set X) ∩ U).Nonempty} ∩ {L | ((L : Set X) ∩ V).Nonempty})
  refine ⟨N, ?_, ?_, ?_⟩
  · intro L hL hconn
    obtain ⟨x, _, hxU, hxV⟩ := hconn.isPreconnected U V hU hV hL.1 hL.2.1 hL.2.2
    exact Set.disjoint_left.mp hUV hxU hxV
  · exact (NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).inter
      ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).inter
        (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV))
  · exact ⟨hcover.trans (union_subset_union hAU hBV), hKU, hKV⟩

theorem isClosed_nonemptyCompacts_membership {X : Type*} [MetricSpace X] :
    IsClosed {p : X × NonemptyCompacts X | p.1 ∈ (p.2 : Set X)} := by
  have heq : {p : X × NonemptyCompacts X | p.1 ∈ (p.2 : Set X)} =
      {p | infDist p.1 (p.2 : Set X) = 0} := by
    ext p
    exact p.2.isCompact.isClosed.mem_iff_infDist_zero p.2.nonempty
  rw [heq]
  exact isClosed_eq NonemptyCompacts.lipschitz_infDist.continuous continuous_const

theorem isClosed_compact_subset_graph
    {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {R : Set (X × T)} (hR : IsClosed R) :
    IsClosed {p : NonemptyCompacts X × T | ∀ x ∈ (p.1 : Set X), (x, p.2) ∈ R} := by
  let F : NonemptyCompacts X × T → Compacts (X × T) :=
    fun p => p.1.toCompacts ×ˢ ({p.2} : Compacts T)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have heq : {p : NonemptyCompacts X × T | ∀ x ∈ (p.1 : Set X), (x, p.2) ∈ R} =
      F ⁻¹' {K : Compacts (X × T) | (K : Set (X × T)) ⊆ R} := by
    ext p
    constructor
    · intro h
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      have ht' : t = p.2 := ht
      subst t
      exact h x hx
    · intro h x hx
      exact h ⟨hx, rfl⟩
  rw [heq]
  exact (Compacts.isClosed_subsets_of_isClosed hR).preimage hF

def positiveContinuumIncidence {X T : Type*} [PseudoMetricSpace X]
    (R : Set (X × T)) (ε : ℝ) : Set (X × T) :=
  {p | ∃ K : NonemptyCompacts X, IsConnected (K : Set X) ∧ p.1 ∈ (K : Set X) ∧
    (∀ x ∈ (K : Set X), (x, p.2) ∈ R) ∧
      ∃ u ∈ (K : Set X), ∃ v ∈ (K : Set X), ε ≤ dist u v}

/-- The compact hyperspace witnesses make each positive-size continuum
incidence a closed relation in the point and level parameters. -/
theorem isClosed_positiveContinuumIncidence
    {X T : Type*} [MetricSpace X] [CompactSpace X] [TopologicalSpace T]
    {R : Set (X × T)} (hR : IsClosed R) (ε : ℝ) :
    IsClosed (positiveContinuumIncidence R ε) := by
  let F : Set ((X × T) × (NonemptyCompacts X × (X × X))) :=
    {p | IsConnected (p.2.1 : Set X) ∧ p.1.1 ∈ (p.2.1 : Set X) ∧
      (∀ x ∈ (p.2.1 : Set X), (x, p.1.2) ∈ R) ∧
        p.2.2.1 ∈ (p.2.1 : Set X) ∧ p.2.2.2 ∈ (p.2.1 : Set X) ∧
          ε ≤ dist p.2.2.1 p.2.2.2}
  have hF : IsClosed F :=
    (isClosed_connected_nonemptyCompacts.preimage continuous_snd.fst).inter
      ((isClosed_nonemptyCompacts_membership.preimage
        (continuous_fst.fst.prodMk continuous_snd.fst)).inter
      ((isClosed_compact_subset_graph hR |>.preimage
        (continuous_snd.fst.prodMk continuous_fst.snd)).inter
      ((isClosed_nonemptyCompacts_membership.preimage
        (continuous_snd.snd.fst.prodMk continuous_snd.fst)).inter
      ((isClosed_nonemptyCompacts_membership.preimage
        (continuous_snd.snd.snd.prodMk continuous_snd.fst)).inter
      (isClosed_le continuous_const (continuous_snd.snd.fst.dist continuous_snd.snd.snd))))))
  have heq : positiveContinuumIncidence R ε = Prod.fst '' F := by
    ext p
    constructor
    · rintro ⟨K, hK, hx, hsub, u, hu, v, hv, hdist⟩
      exact ⟨(p, (K, (u, v))), ⟨hK, hx, hsub, hu, hv, hdist⟩, rfl⟩
    · rintro ⟨⟨p, K, u, v⟩, hp, rfl⟩
      exact ⟨K, hp.1, hp.2.1, hp.2.2.1, u, hp.2.2.2.1, v,
        hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace F hF

def nontrivialFiberComponentRelation {X T : Type*} [TopologicalSpace X]
    (R : Set (X × T)) : Set (X × T) :=
  {p | (connectedComponentIn {x | (x, p.2) ∈ R} p.1).Nontrivial}

private theorem isClosed_connectedComponentIn_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (x : X) :
    IsClosed (connectedComponentIn A x) := by
  by_cases hx : x ∈ A
  · rw [connectedComponentIn_eq_image hx]
    exact hA.isClosedMap_subtype_val _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

theorem nontrivialFiberComponentRelation_eq_iUnion
    {X T : Type*} [MetricSpace X] [CompactSpace X] [TopologicalSpace T]
    {R : Set (X × T)} (hR : IsClosed R) :
    nontrivialFiberComponentRelation R =
      ⋃ n : ℕ, positiveContinuumIncidence R (1 / ((n : ℝ) + 1)) := by
  ext p
  constructor
  · intro hp
    let A : Set X := {x | (x, p.2) ∈ R}
    change (connectedComponentIn A p.1).Nontrivial at hp
    have hx : p.1 ∈ A := by
      by_contra hx
      have he := connectedComponentIn_eq_empty hx
      exact Set.not_nontrivial_empty (he ▸ hp)
    have hA : IsClosed A := hR.preimage (continuous_id.prodMk continuous_const)
    let K : NonemptyCompacts X :=
      ⟨⟨connectedComponentIn A p.1,
        (isClosed_connectedComponentIn_of_isClosed hA p.1).isCompact⟩,
        ⟨p.1, mem_connectedComponentIn hx⟩⟩
    obtain ⟨u, hu, v, hv, huv⟩ := hp
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr huv)
    refine mem_iUnion.mpr ⟨n, K, isConnected_connectedComponentIn_iff.mpr hx,
      mem_connectedComponentIn hx, ?_, u, hu, v, hv, hn.le⟩
    exact fun _ hy => connectedComponentIn_subset A p.1 hy
  · intro hp
    obtain ⟨n, K, hK, hx, hsub, u, hu, v, hv, hdist⟩ := mem_iUnion.mp hp
    have hKsub := hK.isPreconnected.subset_connectedComponentIn hx hsub
    refine ⟨u, hKsub hu, v, hKsub hv, ?_⟩
    intro he
    have hpositive : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hzero : 0 < (0 : ℝ) := by simpa only [he, dist_self] using hpositive.trans_le hdist
    exact lt_irrefl 0 hzero

/-- The relation “the point belongs to a nondegenerate component of
the compact level fiber” is Fσ, hence Borel. -/
theorem measurableSet_nontrivialFiberComponentRelation
    {X T : Type*} [MetricSpace X] [CompactSpace X] [TopologicalSpace T]
    [MeasurableSpace (X × T)] [BorelSpace (X × T)]
    {R : Set (X × T)} (hR : IsClosed R) :
    MeasurableSet (nontrivialFiberComponentRelation R) := by
  rw [nontrivialFiberComponentRelation_eq_iUnion hR]
  exact MeasurableSet.iUnion (fun n =>
    (isClosed_positiveContinuumIncidence hR (1 / ((n : ℝ) + 1))).measurableSet)

end CircleDomainRigidity

end OAI
