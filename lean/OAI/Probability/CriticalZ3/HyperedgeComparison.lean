import OAI.Probability.CriticalZ3.Resampling

namespace OAI

universe uE uI uV

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

/-- Full labelled hyperedges; allowing empty hyperedges causes no change to clusters. -/
abbrev Hypergraph (V : Type uV) (E : Type uE) := E → Set V

def Adj (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x y : V) : Prop :=
  ∃ e, ω e = true ∧ Disjoint (H e) D ∧ x ∈ H e ∧ y ∈ H e

def Connected (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x y : V) : Prop :=
  Relation.ReflTransGen (Adj H ω D) x y

def cluster (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) : Set V :=
  {y | Connected H ω D x y}

def clusters (H : Hypergraph V E) (ω : E → Bool) (D S : Set V) : Set V :=
  {y | ∃ x ∈ S, y ∈ cluster H ω D x}

def Meets (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) (T : Set V) : Prop :=
  ∃ y ∈ T, Connected H ω D x y

theorem adj_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Adj H ω D x y) : Adj H ω D y x := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd, hy, hx⟩

theorem connected_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Connected H ω D x y) : Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hxy ih => exact ih.head (adj_symm hxy)

theorem connected_refl (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) :
    Connected H ω D x x := .refl

theorem connected_trans {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y z : V}
    (hxy : Connected H ω D x y) (hyz : Connected H ω D y z) :
    Connected H ω D x z := hxy.trans hyz

theorem mem_cluster_self (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) :
    x ∈ cluster H ω D x := .refl

theorem adj_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') {x y : V} (h : Adj H ω D' x y) : Adj H ω D x y := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd.mono_right hDD, hx, hy⟩

theorem cluster_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') (x : V) : cluster H ω D' x ⊆ cluster H ω D x :=
  Relation.ReflTransGen.mono (fun _ _ => adj_mono_delete hDD) x

theorem clusters_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' S : Set V}
    (hDD : D ⊆ D') : clusters H ω D' S ⊆ clusters H ω D S := by
  rintro y ⟨x, hx, hy⟩
  exact ⟨x, hx, cluster_mono_delete hDD x hy⟩

theorem clusters_contains (H : Hypergraph V E) (ω : E → Bool) (D S : Set V) :
    S ⊆ clusters H ω D S := fun x hx => ⟨x, hx, .refl⟩

theorem cluster_closed {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {s x y : V}
    (hx : x ∈ cluster H ω D s) (hxy : Adj H ω D x y) : y ∈ cluster H ω D s :=
  hx.tail hxy

theorem clusters_closed {H : Hypergraph V E} {ω : E → Bool} {D S : Set V} {x y : V}
    (hx : x ∈ clusters H ω D S) (hxy : Adj H ω D x y) : y ∈ clusters H ω D S := by
  obtain ⟨s, hs, hx⟩ := hx
  exact ⟨s, hs, hx.tail hxy⟩

theorem cluster_avoids_deleted {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x : V}
    (hx : x ∉ D) : Disjoint (cluster H ω D x) D := by
  apply Set.disjoint_left.mpr
  intro y hy
  induction hy with
  | refl => exact hx
  | @tail z y _ hzy _ =>
    obtain ⟨e, _, hd, _, hy⟩ := hzy
    exact fun hyD => Set.disjoint_left.mp hd hy hyD

theorem clusters_avoids_deleted {H : Hypergraph V E} {ω : E → Bool} {D S : Set V}
    (hSD : Disjoint S D) : Disjoint (clusters H ω D S) D := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, hy⟩ hyD
  exact Set.disjoint_left.mp (cluster_avoids_deleted
    (fun hxD => Set.disjoint_left.mp hSD hx hxD)) hy hyD

/-- Disjointness of a full cluster from a tested set is also disjointness from its
entire union of clusters, the fact used in the first-listed-node partition. -/
theorem cluster_disjoint_clusters_iff {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {x : V} :
    Disjoint (cluster H ω D x) (clusters H ω D S) ↔
      Disjoint (cluster H ω D x) S := by
  constructor
  · exact fun h => h.mono_right (clusters_contains H ω D S)
  · intro h
    apply Set.disjoint_left.mpr
    rintro y hy ⟨s, hs, hsy⟩
    exact Set.disjoint_left.mp h (connected_trans hy (connected_symm hsy)) hs

/-- Deleting a union of clusters does not change any of the other clusters.
This is deterministic, before any product-law conditioning. -/
theorem cluster_delete_clusters {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {x : V} (hx : x ∉ clusters H ω D S) :
    cluster H ω (D ∪ clusters H ω D S) x = cluster H ω D x := by
  apply Set.Subset.antisymm (cluster_mono_delete Set.subset_union_left x)
  intro y hy
  have hall : ∀ z ∈ cluster H ω D x, z ∉ clusters H ω D S := by
    rintro z hz ⟨s, hs, hsz⟩
    exact hx ⟨s, hs, connected_trans hsz (connected_symm hz)⟩
  induction hy with
  | refl => exact .refl
  | @tail z y hxz hzy ih =>
    apply ih.tail
    obtain ⟨e, he, hd, hz, hy⟩ := hzy
    refine ⟨e, he, Disjoint.union_right hd ?_, hz, hy⟩
    apply Set.disjoint_left.mpr
    intro a ha hbad
    exact hall z hxz (clusters_closed hbad ⟨e, he, hd, ha, hz⟩)

/-- Changing bits on hyperedges disjoint from C(S) cannot change C(S).
This is the key measurability assertion required for exact-cluster conditioning. -/
theorem clusters_eq_of_agree_incident {H : Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V}
    (hagree : ∀ e, ¬ Disjoint (H e) (clusters H ω D S) → ω' e = ω e) :
    clusters H ω' D S = clusters H ω D S := by
  have hnew : clusters H ω' D S ⊆ clusters H ω D S := by
    rintro y ⟨x, hx, hy⟩
    have hr : ∀ z, Connected H ω' D x z → Connected H ω D x z := by
      intro z hz
      induction hz with
      | refl => exact .refl
      | @tail a b _ hab ia =>
        obtain ⟨e, he, hd, ha, hb⟩ := hab
        have hi : ¬ Disjoint (H e) (clusters H ω D S) := by
          intro h
          exact Set.disjoint_left.mp h ha ⟨x, hx, ia⟩
        exact ia.tail ⟨e, (hagree e hi) ▸ he, hd, ha, hb⟩
    exact ⟨x, hx, hr y hy⟩
  apply Set.Subset.antisymm hnew
  rintro y ⟨x, hx, hy⟩
  have hr : ∀ z, Connected H ω D x z → Connected H ω' D x z := by
    intro z hz
    induction hz with
    | refl => exact .refl
    | @tail a b hxa hab ia =>
      obtain ⟨e, he, hd, ha, hb⟩ := hab
      have hi : ¬ Disjoint (H e) (clusters H ω D S) := by
        intro h
        exact Set.disjoint_left.mp h ha ⟨x, hx, hxa⟩
      exact ia.tail ⟨e, (hagree e hi).trans he, hd, ha, hb⟩
  exact ⟨x, hx, hr y hy⟩

def ClusterDomain (s : V) (S : Set V) : Set (Set V) :=
  {U | s ∈ U ∧ Disjoint U S}

noncomputable def residualSample (H : Hypergraph V E) (ω : E → Bool)
    (s : V) (S U : Set V) (F : Set V → ℝ) : ℝ := by
  classical
  exact if s ∈ clusters H ω U S then 0 else
    F (cluster H ω (clusters H ω U S) s) -
    F (cluster H ω (clusters H ω U S ∪ U) s)

theorem residual_cluster_mem_domain {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U : Set V} (hs : s ∉ clusters H ω U S) :
    cluster H ω (clusters H ω U S) s ∈ ClusterDomain s S := by
  refine ⟨.refl, (cluster_avoids_deleted hs).mono_right ?_⟩
  exact clusters_contains H ω U S

theorem residual_cluster_union_mem_domain {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U : Set V} (hs : s ∉ clusters H ω U S) (hsU : s ∉ U) :
    cluster H ω (clusters H ω U S ∪ U) s ∈ ClusterDomain s S := by
  refine ⟨.refl, (cluster_avoids_deleted (fun h => h.elim hs hsU)).mono_right ?_⟩
  exact (clusters_contains H ω U S).trans Set.subset_union_left

theorem residualSample_nonneg {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U : Set V} {F : Set V → ℝ} (hsU : s ∉ U)
    (hF : MonotoneOn F (ClusterDomain s S)) :
    0 ≤ residualSample H ω s S U F := by
  classical
  unfold residualSample
  split_ifs with hs
  · exact le_rfl
  · exact sub_nonneg.mpr (hF (residual_cluster_union_mem_domain hs hsU)
      (residual_cluster_mem_domain hs) (cluster_mono_delete Set.subset_union_left s))

theorem residualSample_mono {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U U' : Set V} {F : Set V → ℝ}
    (hUU : U ⊆ U') (hsU' : s ∉ U') (hF : MonotoneOn F (ClusterDomain s S)) :
    residualSample H ω s S U F ≤ residualSample H ω s S U' F := by
  classical
  have hsU : s ∉ U := fun hs => hsU' (hUU hs)
  by_cases hs : s ∈ clusters H ω U S
  · rw [residualSample, ite_eq_left hs]
    exact residualSample_nonneg hsU' hF
  · have hs' : s ∉ clusters H ω U' S :=
      fun h => hs (clusters_mono_delete hUU h)
    have hfirst : F (cluster H ω (clusters H ω U S) s) ≤
        F (cluster H ω (clusters H ω U' S) s) :=
      hF (residual_cluster_mem_domain hs) (residual_cluster_mem_domain hs')
        (cluster_mono_delete (clusters_mono_delete hUU) s)
    have heq : cluster H ω (clusters H ω U S ∪ U) s = cluster H ω U s := by
      rw [Set.union_comm]
      exact cluster_delete_clusters hs
    have heq' : cluster H ω (clusters H ω U' S ∪ U') s = cluster H ω U' s := by
      rw [Set.union_comm]
      exact cluster_delete_clusters hs'
    have hsecond : F (cluster H ω (clusters H ω U' S ∪ U') s) ≤
        F (cluster H ω (clusters H ω U S ∪ U) s) := by
      apply hF (residual_cluster_union_mem_domain hs' hsU')
        (residual_cluster_union_mem_domain hs hsU)
      rw [heq, heq']
      exact cluster_mono_delete hUU s
    simp only [residualSample, ite_eq_right hs, ite_eq_right hs']
    exact sub_le_sub hfirst hsecond

/-- Bits on deleted hyperedges are irrelevant to the surviving clusters. -/
theorem cluster_eq_of_agree_disjoint {H : Hypergraph V E} {ω ω' : E → Bool}
    {D : Set V} (hagree : ∀ e, Disjoint (H e) D → ω' e = ω e) (s : V) :
    cluster H ω' D s = cluster H ω D s := by
  have hrel : Adj H ω' D = Adj H ω D := by
    funext x y
    apply propext
    constructor <;> rintro ⟨e, he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd) ▸ he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd).trans he, hd, hx, hy⟩
  unfold cluster Connected
  rw [hrel]

theorem clusters_eq_of_agree_disjoint {H : Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V} (hagree : ∀ e, Disjoint (H e) D → ω' e = ω e) :
    clusters H ω' D S = clusters H ω D S := by
  unfold clusters
  simp only [cluster_eq_of_agree_disjoint hagree]

theorem clusters_singleton (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (s : V) :
    clusters H ω D {s} = cluster H ω D s := by
  ext y
  simp [clusters]

/-- Deleting a cluster does not change the union of any disjoint clusters. -/
theorem clusters_delete_cluster {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {s : V} (h : Disjoint (cluster H ω D s) S) :
    clusters H ω (D ∪ cluster H ω D s) S = clusters H ω D S := by
  ext y
  constructor
  · exact fun hy => clusters_mono_delete Set.subset_union_left hy
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, hx, ?_⟩
    have heq := cluster_delete_clusters (H := H) (ω := ω) (D := D) (S := {s})
      (x := x) (by simpa only [clusters_singleton] using (fun hxs => Set.disjoint_left.mp h hxs hx))
    rw [clusters_singleton] at heq
    rwa [heq]

theorem cluster_eq_of_connected {H : Hypergraph V E} {ω : E → Bool} {D : Set V}
    {s t : V} (hst : Connected H ω D s t) :
    cluster H ω D s = cluster H ω D t := by
  ext y
  exact ⟨fun hy => connected_trans (connected_symm hst) hy,
    fun hy => connected_trans hst hy⟩

def earlier {n : ℕ} (x : Fin n → V) (k : Fin n) : Set V :=
  {v | ∃ j, j < k ∧ x j = v}

def firstRoot {n : ℕ} (H : Hypergraph V E) (x : Fin n → V) (ω : E → Bool)
    (D : Set V) (k i : Fin n) : Prop :=
  Disjoint (cluster H ω D (x k)) (earlier x k) ∧ Connected H ω D (x k) (x i)

theorem firstRoot_iff {n : ℕ} {H : Hypergraph V E} {x : Fin n → V} {ω : E → Bool}
    {D : Set V} {k i : Fin n} :
    firstRoot H x ω D k i ↔ Connected H ω D (x k) (x i) ∧
      ∀ j < k, ¬Connected H ω D (x j) (x i) := by
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨hc, ?_⟩
    intro j hj hji
    exact Set.disjoint_left.mp hd (connected_trans hc (connected_symm hji)) ⟨j, hj, rfl⟩
  · rintro ⟨hc, hf⟩
    refine ⟨Set.disjoint_left.mpr ?_, hc⟩
    rintro y hy ⟨j, hj, rfl⟩
    exact hf j hj (connected_trans (connected_symm hy) hc)

theorem exists_unique_firstRoot {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (D : Set V) (i : Fin n) : ∃! k, firstRoot H x ω D k i := by
  classical
  let J := Finset.univ.filter (fun j => Connected H ω D (x j) (x i))
  have hJ : J.Nonempty := ⟨i, by simp [J, connected_refl]⟩
  let k := J.min' hJ
  have hkJ : k ∈ J := Finset.min'_mem J hJ
  have hkc : Connected H ω D (x k) (x i) := (Finset.mem_filter.mp hkJ).2
  have hf : firstRoot H x ω D k i := by
    apply firstRoot_iff.mpr
    refine ⟨hkc, ?_⟩
    intro j hj hc
    have hkj : k ≤ j := Finset.min'_le J j (by simp [J, hc])
    exact (not_le_of_gt hj) hkj
  refine ⟨k, hf, ?_⟩
  intro j hj
  apply le_antisymm
  · by_contra h
    exact (firstRoot_iff.mp hj).2 k (lt_of_not_ge h) hkc
  · exact Finset.min'_le J j (by simp [J, (firstRoot_iff.mp hj).1])

/-- The first-listed-node partition, as a pointwise identity for any cluster
functional. This is stronger than its integrated mass identity H d = 1. -/
theorem sum_firstRoot {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (D : Set V) (i : Fin n) (F : Set V → ℝ) :
    (∑ k, if firstRoot H x ω D k i then F (cluster H ω D (x k)) else 0) =
      F (cluster H ω D (x i)) := by
  classical
  obtain ⟨k, hk, huniq⟩ := exists_unique_firstRoot H x ω D i
  rw [Finset.sum_eq_single k]
  · rw [ite_eq_left hk, cluster_eq_of_connected hk.2]
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (huniq j h))]
  · simp

section FiniteLaw
variable [Fintype E]

noncomputable def law (p : E → Set.Icc (0 : ℝ) 1) : Measure (E → Bool) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

instance law_probability (p : E → Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (law p) := by
  unfold law
  infer_instance

/-- Functions of complementary finite sets of independent bits are independent.
The dependence conditions are extensional, avoiding auxiliary sigma-algebras. -/
theorem independent_of_disjoint_bits (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (f g : (E → Bool) → ℝ)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hg : ∀ ω ω', (∀ e ∉ J, ω' e = ω e) → g ω' = g ω) :
    IndepFun f g (law p) := by
  classical
  let f' : (J → Bool) → ℝ := fun a => f (fun e => if h : e ∈ J then a ⟨e,h⟩ else false)
  let g' : (↑(Jᶜ) → Bool) → ℝ := fun a =>
    g (fun e => if h : e ∈ Jᶜ then a ⟨e,h⟩ else false)
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (law p) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h := (hi.indepFun_finset J Jᶜ disjoint_compl_right
    (fun e => measurable_pi_apply e)).comp
    (measurable_of_countable f') (measurable_of_countable g')
  have heqf : (f' ∘ (fun (ω : E → Bool) (e : J) => ω e)) = f := by
    funext ω
    apply hf
    intro e he
    simp [he]
  have heqg : (g' ∘ (fun (ω : E → Bool) (e : ↑(Jᶜ)) => ω e)) = g := by
    funext ω
    apply hg
    intro e he
    simp [he]
  rwa [heqf, heqg] at h

/-- The exact-cluster indicator sees no bit on a hyperedge disjoint from W,
including when the cluster was sampled after an earlier deletion D. -/
theorem exact_cluster_independent (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    IndepFun (fun ω => if clusters H ω D S = W then (1 : ℝ) else 0) g (law p) := by
  classical
  apply independent_of_disjoint_bits p (Finset.univ.filter (fun e => ¬ Disjoint (H e) W))
  · intro ω ω' hagree
    have heq : clusters H ω' D S = W ↔ clusters H ω D S = W := by
      constructor
      · intro h
        have hh : clusters H ω D S = clusters H ω' D S := by
          apply clusters_eq_of_agree_incident
          intro e he
          rw [h] at he
          exact (hagree e (by simp [he])).symm
        exact hh.trans h
      · intro h
        have hh : clusters H ω' D S = clusters H ω D S := by
          apply clusters_eq_of_agree_incident
          intro e he
          rw [h] at he
          exact hagree e (by simp [he])
        exact hh.trans h
    simp only [heq]
  · intro ω ω' hagree
    apply hg ω ω'
    intro e he
    exact hagree e (by simp [he])

/-- Integrated exact-cluster independence, with no positivity restriction on
an exact cluster event (zero probability events also satisfy the identity). -/
theorem exact_cluster_integral (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    (∫ ω, (if clusters H ω D S = W then (1 : ℝ) else 0) * g ω ∂law p) =
      (∫ ω, if clusters H ω D S = W then (1 : ℝ) else 0 ∂law p) *
        ∫ ω, g ω ∂law p := by
  classical
  exact (exact_cluster_independent H p D S W g hg).integral_fun_mul_eq_mul_integral
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- Partition a finite expectation by exact values, without conditional-probability
notation and without requiring positive individual atom masses. -/
theorem integral_eq_sum_fibers {I : Type uI} [Fintype I] [DecidableEq I]
    (p : E → Set.Icc (0 : ℝ) 1) (X : (E → Bool) → I) (f : (E → Bool) → ℝ) :
    (∫ ω, f ω ∂law p) = ∑ i, ∫ ω, if X ω = i then f ω else 0 ∂law p := by
  classical
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  congr 1
  funext ω
  simp

noncomputable def meanAfterDelete (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (s : V) (W : Set V) (F : Set V → ℝ) : ℝ :=
  ∫ ω, F (cluster H ω W s) ∂law p

noncomputable def resample (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (s : V) (S : Set V) (F : Set V → ℝ) (U : Set V) : ℝ :=
  ∫ ω, meanAfterDelete H p s (clusters H ω U S) F ∂law p

noncomputable def residualMean (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (s : V) (S U : Set V) (F : Set V → ℝ) : ℝ := by
  classical
  exact ∫ ω, if s ∈ clusters H ω U S then 0 else
    meanAfterDelete H p s (clusters H ω U S) F -
      meanAfterDelete H p s (clusters H ω U S ∪ U) F ∂law p

theorem residualMean_eq_integral [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S U : Set V) (F : Set V → ℝ) :
    residualMean H p s S U F = ∫ ω, residualSample H ω s S U F ∂law p := by
  classical
  unfold residualMean
  rw [integral_eq_sum_fibers p (fun ω => clusters H ω U S),
    integral_eq_sum_fibers p (fun ω => clusters H ω U S)]
  apply Finset.sum_congr rfl
  intro W _
  by_cases hs : s ∈ W
  · have hleft : (fun ω => if clusters H ω U S = W then
        (if s ∈ clusters H ω U S then 0 else
          meanAfterDelete H p s (clusters H ω U S) F -
          meanAfterDelete H p s (clusters H ω U S ∪ U) F) else 0) =
        (fun _ => (0 : ℝ)) := by
      funext ω
      split_ifs with h <;> simp_all
    have hright : (fun ω => if clusters H ω U S = W then
        residualSample H ω s S U F else 0) = (fun _ => (0 : ℝ)) := by
      funext ω
      unfold residualSample
      split_ifs with h <;> simp_all
    rw [hleft, hright]
  · let g : (E → Bool) → ℝ := fun ω =>
        F (cluster H ω W s) - F (cluster H ω (W ∪ U) s)
    have hind := exact_cluster_integral H p U S W g (by
      intro ω ω' hagree
      dsimp [g]
      rw [cluster_eq_of_agree_disjoint hagree s,
        cluster_eq_of_agree_disjoint (fun e he => hagree e (he.mono_right Set.subset_union_left)) s])
    have hleft : (fun ω => if clusters H ω U S = W then
        (if s ∈ clusters H ω U S then 0 else
          meanAfterDelete H p s (clusters H ω U S) F -
          meanAfterDelete H p s (clusters H ω U S ∪ U) F) else 0) =
        (fun ω => (if clusters H ω U S = W then (1 : ℝ) else 0) *
          (∫ ω', g ω' ∂law p)) := by
      funext ω
      by_cases h : clusters H ω U S = W
      · simp [h, hs, g, meanAfterDelete,
          integral_sub (Integrable.of_finite) (Integrable.of_finite)]
      · simp [h]
    have hright : (fun ω => if clusters H ω U S = W then
        residualSample H ω s S U F else 0) =
        (fun ω => (if clusters H ω U S = W then (1 : ℝ) else 0) * g ω) := by
      funext ω
      by_cases h : clusters H ω U S = W
      · simp [h, hs, g, residualSample]
      · simp [h]
    rw [hleft, hright, integral_mul_const, hind]

theorem residualMean_nonneg [Fintype V] {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S U : Set V} {F : Set V → ℝ}
    (hsU : s ∉ U) (hF : MonotoneOn F (ClusterDomain s S)) :
    0 ≤ residualMean H p s S U F := by
  rw [residualMean_eq_integral]
  exact integral_nonneg (fun _ => residualSample_nonneg hsU hF)

theorem residualMean_mono [Fintype V] {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S U U' : Set V} {F : Set V → ℝ}
    (hUU : U ⊆ U') (hsU' : s ∉ U') (hF : MonotoneOn F (ClusterDomain s S)) :
    residualMean H p s S U F ≤ residualMean H p s S U' F := by
  rw [residualMean_eq_integral, residualMean_eq_integral]
  exact integral_mono (Integrable.of_finite) (Integrable.of_finite)
    (fun _ => residualSample_mono hUU hsU' hF)

theorem meanAfterDelete_antitone {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S W W' : Set V} {F : Set V → ℝ}
    (hWW : W ⊆ W') (hSW : S ⊆ W) (hs : s ∉ W')
    (hF : MonotoneOn F (ClusterDomain s S)) :
    meanAfterDelete H p s W' F ≤ meanAfterDelete H p s W F := by
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  apply hF
  · exact ⟨.refl, (cluster_avoids_deleted hs).mono_right (hSW.trans hWW)⟩
  · exact ⟨.refl, (cluster_avoids_deleted (fun h => hs (hWW h))).mono_right hSW⟩
  · exact cluster_mono_delete hWW s

theorem resample_monotone {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S : Set V} {F : Set V → ℝ}
    (hF : MonotoneOn F (ClusterDomain s S)) :
    MonotoneOn (resample H p s S F) (ClusterDomain s S) := by
  intro U hU U' hU' hUU
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  apply meanAfterDelete_antitone (clusters_mono_delete hUU) (clusters_contains H ω U' S)
  · exact fun hs => Set.disjoint_left.mp (clusters_avoids_deleted hU.2.symm) hs hU.1
  · exact hF

theorem resample_nonneg {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S U : Set V} {F : Set V → ℝ}
    (hF : ∀ U ∈ ClusterDomain s S, 0 ≤ F U) (hU : U ∈ ClusterDomain s S) :
    0 ≤ resample H p s S F U := by
  apply integral_nonneg
  intro ω
  apply integral_nonneg
  intro ω'
  apply hF
  exact ⟨.refl, (cluster_avoids_deleted (fun hs =>
    Set.disjoint_left.mp (clusters_avoids_deleted hU.2.symm) hs hU.1)).mono_right
      (clusters_contains H ω U S)⟩

noncomputable def clusterMass (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (D S W : Set V) : ℝ :=
  ∫ ω, if clusters H ω D S = W then (1 : ℝ) else 0 ∂law p

/-- The exact-cluster conditional expectation used in the column partition. -/
theorem cluster_conditioning (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S W : Set V) (F : Set V → ℝ)
    (hs : s ∉ W) :
    (∫ ω, if clusters H ω D S = W then F (cluster H ω D s) else 0 ∂law p) =
      clusterMass H p D S W * meanAfterDelete H p s (D ∪ W) F := by
  classical
  have hind := exact_cluster_integral H p D S W
    (fun ω => F (cluster H ω (D ∪ W) s)) (by
      intro ω ω' hagree
      rw [cluster_eq_of_agree_disjoint
        (fun e he => hagree e (he.mono_right Set.subset_union_right)) s])
  unfold clusterMass meanAfterDelete
  rw [← hind]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases h : clusters H ω D S = W
  · have hcs : cluster H ω (D ∪ W) s = cluster H ω D s := by
      rw [← h]
      exact cluster_delete_clusters (by rwa [h])
    simp [h, hcs]
  · simp [h]

/-- Multiply the exact-cluster identity by an arbitrary function of the cluster.
No positive-probability conditioning is needed. -/
theorem exact_cluster_weight [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S : Set V) (f : Set V → ℝ)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, f (clusters H ω D S) * g ω (clusters H ω D S) ∂law p) =
      ∫ ω, f (clusters H ω D S) * (∫ ω', g ω' (clusters H ω D S) ∂law p) ∂law p := by
  classical
  rw [integral_eq_sum_fibers p (fun ω => clusters H ω D S),
    integral_eq_sum_fibers p (fun ω => clusters H ω D S)]
  apply Finset.sum_congr rfl
  intro U _
  have hleft : (fun ω => if clusters H ω D S = U then
      f (clusters H ω D S) * g ω (clusters H ω D S) else 0) =
      (fun ω => f U * ((if clusters H ω D S = U then (1:ℝ) else 0) * g ω U)) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  have hright : (fun ω => if clusters H ω D S = U then
      f (clusters H ω D S) * (∫ ω', g ω' (clusters H ω D S) ∂law p) else 0) =
      (fun ω => f U * ((if clusters H ω D S = U then (1:ℝ) else 0) *
        (∫ ω', g ω' U ∂law p))) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  rw [hleft, hright, integral_const_mul, integral_const_mul, integral_mul_const,
    exact_cluster_integral H p D S U (fun ω => g ω U) (hg U)]

/-- Exact-cluster integration of a functional rooted outside the measured cluster. -/
theorem conditioning_weight [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S : Set V)
    (w : Set V → ℝ) (F : Set V → ℝ) (hw : ∀ U, s ∈ U → w U = 0) :
    (∫ ω, w (clusters H ω D S) * F (cluster H ω D s) ∂law p) =
      ∫ ω, w (clusters H ω D S) *
        meanAfterDelete H p s (D ∪ clusters H ω D S) F ∂law p := by
  classical
  rw [integral_eq_sum_fibers p (fun ω => clusters H ω D S),
    integral_eq_sum_fibers p (fun ω => clusters H ω D S)]
  apply Finset.sum_congr rfl
  intro U _
  have hleft : (fun ω => if clusters H ω D S = U then
      w (clusters H ω D S) * F (cluster H ω D s) else 0) =
      (fun ω => w U * (if clusters H ω D S = U then F (cluster H ω D s) else 0)) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  have hright : (fun ω => if clusters H ω D S = U then
      w (clusters H ω D S) * meanAfterDelete H p s (D ∪ clusters H ω D S) F else 0) =
      (fun ω => w U * ((if clusters H ω D S = U then (1:ℝ) else 0) *
        meanAfterDelete H p s (D ∪ U) F)) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  rw [hleft, hright, integral_const_mul, integral_const_mul, integral_mul_const]
  by_cases hs : s ∈ U
  · simp [hw U hs]
  · rw [cluster_conditioning H p s D S U F hs]
    rfl

/-- For residuals, after conditioning on W the second sample may instead be
read in the original configuration on the graph with U deleted. -/
theorem residualMean_alternative [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S U : Set V) (F : Set V → ℝ) :
    residualMean H p s S U F =
      ∫ ω, if s ∈ clusters H ω U S then 0 else
        meanAfterDelete H p s (clusters H ω U S) F - F (cluster H ω U s) ∂law p := by
  classical
  have hc := conditioning_weight H p s U S
    (fun W => if s ∈ W then 0 else 1) F (by intro W h; simp [h])
  have heq₁ : (fun ω => if s ∈ clusters H ω U S then (0:ℝ) else
      meanAfterDelete H p s (clusters H ω U S) F - F (cluster H ω U s)) =
      (fun ω => (if s ∈ clusters H ω U S then 0 else meanAfterDelete H p s
        (clusters H ω U S) F) - (if s ∈ clusters H ω U S then 0 else 1) *
          F (cluster H ω U s)) := by
    funext ω
    split_ifs <;> simp
  have heq₂ : (fun ω => if s ∈ clusters H ω U S then (0:ℝ) else
      meanAfterDelete H p s (clusters H ω U S) F -
        meanAfterDelete H p s (clusters H ω U S ∪ U) F) =
      (fun ω => (if s ∈ clusters H ω U S then 0 else meanAfterDelete H p s
        (clusters H ω U S) F) - (if s ∈ clusters H ω U S then 0 else 1) *
          meanAfterDelete H p s (U ∪ clusters H ω U S) F) := by
    funext ω
    split_ifs <;> simp [Set.union_comm]
  unfold residualMean
  rw [heq₁, heq₂, integral_sub (Integrable.of_finite) (Integrable.of_finite),
    integral_sub (Integrable.of_finite) (Integrable.of_finite), hc]

noncomputable def column {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ)
    (i : Fin n) : ℝ := by
  classical
  exact ∫ ω, if firstRoot H x ω ∅ k i then F (cluster H ω ∅ (x k)) else 0 ∂law p

theorem sum_column {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (F : Set V → ℝ) (i : Fin n) :
    ∑ k, column H p x k F i = ∫ ω, F (cluster H ω ∅ (x i)) ∂law p := by
  classical
  unfold column
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => sum_firstRoot H x ω ∅ i F)

/-- The first-listed-event column disintegrates over its exact root cluster. -/
theorem column_conditional_expectation [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, if firstRoot H x ω ∅ k i then g ω (cluster H ω ∅ (x k)) else 0 ∂law p) =
      column H p x k (fun U => ∫ ω, g ω U ∂law p) i := by
  classical
  have h := exact_cluster_weight H p ∅ {x k}
    (fun U => if Disjoint U (earlier x k) ∧ x i ∈ U then 1 else 0) g hg
  simp only [clusters_singleton] at h
  have heq (q : (E → Bool) → Set V → ℝ) :
      (fun ω => if firstRoot H x ω ∅ k i then q ω (cluster H ω ∅ (x k)) else 0) =
      (fun ω => (if Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧
        x i ∈ cluster H ω ∅ (x k) then (1:ℝ) else 0) * q ω (cluster H ω ∅ (x k))) := by
    funext ω
    by_cases hf : firstRoot H x ω ∅ k i
    · have hf' : Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧
          x i ∈ cluster H ω ∅ (x k) := hf
      simp [hf, hf']
    · have hf' : ¬(Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧
          x i ∈ cluster H ω ∅ (x k)) := hf
      simp [hf, hf']
  rw [← heq g, ← heq (fun _ U => ∫ ω, g ω U ∂law p)] at h
  exact h

theorem column_resample [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n) (F : Set V → ℝ) :
    column H p x k (resample H p (x k) (earlier x k) F) i =
      ∫ ω, if firstRoot H x ω ∅ k i then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F else 0 ∂law p := by
  classical
  have h := column_conditional_expectation H p x k i
    (fun ω U => meanAfterDelete H p (x k) (clusters H ω U (earlier x k)) F)
    (by intro U ω ω' hagree; rw [clusters_eq_of_agree_disjoint hagree])
  change _ = column H p x k (resample H p (x k) (earlier x k) F) i at h
  rw [← h]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i
  · have heq := clusters_delete_cluster hf.1
    simp only [Set.empty_union] at heq
    simp [hf, heq]
  · simp [hf]

/-- An earlier list segment is included in every later segment. -/
theorem earlier_mono {n : ℕ} (x : Fin n → V) {k j : Fin n} (hkj : k ≤ j) :
    earlier x k ⊆ earlier x j := by
  rintro y ⟨l, hl, hly⟩
  exact ⟨l, lt_of_lt_of_le hl hkj, hly⟩

/-- The residual term after conditioning on C(x_j), retaining the original
configuration only on hyperedges disjoint from that cluster. -/
theorem column_residual [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k j i : Fin n)
    (hkj : k < j) (F : Set V → ℝ) :
    column H p x j (residualMean H p (x k) (earlier x k) · F) i =
      ∫ ω, if firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k) then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F -
          F (cluster H ω ∅ (x k)) else 0 ∂law p := by
  classical
  have hfun : (fun U => residualMean H p (x k) (earlier x k) U F) =
      (fun U => ∫ ω, if x k ∈ clusters H ω U (earlier x k) then 0 else
        meanAfterDelete H p (x k) (clusters H ω U (earlier x k)) F -
          F (cluster H ω U (x k)) ∂law p) := by
    funext U
    exact residualMean_alternative H p (x k) (earlier x k) U F
  rw [hfun]
  rw [← column_conditional_expectation H p x j i _ (by
    intro U ω ω' hagree
    rw [clusters_eq_of_agree_disjoint hagree, cluster_eq_of_agree_disjoint hagree])]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ j i
  · have hdis : Disjoint (cluster H ω ∅ (x j)) (earlier x k) :=
      hf.1.mono_right (earlier_mono x hkj.le)
    have hs : x k ∉ cluster H ω ∅ (x j) := fun hs =>
      Set.disjoint_left.mp hf.1 hs ⟨k, hkj, rfl⟩
    have hW := clusters_delete_cluster hdis
    have hC := cluster_delete_clusters (H := H) (ω := ω) (D := ∅) (S := {x j})
      (x := x k) (by simpa only [clusters_singleton] using hs)
    simp only [Set.empty_union, clusters_singleton] at hW hC
    simp only [hf, ite_true, hW, hC, true_and]
    split_ifs <;> simp_all
  · simp [hf]

omit [Fintype E] in
/-- Separation from a union of full clusters is exactly avoidance by the root. -/
theorem disjoint_cluster_iff_root_notin {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {s : V} :
    Disjoint (cluster H ω D s) S ↔ s ∉ clusters H ω D S := by
  constructor
  · rintro hd ⟨t, ht, hts⟩
    exact Set.disjoint_left.mp hd (connected_symm hts) ht
  · intro hs
    apply Set.disjoint_left.mpr
    intro t hst ht
    exact hs ⟨t, ht, connected_symm hst⟩

omit [Fintype E] in
theorem firstRoot_notin_earlier_clusters {n : ℕ} {H : Hypergraph V E}
    {x : Fin n → V} {ω : E → Bool} {D : Set V} {j i k : Fin n}
    (hf : firstRoot H x ω D j i) (hkj : k ≤ j) :
    x i ∉ clusters H ω D (earlier x k) := by
  have hd := (cluster_disjoint_clusters_iff.mpr hf.1).mono_right
    (show clusters H ω D (earlier x k) ⊆ clusters H ω D (earlier x j) from by
      rintro y ⟨z, hz, hzy⟩
      exact ⟨z, earlier_mono x hkj hz, hzy⟩)
  exact fun hi => Set.disjoint_left.mp hd hf.2 hi

omit [Fintype E] in

theorem firstListed_partition {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (k i : Fin n) (a : ℝ) :
    (if x k ∉ clusters H ω ∅ (earlier x k) ∧ x i ∉ clusters H ω ∅ (earlier x k)
      then a else 0) =
      (if firstRoot H x ω ∅ k i then a else 0) +
        ∑ j, if k < j ∧ firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
          then a else 0 := by
  classical
  obtain ⟨j, hj, huniq⟩ := exists_unique_firstRoot H x ω ∅ i
  have hsum : (∑ l, if k < l ∧ firstRoot H x ω ∅ l i ∧
      x k ∉ clusters H ω ∅ (earlier x k) then a else 0) =
      if k < j ∧ x k ∉ clusters H ω ∅ (earlier x k) then a else 0 := by
    rw [Finset.sum_eq_single j]
    · simp only [hj, true_and]
    · intro l _ hlj
      have hlf : ¬firstRoot H x ω ∅ l i := fun h => hlj (huniq l h)
      simp [hlf]
    · simp
  rw [hsum]
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hi : x i ∈ clusters H ω ∅ (earlier x k) := ⟨x j, ⟨j, hjk,rfl⟩, hj.2⟩
    have hk : ¬firstRoot H x ω ∅ k i := fun h => (ne_of_lt hjk) (huniq k h).symm
    simp [hi, hk, not_lt_of_gt hjk]
  · have hs := disjoint_cluster_iff_root_notin.mp hj.1
    have hi := firstRoot_notin_earlier_clusters hj le_rfl
    simp [hj, hs, hi]
  · have hi := firstRoot_notin_earlier_clusters hj hkj.le
    have hk : ¬firstRoot H x ω ∅ k i := fun h => (ne_of_lt hkj) (huniq k h)
    simp [hi, hk, hkj]

/-- Integrated form of the first-listed-node partition. -/
theorem integral_firstListed_partition {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n)
    (g : (E → Bool) → ℝ) :
    (∫ ω, if x k ∉ clusters H ω ∅ (earlier x k) ∧ x i ∉ clusters H ω ∅ (earlier x k)
      then g ω else 0 ∂law p) =
      (∫ ω, if firstRoot H x ω ∅ k i then g ω else 0 ∂law p) +
        ∑ j, ∫ ω, if k < j ∧ firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
          then g ω else 0 ∂law p := by
  simp_rw [firstListed_partition H x _ k i]
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_finsetSum _ (fun _ _ => Integrable.of_finite)]

/-- Subtraction under a finite expectation with the same event indicator. -/
theorem integral_indicator_sub (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) [DecidablePred P] (f g : (E → Bool) → ℝ) :
    (∫ ω, if P ω then f ω - g ω else 0 ∂law p) =
      (∫ ω, if P ω then f ω else 0 ∂law p) -
        ∫ ω, if P ω then g ω else 0 ∂law p := by
  have h : (fun ω => if P ω then f ω-g ω else 0) =
      (fun ω => (if P ω then f ω else 0) - (if P ω then g ω else 0)) := by
    funext ω
    by_cases h : P ω <;> simp [h]
  rw [h, integral_sub (Integrable.of_finite) (Integrable.of_finite)]

theorem column_identity [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n) (F : Set V → ℝ) :
    column H p x k F i = column H p x k (resample H p (x k) (earlier x k) F) i +
      ∑ j, if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) i
        else 0 := by
  classical
  let c : (E → Bool) → ℝ := fun ω =>
    meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F
  let f : (E → Bool) → ℝ := fun ω => F (cluster H ω ∅ (x k))
  let P : Fin n → (E → Bool) → Prop := fun j ω =>
    k < j ∧ firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
  have hcond := conditioning_weight H p (x k) ∅ (earlier x k)
    (fun U => if x k ∉ U ∧ x i ∉ U then 1 else 0) F (by intro U h; simp [h])
  simp only [ite_mul, one_mul, zero_mul, Set.empty_union] at hcond
  rw [integral_firstListed_partition H p x k i,
    integral_firstListed_partition H p x k i] at hcond
  change column H p x k F i + (∑ j, ∫ ω, if P j ω then f ω else 0 ∂law p) =
    (∫ ω, if firstRoot H x ω ∅ k i then c ω else 0 ∂law p) +
      (∑ j, ∫ ω, if P j ω then c ω else 0 ∂law p) at hcond
  have hbase : column H p x k (resample H p (x k) (earlier x k) F) i =
      ∫ ω, if firstRoot H x ω ∅ k i then c ω else 0 ∂law p :=
    column_resample H p x k i F
  have hres (j : Fin n) :
      (if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) i else 0) =
        (∫ ω, if P j ω then c ω else 0 ∂law p) -
          ∫ ω, if P j ω then f ω else 0 ∂law p := by
    by_cases hkj : k < j
    · rw [ite_eq_left hkj, column_residual H p x k j i hkj F]
      rw [← integral_indicator_sub p (P j) c f]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
      · simp [P, hkj, h, c, f]
      · simp [P, hkj, h]
    · simp [P, hkj]
  have hsum : (∑ j, if k < j then
      column H p x j (residualMean H p (x k) (earlier x k) · F) i else 0) =
      (∑ j, ∫ ω, if P j ω then c ω else 0 ∂law p) -
        (∑ j, ∫ ω, if P j ω then f ω else 0 ∂law p) := by
    simp_rw [hres]
    rw [Finset.sum_sub_distrib]
  rw [hsum, hbase]
  linarith

omit [Fintype E] in
/-- Closing every hyperedge isolates every node, in every deletion graph. -/
theorem cluster_all_closed (H : Hypergraph V E) (D : Set V) (s : V) :
    cluster H (fun _ => false) D s = {s} := by
  ext y
  constructor
  · intro hy
    change y = s
    induction hy with
    | refl => rfl
    | tail _ h _ => obtain ⟨e, he, _⟩ := h; simp at he
  · rintro rfl
    exact .refl

/-- A state of the alternating conditional cluster resampling chain. -/
noncomputable def nextState (H : Hypergraph V E) (s : V) (S : Set V)
    (U : ClusterDomain s S) (ω ω' : E → Bool) : ClusterDomain s S :=
  ⟨cluster H ω' (clusters H ω U.1 S) s,
    ⟨.refl, (cluster_avoids_deleted (fun hs =>
      Set.disjoint_left.mp (clusters_avoids_deleted U.2.2.symm) hs U.2.1)).mono_right
        (clusters_contains H ω U.1 S)⟩⟩

/-- The finite transition matrix for the actual two-stage cluster resampling. -/
noncomputable def resamplingTransition [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) :
    FiniteResampling.Transition (ClusterDomain s S) where
  weight U T := ∫ ω, ∫ ω', if nextState H s S U ω ω' = T then (1:ℝ) else 0 ∂law p ∂law p
  nonneg U T := integral_nonneg (fun _ => integral_nonneg (fun _ => by split_ifs <;> norm_num))
  total U := by
    classical
    rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    have heq : (fun ω => ∑ T : ClusterDomain s S,
        ∫ ω', if nextState H s S U ω ω' = T then (1:ℝ) else 0 ∂law p) =
        (fun _ => (1:ℝ)) := by
      funext ω
      rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      simp
    rw [heq]
    simp

theorem resamplingTransition_act [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (F : Set V → ℝ)
    (U : ClusterDomain s S) :
    (resamplingTransition H p s S).act (fun T => F T.1) U =
      resample H p s S F U.1 := by
  classical
  unfold FiniteResampling.Transition.act resamplingTransition resample meanAfterDelete
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω'
  change (∑ T : ClusterDomain s S,
    (if nextState H s S U ω ω' = T then (1:ℝ) else 0) * F T.1) =
      F (nextState H s S U ω ω').1
  simp [ite_mul]

/-- Probability mass of the all-closed finite configuration. -/
theorem all_closed_mass (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).real {fun _ => false} = ∏ e, (1 - (p e : ℝ)) := by
  classical
  rw [Measure.real_def, law, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {false} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton false)]
  simp [unitInterval.coe_symm_eq]

theorem all_closed_mass_pos (p : E → Set.Icc (0 : ℝ) 1)
    (hp : ∀ e, (p e : ℝ) < 1) : 0 < (law p).real {fun _ => false} := by
  rw [all_closed_mass]
  exact Finset.prod_pos (fun e _ => sub_pos.mpr (hp e))

/-- A uniform positive atom, without discarding any zero-mass cluster states. -/
theorem resamplingTransition_atom [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (hs : s ∉ S)
    (U : ClusterDomain s S) :
    (law p).real {fun _ => false} ≤ (resamplingTransition H p s S).weight U
      ⟨{s}, ⟨by simp, by simpa using hs⟩⟩ := by
  classical
  let z : ClusterDomain s S := ⟨{s}, ⟨by simp, by simpa using hs⟩⟩
  have hi : (∫ ω' : E → Bool, if ω' = (fun _ => false) then (1:ℝ) else 0 ∂law p) =
      (law p).real {fun _ => false} := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := law p) (s := {fun _ => false}) (measurableSet_singleton _))
  have hj (ω : E → Bool) : (law p).real {fun _ => false} ≤
      ∫ ω', if nextState H s S U ω ω' = z then (1:ℝ) else 0 ∂law p := by
    rw [← hi]
    apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
    intro ω'
    by_cases hc : ω' = (fun _ => false)
    · subst ω'
      have heq : nextState H s S U ω (fun _ => false) = z := by
        apply Subtype.ext
        exact cluster_all_closed H _ s
      simp [heq]
    · simp only [hc, ite_false]
      split_ifs <;> norm_num
  have h := integral_mono (μ := law p) (Integrable.of_finite) (Integrable.of_finite) hj
  simpa [resamplingTransition, z] using h

/-- The actual conditional cluster-resampling iterates tend to a nonnegative
constant. This version does not need stationarity or positive mass at every state. -/
theorem resample_tendsto_constant [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (s : V) (S : Set V) (hs : s ∉ S) (F : Set V → ℝ)
    (hF : ∀ U ∈ ClusterDomain s S, 0 ≤ F U) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ U ∈ ClusterDomain s S,
      Tendsto (fun n : ℕ => ((resample H p s S)^[n] F) U) atTop (nhds c) := by
  classical
  let z : ClusterDomain s S := ⟨{s}, ⟨by simp, by simpa using hs⟩⟩
  let : Nonempty (ClusterDomain s S) := ⟨z⟩
  let K := resamplingTransition H p s S
  let a := (law p).real {fun _ => false}
  have ha0 : 0 < a := all_closed_mass_pos p hp
  have ha1 : a ≤ 1 := measureReal_le_one
  have hatom : ∀ U, a ≤ K.weight U z := fun U => resamplingTransition_atom H p s S hs U
  obtain ⟨c, hcl, _, hlim⟩ := K.iterates_tendsto_constant z a ha0 ha1 hatom (fun U => F U.1)
  have hc : 0 ≤ c := (FiniteResampling.le_lower (fun U : ClusterDomain s S => hF U.1 U.2)).trans hcl
  have heq (n : ℕ) : (fun U : ClusterDomain s S => ((resample H p s S)^[n] F) U.1) =
      (K.act)^[n] (fun U => F U.1) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      funext U
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [← resamplingTransition_act H p s S ((resample H p s S)^[n] F) U]
      exact congrFun (congrArg K.act ih) U
  refine ⟨c, hc, ?_⟩
  intro U hU
  have h := hlim ⟨U, hU⟩
  simpa only [← heq] using h

/-- Pointwise convergence exchanges with any expectation on a finite bit space. -/
theorem tendsto_integral_finite (p : E → Set.Icc (0 : ℝ) 1)
    (f : ℕ → (E → Bool) → ℝ) (g : (E → Bool) → ℝ)
    (h : ∀ ω, Tendsto (fun n => f n ω) atTop (nhds (g ω))) :
    Tendsto (fun n => ∫ ω, f n ω ∂law p) atTop (nhds (∫ ω, g ω ∂law p)) := by
  simp_rw [integral_fintype (Integrable.of_finite)]
  exact tendsto_finsetSum _ (fun ω _ => tendsto_const_nhds.smul (h ω))

/-- Column convergence only needs convergence on its specified cluster domain. -/
theorem column_tendsto {n : ℕ} (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (x : Fin n → V) (k i : Fin n) (F : ℕ → Set V → ℝ) (c : ℝ)
    (h : ∀ U ∈ ClusterDomain (x k) (earlier x k),
      Tendsto (fun t => F t U) atTop (nhds c)) :
    Tendsto (fun t => column H p x k (F t) i) atTop
      (nhds (column H p x k (fun _ => c) i)) := by
  unfold column
  apply tendsto_integral_finite
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i
  · simp only [hf, ite_true]
    exact h _ ⟨.refl, hf.1⟩
  · simp only [hf, ite_false]
    exact tendsto_const_nhds

/-- Unnormalized cluster columns d_k h_k. -/
noncomputable def baseMatrix {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => column H p x k (fun _ => 1) i

omit [Fintype E] in
theorem root_notin_earlier {n : ℕ} {x : Fin n → V} (hx : Function.Injective x) (k : Fin n) :
    x k ∉ earlier x k := by
  rintro ⟨j, hj, heq⟩
  exact (ne_of_lt hj) (hx heq)

theorem baseMatrix_lowerTriangular {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) : (baseMatrix H p x).IsLowerTriangular := by
  intro i j hij
  have hf (ω : E → Bool) : ¬firstRoot H x ω ∅ j i := by
    intro hf
    exact Set.disjoint_left.mp hf.1 hf.2 ⟨i, hij, rfl⟩
  simp [baseMatrix, column, hf]

/-- The diagonal mass is positive because fully closing the graph ensures E_k. -/
theorem baseMatrix_diag_pos {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < baseMatrix H p x k k := by
  have hi : (∫ ω : E → Bool, if ω = (fun _ => false) then (1:ℝ) else 0 ∂law p) =
      (law p).real {fun _ => false} := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := law p) (s := {fun _ => false}) (measurableSet_singleton _))
  apply (all_closed_mass_pos p hp).trans_le
  rw [← hi]
  unfold baseMatrix column
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  by_cases hc : ω = (fun _ => false)
  · subst ω
    have hf : firstRoot H x (fun _ => false) ∅ k k := by
      refine ⟨?_, .refl⟩
      rw [cluster_all_closed]
      simpa using root_notin_earlier hx k
    simp [hf]
  · simp only [hc, ite_false]
    split_ifs <;> norm_num

theorem baseMatrix_det_ne_zero {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) :
    (baseMatrix H p x).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (baseMatrix_lowerTriangular H p x)]
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => ne_of_gt (baseMatrix_diag_pos H p hp x hx k))

/-- Coordinates in the basis of unnormalized cluster columns. -/
noncomputable def coeff {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) : Fin n → ℝ :=
  (baseMatrix H p x)⁻¹ *ᵥ column H p x k F

theorem column_const {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (c : ℝ) :
    column H p x k (fun _ => c) = c • column H p x k (fun _ => 1) := by
  funext i
  unfold column
  change (∫ ω, if firstRoot H x ω ∅ k i then c else 0 ∂law p) =
    c * ∫ ω, if firstRoot H x ω ∅ k i then 1 else 0 ∂law p
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i <;> simp [hf]

theorem coeff_const {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k i : Fin n) (c : ℝ) :
    coeff H p x k (fun _ => c) i = if i = k then c else 0 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  have hinv : coeff H p x k (fun _ => 1) i = if i = k then 1 else 0 := by
    change ((baseMatrix H p x)⁻¹ * baseMatrix H p x) i k = _
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]
  unfold coeff
  rw [column_const, Matrix.mulVec_smul]
  change c * coeff H p x k (fun _ => 1) i = _
  rw [hinv]
  split_ifs <;> simp

/-- Inverse-basis coordinates obey the same column identity. -/
theorem coeff_identity [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) :
    coeff H p x k F = coeff H p x k (resample H p (x k) (earlier x k) F) +
      ∑ j, if k < j then coeff H p x j (residualMean H p (x k) (earlier x k) · F) else 0 := by
  have hc : column H p x k F = column H p x k (resample H p (x k) (earlier x k) F) +
      ∑ j, if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) else 0 := by
    funext i
    simpa only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] using
      column_identity H p x k i F
  unfold coeff
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : k < j <;> simp [h]

/-- Convergence passes to inverse-basis coordinates by finite linearity. -/
theorem coeff_tendsto {n : ℕ} (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (x : Fin n → V) (k i : Fin n) (F : ℕ → Set V → ℝ) (c : ℝ)
    (h : ∀ U ∈ ClusterDomain (x k) (earlier x k),
      Tendsto (fun t => F t U) atTop (nhds c)) :
    Tendsto (fun t => coeff H p x k (F t) i) atTop
      (nhds (coeff H p x k (fun _ => c) i)) := by
  unfold coeff Matrix.mulVec dotProduct
  exact tendsto_finsetSum _ (fun j _ => tendsto_const_nhds.mul (column_tendsto H p x k j F c h))

theorem coeff_nonneg [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) (F : Set V → ℝ)
    (hF0 : ∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ F U)
    (hFm : MonotoneOn F (ClusterDomain (x k) (earlier x k))) (i : Fin n) :
    0 ≤ coeff H p x k F i := by
  suffices aux : ∀ m : ℕ, ∀ k : Fin n, n - k.val = m → ∀ F : Set V → ℝ,
      (∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ F U) →
      MonotoneOn F (ClusterDomain (x k) (earlier x k)) →
      ∀ i, 0 ≤ coeff H p x k F i by
    exact aux (n - k.val) k rfl F hF0 hFm i
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k hkm F hF0 hFm i
    let G : ℕ → Set V → ℝ := fun t => (resample H p (x k) (earlier x k))^[t] F
    have hG0 (t : ℕ) : ∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ G t U := by
      induction t with
      | zero => exact hF0
      | succ t ht =>
        intro U hU
        simpa only [G, Function.iterate_succ_apply'] using
          (resample_nonneg (H := H) (p := p) ht hU)
    have hGm (t : ℕ) : MonotoneOn (G t) (ClusterDomain (x k) (earlier x k)) := by
      induction t with
      | zero => exact hFm
      | succ t ht =>
        simpa only [G, Function.iterate_succ_apply'] using
          (resample_monotone (H := H) (p := p) ht)
    have hstep (t : ℕ) : coeff H p x k (G (t + 1)) i ≤ coeff H p x k (G t) i := by
      have hid := congrFun (coeff_identity H p x k (G t)) i
      simp only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] at hid
      have hr : 0 ≤ ∑ j : Fin n, if k < j then
          coeff H p x j (residualMean H p (x k) (earlier x k) · (G t)) i else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs with hkj
        · have hmj : n - j.val < m := by
            have hjn := j.isLt
            have hkn := k.isLt
            have hkjv : k.val < j.val := hkj
            omega
          apply ih (n - j.val) hmj j rfl _
          · intro U hU
            apply residualMean_nonneg _ (hGm t)
            intro hu
            exact Set.disjoint_left.mp hU.2 hu ⟨k, hkj, rfl⟩
          · intro U hU U' hU' hUU
            apply residualMean_mono hUU _ (hGm t)
            intro hu
            exact Set.disjoint_left.mp hU'.2 hu ⟨k, hkj, rfl⟩
        · exact le_rfl
      have heq : G (t + 1) = resample H p (x k) (earlier x k) (G t) :=
        Function.iterate_succ_apply' _ _ _
      rw [heq]
      linarith
    have hant : Antitone (fun t => coeff H p x k (G t) i) :=
      antitone_nat_of_succ_le hstep
    obtain ⟨c, hc, hlim⟩ := resample_tendsto_constant H p hp (x k) (earlier x k)
      (root_notin_earlier hx k) F hF0
    have hl := coeff_tendsto H p x k i G c hlim
    have hle : coeff H p x k (fun _ => c) i ≤ coeff H p x k F i := by
      apply le_of_tendsto hl
      exact Filter.Eventually.of_forall (fun t => hant (Nat.zero_le t))
    apply le_trans _ hle
    rw [coeff_const H p hp x hx]
    split_ifs <;> positivity

/-- The observable that a cluster contains another listed vertex. -/
noncomputable def hitsOther {n : ℕ} (x : Fin n → V) (k : Fin n) (U : Set V) : ℝ :=
  if ∃ j, j ≠ k ∧ x j ∈ U then 1 else 0

noncomputable def isolatedMass {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) : ℝ :=
  ∫ ω, if ∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j) then 1 else 0 ∂law p

omit [Fintype E] in
theorem isolated_firstRoot {n : ℕ} {H : Hypergraph V E} {x : Fin n → V}
    {k : Fin n} {ω : E → Bool}
    (h : ∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j)) : firstRoot H x ω ∅ k k := by
  refine ⟨Set.disjoint_left.mpr ?_, .refl⟩
  rintro y hy ⟨j, hj, rfl⟩
  exact h j (ne_of_lt hj) hy

theorem isolatedMass_pos {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < isolatedMass H p x k := by
  have hi : (∫ ω : E → Bool, if ω = (fun _ => false) then (1:ℝ) else 0 ∂law p) =
      (law p).real {fun _ => false} := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := law p) (s := {fun _ => false}) (measurableSet_singleton _))
  apply (all_closed_mass_pos p hp).trans_le
  rw [← hi]
  unfold isolatedMass
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  by_cases hc : ω = (fun _ => false)
  · subst ω
    have hf : ∀ j, j ≠ k → ¬Connected H (fun _ => false) ∅ (x k) (x j) := by
      intro j hj hc
      have : x j ∈ cluster H (fun _ => false) ∅ (x k) := hc
      rw [cluster_all_closed] at this
      exact hj (hx this)
    dsimp only
    rw [ite_eq_left hf]
    simp
  · simp only [hc, ite_false]
    split_ifs <;> norm_num

theorem column_hitsOther {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) :
    column H p x k (hitsOther x k) = column H p x k (fun _ => 1) -
      Pi.single k (isolatedMass H p x k) := by
  classical
  funext i
  change column H p x k (hitsOther x k) i = column H p x k (fun _ => 1) i - _
  by_cases hik : i = k
  · subst i
    simp only [Pi.single_eq_same]
    unfold column isolatedMass
    rw [← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    by_cases ho : ∃ j, j ≠ k ∧ x j ∈ cluster H ω ∅ (x k)
    · have hn : ¬∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j) := by
        obtain ⟨j, hj, hc⟩ := ho
        exact fun h => h j hj hc
      simp [hitsOther, ho, hn]
    · have hy : ∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j) := by
        intro j hj hc
        exact ho ⟨j, hj, hc⟩
      simp only [hitsOther, ite_eq_right ho, ite_eq_left hy, ite_eq_left (isolated_firstRoot hy)]
      norm_num
  · simp only [Pi.single_eq_of_ne hik, sub_zero]
    unfold column
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hf : firstRoot H x ω ∅ k i
    · simp [hf, hitsOther, show ∃ j, j ≠ k ∧ x j ∈ cluster H ω ∅ (x k) from ⟨i, hik, hf.2⟩]
    · simp [hf]

/-- The inverse cluster matrix has nonpositive off-diagonal entries. -/
theorem inverse_offdiag_nonpos [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) {k i : Fin n} (hik : i ≠ k) :
    (baseMatrix H p x)⁻¹ i k ≤ 0 := by
  have hF0 : ∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ hitsOther x k U := by
    intro U _
    unfold hitsOther
    split_ifs <;> norm_num
  have hFm : MonotoneOn (hitsOther x k) (ClusterDomain (x k) (earlier x k)) := by
    intro U _ U' _ hUU
    unfold hitsOther
    split_ifs with h h'
    · rfl
    · obtain ⟨j, hj, hc⟩ := h
      exact (h' ⟨j, hj, hUU hc⟩).elim
    · norm_num
    · rfl
  have hc := coeff_nonneg H p hp x hx k (hitsOther x k) hF0 hFm i
  have heq : coeff H p x k (hitsOther x k) i =
      -(baseMatrix H p x)⁻¹ i k * isolatedMass H p x k := by
    unfold coeff
    rw [column_hitsOther, Matrix.mulVec_sub]
    change coeff H p x k (fun _ => 1) i - _ = _
    rw [coeff_const H p hp x hx, ite_eq_right hik]
    rw [Matrix.mulVec_single]
    simp
  rw [heq] at hc
  have ha := isolatedMass_pos H p hp x hx k
  nlinarith

/-- The first-listed cluster columns partition every row. -/
theorem baseMatrix_mulVec_one {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) :
    baseMatrix H p x *ᵥ (fun _ => 1) = fun _ => 1 := by
  funext i
  unfold Matrix.mulVec dotProduct baseMatrix column
  simp only [mul_one]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have hs (ω : E → Bool) := sum_firstRoot H x ω ∅ i (fun _ => (1:ℝ))
  simp_rw [hs]
  simp

/-- Consequently each row of the inverse also sums to one. -/
theorem inverse_mulVec_one {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) :
    (baseMatrix H p x)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  calc
    _ = (baseMatrix H p x)⁻¹ *ᵥ (baseMatrix H p x *ᵥ (fun _ => 1)) :=
      congrArg (fun v => (baseMatrix H p x)⁻¹ *ᵥ v) (baseMatrix_mulVec_one H p x).symm
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- Expectation vector of a cluster observable at the listed vertices. -/
noncomputable def expectationVector {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (F : Set V → ℝ) : Fin n → ℝ :=
  fun i => ∫ ω, F (cluster H ω ∅ (x i)) ∂law p

theorem expectationVector_eq_sum_columns {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (F : Set V → ℝ) :
    expectationVector H p x F = ∑ k, column H p x k F := by
  funext i
  simp only [Finset.sum_apply, column]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [sum_firstRoot]
  rfl

/-- Increasing observables give nonnegative inverse expectation vectors. -/
theorem inverse_expectation_nonneg [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (F : Set V → ℝ)
    (hF0 : ∀ U, 0 ≤ F U) (hFm : Monotone F) (i : Fin n) :
    0 ≤ ((baseMatrix H p x)⁻¹ *ᵥ expectationVector H p x F) i := by
  rw [expectationVector_eq_sum_columns, Matrix.mulVec_sum]
  simp only [Finset.sum_apply]
  exact Finset.sum_nonneg (fun k _ => coeff_nonneg H p hp x hx k F
    (fun U _ => hF0 U) (hFm.monotoneOn _) i)

/-- The final diagonal entry of the inverse is reciprocal to the probability
of avoiding all preceding listed vertices. -/
theorem inverse_last_diag_mul {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n + 1) → V) (hx : Function.Injective x) :
    (baseMatrix H p x)⁻¹ (Fin.last n) (Fin.last n) *
      baseMatrix H p x (Fin.last n) (Fin.last n) = 1 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
    M (Fin.last n) (Fin.last n)) (Matrix.nonsing_inv_mul (baseMatrix H p x) hdet)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_single (Fin.last n)] at h
  · exact h
  · intro j _ hj
    have hjl : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hj
    exact mul_eq_zero_of_right _ (baseMatrix_lowerTriangular H p x hjl)
  · simp

/-- Scalar consequence of the cone: a target observable large at every earlier
listed vertex must have a correspondingly large expectation at the last one. -/
theorem expectation_comparison [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n + 1) → V) (hx : Function.Injective x) (F : Set V → ℝ)
    (hF0 : ∀ U, 0 ≤ F U) (hFm : Monotone F) (b : ℝ)
    (hb : ∀ j ≠ Fin.last n, b ≤ expectationVector H p x F j) :
    b * (1 - baseMatrix H p x (Fin.last n) (Fin.last n)) ≤
      expectationVector H p x F (Fin.last n) := by
  classical
  let l := Fin.last n
  let M := baseMatrix H p x
  let y := expectationVector H p x F
  have hrow : (∑ j, M⁻¹ l j) = 1 := by
    have h := congrFun (inverse_mulVec_one H p hp x hx) l
    simpa [Matrix.mulVec, dotProduct, M] using h
  have hpos : 0 ≤ ∑ j, M⁻¹ l j * y j :=
    inverse_expectation_nonneg H p hp x hx F hF0 hFm l
  have hdiff : (∑ j, M⁻¹ l j * (y j - b)) ≤ M⁻¹ l l * (y l - b) := by
    calc
      _ ≤ ∑ j, if j = l then M⁻¹ l l * (y l - b) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j = l
        · subst j; simp
        · rw [ite_eq_right hj]
          exact mul_nonpos_of_nonpos_of_nonneg
            (inverse_offdiag_nonpos H p hp x hx (Ne.symm hj)) (sub_nonneg.mpr (hb j hj))
      _ = _ := by simp
  simp_rw [mul_sub] at hdiff
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul] at hdiff
  have hlow : -b ≤ M⁻¹ l l * (y l - b) := by linarith
  have hd : 0 < M l l := baseMatrix_diag_pos H p hp x hx l
  have hprod : M⁻¹ l l * M l l = 1 := inverse_last_diag_mul H p hp x hx
  have hh := mul_le_mul_of_nonneg_right hlow hd.le
  have heq : M⁻¹ l l * (y l - b) * M l l = y l - b := by
    calc
      _ = (M⁻¹ l l * M l l) * (y l - b) := by ring
      _ = y l - b := by rw [hprod, one_mul]
  rw [heq] at hh
  change b * (1 - M l l) ≤ y l
  linarith

/-- Real probability of any event in the finite bit space. -/
noncomputable def eventProb (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) : ℝ :=
  ∫ ω, if P ω then 1 else 0 ∂law p

theorem eventProb_eq_real (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p P = (law p).real {ω | P ω} := by
  simpa [eventProb, Set.indicator] using
    (integral_indicator_one (μ := law p) (s := {ω | P ω}) (Set.toFinite _).measurableSet)

theorem eventProb_compl (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p (fun ω => ¬P ω) = 1 - eventProb p P := by
  unfold eventProb
  calc
    _ = ∫ ω, (1:ℝ) - if P ω then 1 else 0 ∂law p := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : P ω <;> simp [h]
    _ = _ := by
      rw [integral_sub (Integrable.of_finite) (Integrable.of_finite)]
      simp

/-- Joint cluster-hit observable, preserving both target sets. -/
noncomputable def jointObservable (A T U : Set V) : ℝ :=
  if (∃ a ∈ A, a ∈ U) ∧ (∃ t ∈ T, t ∈ U) then 1 else 0

omit [Fintype E] in
theorem jointObservable_nonneg (A T U : Set V) : 0 ≤ jointObservable A T U := by
  unfold jointObservable
  split_ifs <;> norm_num

omit [Fintype E] in
theorem jointObservable_monotone (A T : Set V) : Monotone (jointObservable A T) := by
  intro U U' hUU
  unfold jointObservable
  split_ifs with h h'
  · rfl
  · obtain ⟨⟨a, ha, hau⟩, ⟨t, ht, htu⟩⟩ := h
    exact (h' ⟨⟨a, ha, hUU hau⟩, ⟨t, ht, hUU htu⟩⟩).elim
  · norm_num
  · rfl

theorem expectation_jointObservable {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (A T : Set V) (i : Fin n) :
    expectationVector H p x (jointObservable A T) i =
      eventProb p (fun ω => Meets H ω ∅ (x i) A ∧ Meets H ω ∅ (x i) T) := by
  unfold expectationVector eventProb
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  unfold jointObservable Meets cluster
  split_ifs <;> first | rfl | simp_all

theorem expectation_jointObservable_of_mem {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (A T : Set V) (i : Fin n) (hi : x i ∈ A) :
    expectationVector H p x (jointObservable A T) i =
      eventProb p (fun ω => Meets H ω ∅ (x i) T) := by
  rw [expectation_jointObservable]
  unfold eventProb
  have ha (ω : E → Bool) : Meets H ω ∅ (x i) A := ⟨x i, hi, .refl⟩
  simp only [ha, true_and]

theorem last_diagonal_avoidance {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin (n+1) → V) :
    baseMatrix H p x (Fin.last n) (Fin.last n) =
      1 - eventProb p (fun ω => Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n))) := by
  rw [← eventProb_compl]
  unfold baseMatrix column eventProb
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have hf : firstRoot H x ω ∅ (Fin.last n) (Fin.last n) ↔
      ¬Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n)) := by
    constructor
    · rintro ⟨hd, _⟩ ⟨a, ha, hc⟩
      exact Set.disjoint_left.mp hd hc ha
    · intro h
      refine ⟨Set.disjoint_left.mpr ?_, .refl⟩
      intro a hc ha
      exact h ⟨a, ha, hc⟩
  by_cases h : Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n))
  · simp only [hf, h, not_true_eq_false, ite_false]
  · simp only [hf, h, not_false_eq_true, ite_true]

theorem joint_comparison_list [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n+1) → V) (hx : Function.Injective x) (T : Set V) (b : ℝ)
    (hb : ∀ j ≠ Fin.last n, b ≤ eventProb p (fun ω => Meets H ω ∅ (x j) T)) :
    b * eventProb p (fun ω => Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n))) ≤
      eventProb p (fun ω => Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n)) ∧
        Meets H ω ∅ (x (Fin.last n)) T) := by
  have h := expectation_comparison H p hp x hx
    (jointObservable (earlier x (Fin.last n)) T)
    (jointObservable_nonneg _ _) (jointObservable_monotone _ _) b (by
      intro j hj
      have hm : x j ∈ earlier x (Fin.last n) :=
        ⟨j, Fin.lt_last_iff_ne_last.mpr hj, rfl⟩
      rw [expectation_jointObservable_of_mem H p x (earlier x (Fin.last n)) T j hm]
      exact hb j hj)
  rw [last_diagonal_avoidance] at h
  simpa only [sub_sub_cancel, expectation_jointObservable] using h

omit [Fintype E] in

theorem exists_target_list [Fintype V] (A : Set V) (o : V) (ho : o ∉ A) :
    ∃ n : ℕ, ∃ x : Fin (n+1) → V, Function.Injective x ∧
      x (Fin.last n) = o ∧ earlier x (Fin.last n) = A := by
  classical
  let n := Fintype.card A
  let e : Fin n ≃ A := (Fintype.equivFin A).symm
  let x : Fin (n+1) → V := Fin.snoc (fun i => (e i).1) o
  refine ⟨n, x, ?_, by simp [x], ?_⟩
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact fun _ => rfl
      | cast j =>
        intro h
        have heq : o = (e j).1 := by simpa [x] using h
        exact (ho (heq ▸ (e j).2)).elim
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        intro h
        have heq : (e i).1 = o := by simpa [x] using h
        exact (ho (heq ▸ (e i).2)).elim
      | cast j =>
        intro h
        have heq : (e i).1 = (e j).1 := by simpa [x] using h
        exact congrArg Fin.castSucc (e.injective (Subtype.ext heq))
  · ext a
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj.ne
      simp [x, (e i).2]
    · intro ha
      let i := e.symm ⟨a, ha⟩
      refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
      simp [x, i]

/-- The joint connection inequality for arbitrary finite targets, first for
strictly subunit hyperedge probabilities. -/
theorem joint_comparison_of_lt_one [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (o : V) (A T : Set V) (b : ℝ)
    (hb : ∀ a ∈ A, b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    b * eventProb p (fun ω => Meets H ω ∅ o A) ≤
      eventProb p (fun ω => Meets H ω ∅ o A ∧ Meets H ω ∅ o T) := by
  by_cases ho : o ∈ A
  · have ha (ω : E → Bool) : Meets H ω ∅ o A := ⟨o, ho, .refl⟩
    have h := hb o ho
    simpa [eventProb, ha] using h
  · obtain ⟨n, x, hx, hxo, hxA⟩ := exists_target_list A o ho
    have h := joint_comparison_list H p hp x hx T b (by
      intro j hj
      apply hb
      rw [← hxA]
      exact ⟨j, Fin.lt_last_iff_ne_last.mpr hj, rfl⟩)
    simpa only [hxo, hxA] using h

/-- Polynomial weight of a specified finite configuration. -/
theorem law_mass (p : E → Set.Icc (0 : ℝ) 1) (ω : E → Bool) :
    (law p).real {ω} = ∏ e, if ω e = true then (p e : ℝ) else 1 - (p e : ℝ) := by
  classical
  rw [Measure.real_def, law, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {ω e} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases he : ω e <;> simp [unitInterval.coe_symm_eq]

/-- All finite event probabilities are continuous in all parameters, including
at configurations with deterministic bits. -/
theorem eventProb_tendsto (p : E → Set.Icc (0 : ℝ) 1)
    (q : ℕ → E → Set.Icc (0 : ℝ) 1)
    (hq : ∀ e, Tendsto (fun n => (q n e : ℝ)) atTop (nhds (p e : ℝ)))
    (P : (E → Bool) → Prop) :
    Tendsto (fun n => eventProb (q n) P) atTop (nhds (eventProb p P)) := by
  simp_rw [eventProb, integral_fintype (Integrable.of_finite), law_mass]
  apply tendsto_finsetSum
  intro ω _
  apply Filter.Tendsto.smul _ tendsto_const_nhds
  apply tendsto_finsetProd
  intro e _
  by_cases he : ω e = true
  · simpa [he] using hq e
  · simpa [he] using tendsto_const_nhds.sub (hq e)

/-- Strictly subunit parameters approaching arbitrary permitted parameters. -/
noncomputable def thinParameter (p : E → Set.Icc (0 : ℝ) 1) (n : ℕ) (e : E) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨((n : ℝ) / ((n : ℝ) + 1)) * (p e : ℝ), by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hr0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := div_nonneg hn (by positivity)
    have hr1 : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
      (div_lt_one (by positivity)).mpr (by linarith)
    exact ⟨mul_nonneg hr0 (p e).2.1,
      (mul_le_of_le_one_right hr0 (p e).2.2).trans hr1.le⟩⟩

omit [Fintype E] in
theorem thinParameter_lt_one (p : E → Set.Icc (0 : ℝ) 1) (n : ℕ) (e : E) :
    (thinParameter p n e : ℝ) < 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hr0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := div_nonneg hn (by positivity)
  have hr1 : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact (mul_le_of_le_one_right hr0 (p e).2.2).trans_lt hr1

omit [Fintype E] in
theorem thinParameter_tendsto (p : E → Set.Icc (0 : ℝ) 1) (e : E) :
    Tendsto (fun n => (thinParameter p n e : ℝ)) atTop (nhds (p e : ℝ)) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop 1
  simpa only [thinParameter, one_mul] using h.mul_const (p e : ℝ)

theorem joint_comparison [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ)
    (hb : ∀ a ∈ A, b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    b * eventProb p (fun ω => Meets H ω ∅ o A) ≤
      eventProb p (fun ω => Meets H ω ∅ o A ∧ Meets H ω ∅ o T) := by
  let q := thinParameter p
  let d : ℕ → ℝ := fun n => ∑ a : V,
    |eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)|
  have hd : Tendsto d atTop (nhds 0) := by
    have h : Tendsto d atTop (nhds (∑ _a : V, (0:ℝ))) := by
      apply tendsto_finsetSum
      intro a _
      simpa only [sub_self, abs_zero] using
        ((eventProb_tendsto p q (thinParameter_tendsto p) (fun ω => Meets H ω ∅ a T)).sub
          (tendsto_const_nhds (x := eventProb p (fun ω => Meets H ω ∅ a T)))).abs
    simpa using h
  have hbound (n : ℕ) (a : V) :
      eventProb p (fun ω => Meets H ω ∅ a T) - eventProb (q n) (fun ω => Meets H ω ∅ a T) ≤ d n := by
    apply le_trans (show eventProb p (fun ω => Meets H ω ∅ a T) -
      eventProb (q n) (fun ω => Meets H ω ∅ a T) ≤
      |eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)| by
        simpa only [neg_sub] using neg_le_abs
          (eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)))
    change |eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)| ≤
      ∑ j : V, |eventProb (q n) (fun ω => Meets H ω ∅ j T) - eventProb p (fun ω => Meets H ω ∅ j T)|
    exact Finset.single_le_sum (fun j _ => abs_nonneg
      (eventProb (q n) (fun ω => Meets H ω ∅ j T) - eventProb p (fun ω => Meets H ω ∅ j T)))
      (Finset.mem_univ a)
  have hi (n : ℕ) := joint_comparison_of_lt_one H (q n) (thinParameter_lt_one p n)
    o A T (b - d n) (by intro a ha; linarith [hb a ha, hbound n a])
  have hl := ((tendsto_const_nhds (x := b)).sub hd).mul
    (eventProb_tendsto p q (thinParameter_tendsto p) (fun ω => Meets H ω ∅ o A))
  have hr := eventProb_tendsto p q (thinParameter_tendsto p)
    (fun ω => Meets H ω ∅ o A ∧ Meets H ω ∅ o T)
  have h := le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall hi)
  simpa only [sub_zero] using h

theorem eventProb_nonneg (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    0 ≤ eventProb p P := by
  rw [eventProb_eq_real]
  exact measureReal_nonneg

theorem eventProb_le_one (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p P ≤ 1 := by
  rw [eventProb_eq_real]
  exact measureReal_le_one

theorem eventProb_mono (p : E → Set.Icc (0 : ℝ) 1) (P Q : (E → Bool) → Prop)
    (h : ∀ ω, P ω → Q ω) : eventProb p P ≤ eventProb p Q := by
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · simp only [hp, ite_false]
    split_ifs <;> norm_num

theorem eventProb_failure (p : E → Set.Icc (0 : ℝ) 1) (P Q : (E → Bool) → Prop) :
    eventProb p (fun ω => P ω ∧ ¬Q ω) = eventProb p P - eventProb p (fun ω => P ω ∧ Q ω) := by
  unfold eventProb
  rw [← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

/-- The strengthened hyperedge failure estimate, including all fixed-bit laws. -/
theorem failure_comparison_mul [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ)
    (hb : ∀ a ∈ A, 1 - b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    eventProb p (fun ω => Meets H ω ∅ o A ∧ ¬Meets H ω ∅ o T) ≤
      b * eventProb p (fun ω => Meets H ω ∅ o A) := by
  rw [eventProb_failure]
  have h := joint_comparison H p o A T (1-b) hb
  nlinarith

theorem failure_comparison [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ a ∈ A, 1 - b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    eventProb p (fun ω => Meets H ω ∅ o A ∧ ¬Meets H ω ∅ o T) ≤ b := by
  apply (failure_comparison_mul H p o A T b hb).trans
  exact mul_le_of_le_one_right hb0 (eventProb_le_one p _)

theorem joint_comparison_ennreal [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ≥0∞)
    (hA : A.Nonempty) (hb : ∀ a ∈ A, b ≤ law p {ω | Meets H ω ∅ a T}) :
    law p {ω | Meets H ω ∅ o A} * b ≤
      law p {ω | Meets H ω ∅ o A ∧ Meets H ω ∅ o T} := by
  have hbn : b ≠ ⊤ := by
    obtain ⟨a, ha⟩ := hA
    exact ne_top_of_le_ne_top (measure_ne_top (law p) _) (hb a ha)
  have hr := joint_comparison H p o A T b.toReal (by
    intro a ha
    rw [eventProb_eq_real, Measure.real_def]
    exact ENNReal.toReal_mono (measure_ne_top (law p) _) (hb a ha))
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (measure_ne_top (law p) _) hbn)
    (measure_ne_top (law p) _)).mp
  simpa only [ENNReal.toReal_mul, eventProb_eq_real, Measure.real_def, mul_comm] using hr

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

/-- The connector presentation uses two directed copies of each undirected
edge; duplication does not change any reachable starred vertex. Nonedges are
isolated connector nodes. -/
abbrev Node (V : Type uV) := V ⊕ (V × V)

def stars : Hypergraph (Node V) V := fun x z =>
  match z with
  | Sum.inl y => y = x
  | Sum.inr e => G.Adj e.1 e.2 ∧ (e.1 = x ∨ e.2 = x)

def OpenAdj (ω : V → Bool) (x y : V) : Prop :=
  G.Adj x y ∧ ω x = true ∧ ω y = true

def Connected (ω : V → Bool) (x y : V) : Prop :=
  ω x = true ∧ Relation.ReflTransGen (OpenAdj G ω) x y

def Meets (ω : V → Bool) (x : V) (T : Set V) : Prop :=
  ∃ y ∈ T, Connected G ω x y

theorem connected_refl {ω : V → Bool} {x : V} (hx : ω x = true) :
    Connected G ω x x := ⟨hx, .refl⟩

theorem connected_open_right {ω : V → Bool} {x y : V}
    (h : Connected G ω x y) : ω y = true := by
  obtain ⟨hx, h⟩ := h
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact hab.2.2

theorem connected_extend {ω : V → Bool} {o x y : V}
    (h : Connected G ω o x) (hxy : G.Adj x y) (hy : ω y = true) :
    Connected G ω o y :=
  ⟨h.1, h.2.tail ⟨hxy, connected_open_right G h, hy⟩⟩

theorem connected_to_stars {ω : V → Bool} {x y : V}
    (h : Connected G ω x y) :
    HyperedgeComparison.Connected (stars G) ω ∅ (Sum.inl x) (Sum.inl y) := by
  obtain ⟨_, h⟩ := h
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    apply ih.trans
    apply Relation.ReflTransGen.trans (b := Sum.inr (a,b))
    · exact Relation.ReflTransGen.single
        ⟨a, hab.2.1, Set.disjoint_empty _, rfl, hab.1, Or.inl rfl⟩
    · exact Relation.ReflTransGen.single
        ⟨b, hab.2.2, Set.disjoint_empty _, ⟨hab.1, Or.inr rfl⟩, rfl⟩

/-- Predicate propagated along a hyperedge path. It explicitly retains the
site-open condition, including in the zero-edge case. -/
def Supported (ω : V → Bool) (o : V) : Node V → Prop
  | Sum.inl x => Connected G ω o x
  | Sum.inr e => G.Adj e.1 e.2 ∧ (Connected G ω o e.1 ∨ Connected G ω o e.2)

theorem supported_label {ω : V → Bool} {o x : V} {z : Node V}
    (h : Supported G ω o z) (hz : z ∈ stars G x) (hx : ω x = true) :
    Connected G ω o x := by
  cases z with
  | inl y =>
    change y = x at hz
    subst y
    exact h
  | inr e =>
    obtain ⟨u,v⟩ := e
    obtain ⟨huv, hm⟩ := hz
    obtain ⟨_, hc | hc⟩ := h
    · rcases hm with rfl | rfl
      · exact hc
      · exact connected_extend G hc huv hx
    · rcases hm with rfl | rfl
      · exact connected_extend G hc huv.symm hx
      · exact hc

theorem supported_of_label {ω : V → Bool} {o x : V} {z : Node V}
    (h : Connected G ω o x) (hz : z ∈ stars G x) : Supported G ω o z := by
  cases z with
  | inl y =>
    change y = x at hz
    subst y
    exact h
  | inr e =>
    obtain ⟨u,v⟩ := e
    obtain ⟨huv, hm⟩ := hz
    refine ⟨huv, ?_⟩
    rcases hm with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h

theorem connected_of_stars {ω : V → Bool} {x y : V} (hx : ω x = true)
    (h : HyperedgeComparison.Connected (stars G) ω ∅ (Sum.inl x) (Sum.inl y)) :
    Connected G ω x y := by
  have hp : ∀ {z z' : Node V}, Supported G ω x z →
      HyperedgeComparison.Connected (stars G) ω ∅ z z' → Supported G ω x z' := by
    intro z z' hs hh
    induction hh with
    | refl => exact hs
    | @tail a b _ hab ih =>
      obtain ⟨e,he,_,ha,hb⟩ := hab
      exact supported_of_label G (supported_label G ih ha he) hb
  exact hp (z := Sum.inl x) (z' := Sum.inl y) (connected_refl G hx) h

theorem meets_to_stars {ω : V → Bool} {o : V} {T : Set V}
    (h : Meets G ω o T) :
    HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' T) := by
  obtain ⟨t,ht,hc⟩ := h
  exact ⟨Sum.inl t, ⟨t,ht,rfl⟩, connected_to_stars G hc⟩

theorem meets_of_stars {ω : V → Bool} {o : V} {T : Set V} (ho : ω o = true)
    (h : HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' T)) :
    Meets G ω o T := by
  obtain ⟨_,⟨t,ht,rfl⟩,hc⟩ := h
  exact ⟨t,ht,connected_of_stars G ho hc⟩

theorem failure_subset_hyperedge {ω : V → Bool} {o : V} {A T : Set V}
    (h : Meets G ω o A ∧ ¬Meets G ω o T) :
    HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' A) ∧
    ¬HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' T) := by
  refine ⟨meets_to_stars G h.1, ?_⟩
  intro ht
  obtain ⟨_,_,hc⟩ := h.1
  exact h.2 (meets_of_stars G hc.1 ht)

end Site

theorem site_failure_comparison [Fintype V] (G : SimpleGraph V)
    (p : V → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ a ∈ A, 1 - b ≤ eventProb p (fun ω => Site.Meets G ω a T)) :
    eventProb p (fun ω => Site.Meets G ω o A ∧ ¬Site.Meets G ω o T) ≤ b := by
  apply (eventProb_mono p _ _ (fun _ => Site.failure_subset_hyperedge G)).trans
  apply failure_comparison (Site.stars G) p (Sum.inl o) (Sum.inl '' A) (Sum.inl '' T) b hb0
  rintro _ ⟨a,ha,rfl⟩
  exact (hb a ha).trans (eventProb_mono p _ _ (fun _ => Site.meets_to_stars G))

end HyperedgeComparison

end OAI
