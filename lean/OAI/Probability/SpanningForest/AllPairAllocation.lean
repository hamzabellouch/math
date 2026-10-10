import OAI.Probability.SpanningForest.GraphBalls
import OAI.Probability.SpanningForest.GraphDomain
import OAI.Probability.SpanningForest.EdgeAllocationMeasurable

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem336.AllPairAllocation

private def radiusPredicate (G : GraphCode) (u v n : ℕ) : Prop :=
  withinRadius G n u v ∨ ¬ ∃ m, withinRadius G m u v

private theorem exists_radiusPredicate (G : GraphCode) (u v : ℕ) :
    ∃ n, radiusPredicate G u v n := by
  classical
  by_cases h : ∃ n, withinRadius G n u v
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr h⟩

def radius (G : GraphCode) (u v : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_radiusPredicate G u v)

theorem withinRadius_radius (G : GraphCode) (hc : GraphConnected G) (u v : ℕ) :
    withinRadius G (radius G u v) u v := by
  classical
  have h := Nat.find_spec (exists_radiusPredicate G u v)
  exact h.resolve_right (not_not.mpr (exists_withinRadius G hc u v))

theorem radius_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) (u v : ℕ) :
    radius (relabelGraph σ G) (σ u) (σ v) = radius G u v := by
  classical
  unfold radius
  apply Nat.find_congr'
  intro n
  simp only [radiusPredicate, withinRadius_relabel]

theorem measurable_radius (u v : ℕ) :
    Measurable (fun G : GraphCode => radius G u v) := by
  classical
  unfold radius
  apply measurable_find
  intro n
  simp only [radiusPredicate, Set.ofPred_or]
  refine (measurableSet_withinRadius n u v).union ?_
  convert (MeasurableSet.iUnion (fun m => measurableSet_withinRadius m u v)).compl using 1
  ext G
  simp

def ballRank (G : GraphCode) (key : ℕ → ℝ) (n u v : ℕ) : ℕ :=
  Set.ncard {w | withinRadius G n u w ∧ key w < key v}

theorem ballRank_strictMono {G : GraphCode} (hf : GraphLocallyFinite G)
    {key : ℕ → ℝ} {n u v w : ℕ} (hv : withinRadius G n u v)
    (hvw : key v < key w) : ballRank G key n u v < ballRank G key n u w := by
  apply Set.ncard_lt_ncard
  · refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro x hx
      exact ⟨hx.1, hx.2.trans hvw⟩
    · intro heq
      have hmem : v ∈ {x | withinRadius G n u x ∧ key x < key w} := ⟨hv, hvw⟩
      rw [← heq] at hmem
      exact (lt_irrefl (key v)) hmem.2
  · exact (finite_withinRadius G hf n u).subset (fun _ h => h.1)

theorem ballRank_injOn {G : GraphCode} (hf : GraphLocallyFinite G)
    {key : ℕ → ℝ} (hk : Function.Injective key) (n u : ℕ) :
    Set.InjOn (ballRank G key n u) {v | withinRadius G n u v} := by
  intro v hv w hw hrank
  apply hk
  rcases lt_trichotomy (key v) (key w) with h | h | h
  · exact False.elim ((ne_of_lt (ballRank_strictMono hf hv h)) hrank)
  · exact h
  · exact False.elim ((ne_of_lt (ballRank_strictMono hf hw h)) hrank.symm)

def coordinate (G : GraphCode) (key : ℕ → ℝ) (e : EdgeCode) : ℕ × (ℕ × ℕ) :=
  let u := EdgeAllocation.source key e
  let v := EdgeAllocation.target key e
  let n := radius G u v
  (u, n, ballRank G key n u v)

theorem coordinate_injective {G : GraphCode} (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) {key : ℕ → ℝ} (hk : Function.Injective key) :
    Function.Injective (coordinate G key) := by
  intro e f h
  have hu : EdgeAllocation.source key e = EdgeAllocation.source key f := congrArg Prod.fst h
  have hn : radius G (EdgeAllocation.source key e) (EdgeAllocation.target key e) =
      radius G (EdgeAllocation.source key f) (EdgeAllocation.target key f) :=
    congrArg (fun x => x.2.1) h
  have hr : ballRank G key
      (radius G (EdgeAllocation.source key e) (EdgeAllocation.target key e))
      (EdgeAllocation.source key e) (EdgeAllocation.target key e) =
    ballRank G key
      (radius G (EdgeAllocation.source key f) (EdgeAllocation.target key f))
      (EdgeAllocation.source key f) (EdgeAllocation.target key f) :=
    congrArg (fun x => x.2.2) h
  rw [← hn, ← hu] at hr
  have hvf : withinRadius G
      (radius G (EdgeAllocation.source key e) (EdgeAllocation.target key e))
      (EdgeAllocation.source key e) (EdgeAllocation.target key f) := by
    rw [hn, hu]
    exact withinRadius_radius G hc _ _
  have hv := ballRank_injOn hf hk _ _ (withinRadius_radius G hc _ _) hvf hr
  apply Subtype.ext
  rw [← EdgeAllocation.rawPair_source_target key e,
    ← EdgeAllocation.rawPair_source_target key f, hu, hv]

theorem ballRank_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) (key : ℕ → ℝ)
    (n u v : ℕ) :
    ballRank (relabelGraph σ G) (relabelLabels σ key) n (σ u) (σ v) =
      ballRank G key n u v := by
  unfold ballRank
  have hs : {w | withinRadius (relabelGraph σ G) n (σ u) w ∧
      relabelLabels σ key w < relabelLabels σ key (σ v)} =
      σ '' {w | withinRadius G n u w ∧ key w < key v} := by
    ext w
    constructor
    · intro h
      refine ⟨σ.symm w, ?_, σ.apply_symm_apply w⟩
      constructor
      · exact (withinRadius_relabel σ G n u (σ.symm w)).mp (by simpa using h.1)
      · simpa [relabelLabels] using h.2
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(withinRadius_relabel σ G n u x).mpr hx.1,
        by simpa [relabelLabels] using hx.2⟩
  rw [hs, Set.ncard_image_of_injective _ σ.injective]

theorem coordinate_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) {key : ℕ → ℝ}
    (hk : Function.Injective key) (e : EdgeCode) :
    coordinate (relabelGraph σ G) (relabelLabels σ key) (mapEdge σ e) =
      (σ (coordinate G key e).1, (coordinate G key e).2) := by
  simp only [coordinate, EdgeAllocation.source_relabel σ hk,
    EdgeAllocation.target_relabel σ hk, radius_relabel, ballRank_relabel]

def coordinateNat (G : GraphCode) (key : ℕ → ℝ) (e : EdgeCode) : ℕ × ℕ :=
  let c := coordinate G key e
  (c.1, Nat.pair c.2.1 c.2.2)

theorem coordinateNat_injective {G : GraphCode} (hc : GraphConnected G)
    (hf : GraphLocallyFinite G) {key : ℕ → ℝ} (hk : Function.Injective key) :
    Function.Injective (coordinateNat G key) := by
  intro e f h
  apply coordinate_injective hc hf hk
  simp only [coordinateNat, Prod.mk.injEq, Nat.pair_eq_pair] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

theorem coordinateNat_relabel (σ : Equiv ℕ ℕ) (G : GraphCode) {key : ℕ → ℝ}
    (hk : Function.Injective key) (e : EdgeCode) :
    coordinateNat (relabelGraph σ G) (relabelLabels σ key) (mapEdge σ e) =
      (σ (coordinateNat G key e).1, (coordinateNat G key e).2) := by
  simp only [coordinateNat, coordinate_relabel σ G hk]

theorem measurable_radius_joint :
    Measurable (fun q : GraphCode × (ℕ × ℕ) => radius q.1 q.2.1 q.2.2) :=
  measurable_from_prod_countable_left fun p => measurable_radius p.1 p.2

theorem measurable_ballRank (n u v : ℕ) :
    Measurable (fun q : GraphCode × (ℕ → ℝ) => ballRank q.1 q.2 n u v) := by
  apply measurable_ncard.comp
  apply measurable_set_iff.mpr
  intro w
  change Measurable (fun q : GraphCode × (ℕ → ℝ) =>
    withinRadius q.1 n u w ∧ q.2 w < q.2 v)
  apply Measurable.and
  · exact (measurableSet_setOfPred.mp (measurableSet_withinRadius n u w)).comp measurable_fst
  · exact measurableSet_setOfPred.mp
      (measurableSet_lt (measurable_snd.eval) (measurable_snd.eval))

theorem measurable_ballRank_joint :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × (ℕ × (ℕ × ℕ)) =>
      ballRank q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) :=
  measurable_from_prod_countable_left fun p => measurable_ballRank p.1 p.2.1 p.2.2

theorem measurable_coordinate :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      coordinate q.1.1 q.1.2 q.2) := by
  have hs : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      EdgeAllocation.source q.1.2 q.2) :=
    EdgeAllocation.measurable_source_joint.comp (measurable_fst.snd.prodMk measurable_snd)
  have ht : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      EdgeAllocation.target q.1.2 q.2) :=
    EdgeAllocation.measurable_target_joint.comp (measurable_fst.snd.prodMk measurable_snd)
  have hn : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      radius q.1.1 (EdgeAllocation.source q.1.2 q.2) (EdgeAllocation.target q.1.2 q.2)) :=
    measurable_radius_joint.comp (measurable_fst.fst.prodMk (hs.prodMk ht))
  exact hs.prodMk (hn.prodMk (measurable_ballRank_joint.comp
    (measurable_fst.prodMk (hn.prodMk (hs.prodMk ht)))))

theorem measurable_coordinateNat :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      coordinateNat q.1.1 q.1.2 q.2) := by
  have hm : Measurable (fun c : ℕ × (ℕ × ℕ) => (c.1, Nat.pair c.2.1 c.2.2)) :=
    Measurable.of_discrete
  exact hm.comp measurable_coordinate

end Problem336.AllPairAllocation

end

end OAI
