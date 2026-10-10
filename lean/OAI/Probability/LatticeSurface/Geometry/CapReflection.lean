import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedBase

namespace OAI

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

lemma finite_partition_measure {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) (tag : X → I) (hm : ∀ i, MeasurableSet {x | tag x = i})
    (s : Set X) (hs : MeasurableSet s) :
    μ s = ∑ i, μ (s ∩ {x | tag x = i}) := by
  classical
  have he : s = ⋃ i, s ∩ {x | tag x = i} := by ext x; simp
  calc
    μ s = μ (⋃ i, s ∩ {x | tag x = i}) := congrArg μ he
    _ = ∑' i, μ (s ∩ {x | tag x = i}) := measure_iUnion
      (fun i j hij => Set.disjoint_left.mpr fun x hx hy => hij (hx.2.symm.trans hy.2))
      (fun i => hs.inter (hm i))
    _ = _ := tsum_fintype _

lemma finite_switch_preserving {N I : Type*} [Fintype N] [Fintype I]
    (tag : (N → ℝ) → I) (hm : ∀ i, MeasurableSet {x | tag x = i})
    (T : I → (N → ℝ) → (N → ℝ))
    (hT : ∀ i, MeasurePreserving (T i))
    (hinv : ∀ i x, tag (T i x) = tag x) :
    MeasurePreserving (fun x => T (tag x) x) := by
  classical
  have hme : Measurable (fun x => T (tag x) x) := by
    have hh : (fun x => T (tag x) x) =
        fun x => ∑ i, ({x | tag x = i}).indicator (T i) x := by
      funext x
      simp [Set.indicator]
    rw [hh]
    exact Finset.measurable_sum _ fun i _ => (hT i).measurable.indicator (hm i)
  refine ⟨hme, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hme hs,
    finite_partition_measure volume tag hm _ (hme hs),
    finite_partition_measure volume tag hm _ hs]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (fun x => T (tag x) x) ⁻¹' s ∩ {x | tag x = i} =
      T i ⁻¹' (s ∩ {x | tag x = i}) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, hinv]
    constructor
    · rintro ⟨h, htag⟩
      exact ⟨by simpa only [htag] using h, htag⟩
    · rintro ⟨h, htag⟩
      exact ⟨by simpa only [htag] using h, htag⟩
  rw [he]
  exact (hT i).measure_preimage (hs.inter (hm i)).nullMeasurableSet

def lock {V : Type*} (G : SimpleGraph V) (a : ℝ) (h : V → ℝ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ 1 < |h x-a| + |h y-a|
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by linarith [h.2]⟩⟩
  loopless := ⟨by intro x h; exact h.1.ne rfl⟩

def reflect {V : Type*} (pins : Set V) (S : Set V) (a : ℝ)
    (h : Free pins → ℝ) (x : Free pins) : ℝ :=
  if (x : V) ∈ S then 2*a-h x else h x

lemma preserving_reflect {V : Type*} [Fintype V] (pins S : Set V) (a : ℝ) :
    MeasurePreserving (reflect pins S a) := by
  classical
  change MeasurePreserving (fun (h : Free pins → ℝ) (x : Free pins) => (fun t : ℝ => if (x : V) ∈ S then 2*a-t else t) (h x))
  refine volume_preserving_pi (f := fun (x : Free pins) (t : ℝ) => if (x : V) ∈ S then 2*a-t else t) ?_
  intro x
  by_cases hx : (x : V) ∈ S
  · simpa [reflect, hx, sub_eq_add_neg, Function.comp_def] using
      (measurePreserving_add_left (volume : Measure ℝ) (2*a)).comp
        (Measure.measurePreserving_neg volume)
  · convert (MeasurePreserving.id (volume : Measure ℝ)) using 1
    funext t
    simp [hx]

lemma reflect_involutive {V : Type*} (pins S : Set V) (a : ℝ) :
    Function.Involutive (reflect pins S a) := by
  intro h
  funext x
  simp only [reflect]
  split_ifs <;> ring

lemma restore_reflect {V : Type*} (pins S : Set V) (b : V → ℝ) (a : ℝ)
    (hS : Disjoint pins S) (h : Free pins → ℝ) (x : V) :
    restore pins b (reflect pins S a h) x =
      if x ∈ S then 2*a-restore pins b h x else restore pins b h x := by
  by_cases hx : x ∈ pins
  · have hxS : x ∉ S := fun hh => Set.disjoint_left.mp hS hx hh
    simp [restore, hx, hxS]
  · simp [restore, hx, reflect]

lemma abs_restore_reflect {V : Type*} (pins S : Set V) (b : V → ℝ) (a : ℝ)
    (hS : Disjoint pins S) (h : Free pins → ℝ) (x : V) :
    |restore pins b (reflect pins S a h) x-a| = |restore pins b h x-a| := by
  rw [restore_reflect pins S b a hS]
  split_ifs
  · rw [show 2*a-restore pins b h x-a = -(restore pins b h x-a) by ring, abs_neg]
  · rfl

lemma lock_reflect {V : Type*} (G : SimpleGraph V) (pins S : Set V) (b : V → ℝ) (a : ℝ)
    (hS : Disjoint pins S) (h : Free pins → ℝ) :
    lock G a (restore pins b (reflect pins S a h)) = lock G a (restore pins b h) := by
  ext x y
  simp only [lock, abs_restore_reflect pins S b a hS]

lemma measurable_lock_fiber {V : Type*} [Fintype V]
    (G H : SimpleGraph V) (pins : Set V) (b : V → ℝ) (a : ℝ) :
    MeasurableSet {h : Free pins → ℝ | lock G a (restore pins b h) = H} := by
  have he : {h : Free pins → ℝ | lock G a (restore pins b h) = H} =
      {h | ∀ x y, (G.Adj x y ∧ 1 < |restore pins b h x-a|+|restore pins b h y-a|) ↔ H.Adj x y} := by
    ext h
    exact ⟨fun hh x y => by rw [← hh]; rfl,
      fun hh => by ext x y; exact hh x y⟩
  rw [he]
  simp only [ofPred_forall]
  apply MeasurableSet.iInter; intro x
  apply MeasurableSet.iInter; intro y
  have hm : MeasurableSet {h : Free pins → ℝ |
      1 < |restore pins b h x-a|+|restore pins b h y-a|} :=
    isOpen_lt continuous_const
      (((continuous_restore pins b x).sub continuous_const).abs.add
      ((continuous_restore pins b y).sub continuous_const).abs) |>.measurableSet
  by_cases hg : G.Adj x y
  · by_cases hh : H.Adj x y
    · simpa only [hg, hh, true_and, iff_true] using hm
    · simpa only [hg, hh, true_and, iff_false, Set.compl_ofPred] using hm.compl
  · simp only [hg, false_and, false_iff]
    exact MeasurableSet.const _

lemma lock_same_sign {V : Type*} {G : SimpleGraph V} {h : V → ℝ} {a : ℝ}
    (hf : ∀ x y, G.Adj x y → |h x-h y| ≤ 1) {x y : V}
    (hxy : (lock G a h).Adj x y) : (a < h x ↔ a < h y) := by
  have hb := abs_le.mp (hf x y hxy.1)
  have hl := hxy.2
  constructor
  · intro hx
    by_contra hy
    have hy := le_of_not_gt hy
    rw [abs_of_nonneg (by linarith : 0 ≤ h x-a), abs_of_nonpos (by linarith : h y-a ≤ 0)] at hl
    linarith [hb.2]
  · intro hy
    by_contra hx
    have hx := le_of_not_gt hx
    rw [abs_of_nonpos (by linarith : h x-a ≤ 0), abs_of_nonneg (by linarith : 0 ≤ h y-a)] at hl
    linarith [hb.1]

lemma reachable_same_sign {V : Type*} {G : SimpleGraph V} {h : V → ℝ} {a : ℝ}
    (hf : ∀ x y, G.Adj x y → |h x-h y| ≤ 1) {x y : V}
    (hxy : (lock G a h).Reachable x y) : (a < h x ↔ a < h y) := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => rfl
  | @cons u v w huv p ih => exact (lock_same_sign hf huv).trans ih

def freeCluster {V : Type*} (pins : Set V) (H : SimpleGraph V) (v : V) : Set V :=
  if Disjoint pins {x | H.Reachable v x} then {x | H.Reachable v x} else ∅

lemma disjoint_freeCluster {V : Type*} (pins : Set V) (H : SimpleGraph V) (v : V) :
    Disjoint pins (freeCluster pins H v) := by
  unfold freeCluster
  split_ifs with hh
  · exact hh
  · exact Set.disjoint_empty _

lemma freeCluster_closed {V : Type*} (pins : Set V) (H : SimpleGraph V) (v x y : V)
    (hx : x ∈ freeCluster pins H v) (hxy : H.Adj x y) :
    y ∈ freeCluster pins H v := by
  unfold freeCluster at *
  split_ifs at * with hh
  · exact hx.trans hxy.reachable
  · exact False.elim hx

lemma reflect_cluster_feasible {V : Type*} {G : SimpleGraph V}
    {pins : Set V} {b : V → ℝ} {a : ℝ} {h : Free pins → ℝ}
    (hf : h ∈ conditionalBody G pins b) (v : V) :
    reflect pins (freeCluster pins (lock G a (restore pins b h)) v) a h ∈
      conditionalBody G pins b := by
  let S := freeCluster pins (lock G a (restore pins b h)) v
  have hS := disjoint_freeCluster pins (lock G a (restore pins b h)) v
  intro x y hxy
  rw [restore_reflect pins S b a hS, restore_reflect pins S b a hS]
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp only [ite_eq_left hx, ite_eq_left hy]
    convert hf x y hxy using 1
    rw [show 2*a-restore pins b h x-(2*a-restore pins b h y) =
      -(restore pins b h x-restore pins b h y) by ring, abs_neg]
  · simp only [ite_eq_left hx, ite_eq_right hy]
    have hn : ¬ (lock G a (restore pins b h)).Adj x y :=
      fun hh => hy (freeCluster_closed pins _ v x y hx hh)
    have hr : |restore pins b h x-a|+|restore pins b h y-a| ≤ 1 := by
      by_contra hh
      exact hn ⟨hxy, lt_of_not_ge hh⟩
    calc
      |2*a-restore pins b h x-restore pins b h y| =
        |-(restore pins b h x-a)-(restore pins b h y-a)| := by congr 1; ring
      _ ≤ |restore pins b h x-a|+|restore pins b h y-a| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (-(restore pins b h x-a)) 0 (restore pins b h y-a)
      _ ≤ 1 := hr
  · simp only [ite_eq_right hx, ite_eq_left hy]
    have hn : ¬ (lock G a (restore pins b h)).Adj x y :=
      fun hh => hx (freeCluster_closed pins _ v y x hy hh.symm)
    have hr : |restore pins b h x-a|+|restore pins b h y-a| ≤ 1 := by
      by_contra hh
      exact hn ⟨hxy, lt_of_not_ge hh⟩
    calc
      |restore pins b h x-(2*a-restore pins b h y)| =
        |(restore pins b h x-a)+(restore pins b h y-a)| := by congr 1; ring
      _ ≤ |restore pins b h x-a|+|restore pins b h y-a| := abs_add_le _ _
      _ ≤ 1 := hr
  · simpa only [ite_eq_right hx, ite_eq_right hy] using hf x y hxy

def clusterFlip {V : Type*} (G : SimpleGraph V) (pins : Set V) (b : V → ℝ)
    (a : ℝ) (v : V) (h : Free pins → ℝ) : Free pins → ℝ :=
  reflect pins (freeCluster pins (lock G a (restore pins b h)) v) a h

lemma preserving_clusterFlip {V : Type*} [Fintype V]
    (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) (a : ℝ) (v : V) :
    MeasurePreserving (clusterFlip G pins b a v) := by
  classical
  let : Fintype (SimpleGraph V) := Fintype.ofFinite _
  apply finite_switch_preserving
    (fun h => lock G a (restore pins b h))
    (fun H => measurable_lock_fiber G H pins b a)
    (fun H => reflect pins (freeCluster pins H v) a)
    (fun H => preserving_reflect pins _ a)
  intro H h
  exact lock_reflect G pins _ b a (disjoint_freeCluster pins H v) h

lemma positive_freeCluster {V : Type*} {G : SimpleGraph V}
    {pins : Set V} {b : V → ℝ} {a : ℝ} {h : Free pins → ℝ}
    (hf : h ∈ conditionalBody G pins b) (hb : ∀ x ∈ pins, b x ≤ a)
    (v : V) (hv : a < restore pins b h v) :
    freeCluster pins (lock G a (restore pins b h)) v =
      {x | (lock G a (restore pins b h)).Reachable v x} := by
  apply ite_eq_left
  apply Set.disjoint_left.mpr
  intro x hx hreach
  have hxpos := (reachable_same_sign hf hreach).mp hv
  have he : restore pins b h x = b x := by simp [restore, hx]
  rw [he] at hxpos
  exact (not_lt_of_ge (hb x hx)) hxpos

lemma clusterFlip_positive {V : Type*} {G : SimpleGraph V}
    {pins : Set V} {b : V → ℝ} {a : ℝ} {h : Free pins → ℝ}
    (hf : h ∈ conditionalBody G pins b) (hb : ∀ x ∈ pins, b x ≤ a)
    (v : V) (hv : a < restore pins b h v) :
    restore pins b (clusterFlip G pins b a v h) v ≤ a ∧
      ∀ x, restore pins b h x ≤ a →
        restore pins b (clusterFlip G pins b a v h) x = restore pins b h x := by
  have he := positive_freeCluster hf hb v hv
  have hdis := disjoint_freeCluster pins (lock G a (restore pins b h)) v
  constructor
  · unfold clusterFlip
    rw [restore_reflect pins _ b a hdis, he]
    simp only [Set.mem_ofPred_eq, SimpleGraph.Reachable.refl, ite_true]
    linarith
  · intro x hx
    unfold clusterFlip
    rw [restore_reflect pins _ b a hdis, he]
    apply ite_eq_right
    intro hr
    exact (not_lt_of_ge hx) ((reachable_same_sign hf hr).mp hv)

def below {V : Type*} (G : SimpleGraph V) (pins : Set V) (b : V → ℝ)
    (a : ℝ) (S : Finset V) : Set (Free pins → ℝ) :=
  conditionalBody G pins b ∩ {h | ∀ x ∈ S, restore pins b h x ≤ a}

lemma measurable_below {V : Type*} [Fintype V] (G : SimpleGraph V) (pins : Set V)
    (b : V → ℝ) (a : ℝ) (S : Finset V) : MeasurableSet (below G pins b a S) := by
  apply (closed_conditionalBody G pins b).measurableSet.inter
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun _ =>
    (isClosed_le (continuous_restore pins b x) continuous_const).measurableSet

lemma volume_below_insert {V : Type*} [Fintype V] (G : SimpleGraph V) (pins : Set V)
    (b : V → ℝ) (a : ℝ) (hb : ∀ x ∈ pins, b x ≤ a) (S : Finset V) (v : V) :
    volume (below G pins b a S) ≤ 2 * volume (below G pins b a (insert v S)) := by
  classical
  let B := below G pins b a (insert v S)
  have hmB : MeasurableSet B := measurable_below G pins b a _
  have hsub : below G pins b a S ⊆ B ∪ clusterFlip G pins b a v ⁻¹' B := by
    rintro h ⟨hf, hS⟩
    by_cases hv : restore pins b h v ≤ a
    · left
      exact ⟨hf, fun x hx => (Finset.mem_insert.mp hx).elim (fun he => he ▸ hv) (hS x)⟩
    · right
      have hh := clusterFlip_positive hf hb v (lt_of_not_ge hv)
      refine ⟨reflect_cluster_feasible hf v, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hh.1
      · rw [hh.2 x (hS x hx)]
        exact hS x hx
  calc
    volume (below G pins b a S) ≤ volume (B ∪ clusterFlip G pins b a v ⁻¹' B) := measure_mono hsub
    _ ≤ volume B + volume (clusterFlip G pins b a v ⁻¹' B) := measure_union_le _ _
    _ = 2 * volume B := by
      rw [(preserving_clusterFlip G pins b a v).measure_preimage hmB.nullMeasurableSet, two_mul]

theorem volume_one_sided {V : Type*} [Fintype V] (G : SimpleGraph V) (pins : Set V)
    (b : V → ℝ) (a : ℝ) (hb : ∀ x ∈ pins, b x ≤ a) (S : Finset V) :
    volume (conditionalBody G pins b) ≤ 2 ^ S.card * volume (below G pins b a S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [below]
  | @insert v S hv ih =>
    calc
      volume (conditionalBody G pins b) ≤ 2 ^ S.card * volume (below G pins b a S) := ih
      _ ≤ 2 ^ S.card * (2 * volume (below G pins b a (insert v S))) :=
        mul_le_mul_right (volume_below_insert G pins b a hb S v) _
      _ = _ := by rw [Finset.card_insert_of_notMem hv, pow_succ]; ac_rfl

end ExtremalEdges

end

end OAI
