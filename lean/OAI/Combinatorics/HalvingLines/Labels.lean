import OAI.Combinatorics.HalvingLines.Directions

namespace OAI

open Filter Topology

namespace PlanarHalving.RankCoordinates
open Set
open scoped unitInterval

structure Family (m : ℕ) where
  graph : Fin m → ℝ → ℝ
  continuous : ∀ j, Continuous (graph j)
  convex : ∀ j, ConvexOn ℝ univ (graph j)
  scale : ℝ
  scale_pos : 0 < scale

noncomputable def Family.value {m : ℕ} [NeZero m] (F : Family m) (p : Point) : I :=
  ⟨smoothed F.graph F.scale p, (smoothed_mem (NeZero.pos m) F.graph F.scale p).1.le,
    (smoothed_mem (NeZero.pos m) F.graph F.scale p).2.le⟩

lemma Family.continuous_value {m : ℕ} [NeZero m] (F : Family m) : Continuous F.value :=
  (continuous_smoothed F.graph F.scale F.continuous).subtype_mk _

noncomputable def Family.flat (m : ℕ) : Family m where
  graph := fun _ _ => 0
  continuous := fun _ => continuous_const
  convex := fun _ => convexOn_const _ (convex_univ)
  scale := 1
  scale_pos := zero_lt_one

end PlanarHalving.RankCoordinates
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.rankFamily (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) : Family (a*n) := by
  classical
  by_cases hJ : 0 < length R J
  · let h := S.window_coordinate hP (start R J) (length R J)
      (by rw [start_add_length]; exact stop_le R J) hJ
    let G := h.choose
    exact ⟨G.graph,G.continuous,G.convex,h.choose_spec.choose,h.choose_spec.choose_spec.1⟩
  · exact Family.flat _

lemma System.rankFamily_spec (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) :
    ∃ G : (S.timeWindow J).FullGraphs (S.drawing.exteriorCrossings (S.timeWindow J).edges),
      (S.rankFamily hP J).graph=G.graph ∧
      ∀ z ∈ S.drawing.exteriorCrossings (S.timeWindow J).edges,
        |(S.rankFamily hP J).value z-(slot G.graph z : ℝ)/(a*n)| ≤ 2/(a*n) := by
  classical
  unfold System.rankFamily
  rw [dite_eq_left hJ]
  exact ⟨_,rfl,(S.window_coordinate hP _ _ _ hJ).choose_spec.choose_spec.2⟩

abbrev Labels := Window → I

noncomputable instance labelsMetric : MetricSpace Labels := PiCountable.metricSpace

noncomputable def System.labels (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (p : Point) : Labels := fun J => (S.rankFamily hP J).value p

lemma System.continuous_labels (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) : Continuous (S.labels hP) :=
  continuous_pi (fun J => (S.rankFamily hP J).continuous_value)

lemma System.coordinate_oscillation (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) :
    ∑ e : ↥S.edges, Metric.ediam ((fun p => S.labels hP p J) '' segment ℝ (P e.val.1) (P e.val.2))
      ≤ 2*a*n := by
  have hh := S.rank_oscillation (Nat.mul_pos (NeZero.pos a) (NeZero.pos n))
    (S.rankFamily hP J).graph (S.rankFamily hP J).convex (S.rankFamily hP J).scale_pos
  convert hh using 1
  apply Finset.sum_congr rfl
  intro e _
  exact (Isometry.ediam_image (isometry_subtype_coe : Isometry (Subtype.val : I → ℝ)) _).symm.trans
    (by rw [Set.image_image]; rfl)

end PlanarHalving.Batches
namespace PlanarHalving.CompactLabels
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal PiCountable unitInterval
variable {ι : Type*} [Encodable ι]

lemma ediam_le_finite {X : Type*} (z : X → (ι → I)) (A : Set X) (K : Finset ι) :
    Metric.ediam (z '' A) ≤ (∑ i ∈ K, Metric.ediam ((fun x => z x i) '' A))+
      ∑' i : {j // j ∉ K}, (2 : ℝ≥0∞)⁻¹ ^ Encodable.encode (i : ι) := by
  apply Metric.ediam_le
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  calc
    edist (z x) (z y) = ∑' i : ι, min ((2 : ℝ≥0∞)⁻¹ ^ Encodable.encode i) (edist (z x i) (z y i)) := rfl
    _ = (∑ i ∈ K, min ((2 : ℝ≥0∞)⁻¹ ^ Encodable.encode i) (edist (z x i) (z y i)))+
        ∑' i : {j // j ∉ K}, min ((2 : ℝ≥0∞)⁻¹ ^ Encodable.encode (i : ι)) (edist (z x i) (z y i)) :=
      (ENNReal.sum_add_tsum_compl ..).symm
    _ ≤ _ := by
      gcongr
      · exact (min_le_right ..).trans (Metric.edist_le_ediam_of_mem ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩)
      · exact min_le_left ..

lemma finite_tail {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ K : Finset ι, ∑' i : {j // j ∉ K}, (2 : ℝ≥0∞)⁻¹ ^ Encodable.encode (i : ι) < ρ/2 := by
  exact ((tendsto_order.1 <| ENNReal.tendsto_tsum_compl_atTop_zero
    (tsum_geometric_encode_lt_top ENNReal.one_half_lt_one).ne).2 _
      <| by simpa using hρ.ne').exists

lemma long_count_bound {X α : Type*} [Fintype α] (z : X → (ι → I)) (A : α → Set X)
    {ρ : ℝ≥0∞} (_hρ : 0 < ρ) (K : Finset ι)
    (hK : ∑' i : {j // j ∉ K}, (2 : ℝ≥0∞)⁻¹ ^ Encodable.encode (i : ι) < ρ/2)
    {B : ℝ≥0∞} (hB : ∀ i, ∑ e : α, Metric.ediam ((fun x => z x i) '' A e) ≤ B) :
    (ρ/2) * ((Finset.univ.filter (fun e : α => ρ ≤ Metric.ediam (z '' A e))).card : ℝ≥0∞)
      ≤ K.card*B := by
  classical
  let E := Finset.univ.filter (fun e : α => ρ ≤ Metric.ediam (z '' A e))
  have he (e : α) (he : e ∈ E) : ρ/2 ≤ ∑ i ∈ K, Metric.ediam ((fun x => z x i) '' A e) := by
    by_contra hh
    have hh' := lt_of_not_ge hh
    have hlt := ENNReal.add_lt_add hh' hK
    rw [ENNReal.add_halves] at hlt
    exact not_lt_of_ge (Finset.mem_filter.mp he).2
      ((ediam_le_finite z (A e) K).trans_lt hlt)
  calc
    _ = ∑ _e ∈ E, ρ/2 := by simp only [Finset.sum_const,nsmul_eq_mul]; rw [mul_comm]
    _ ≤ ∑ e ∈ E, ∑ i ∈ K, Metric.ediam ((fun x => z x i) '' A e) := Finset.sum_le_sum he
    _ ≤ ∑ e : α, ∑ i ∈ K, Metric.ediam ((fun x => z x i) '' A e) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset ..)
    _ = ∑ i ∈ K, ∑ e : α, Metric.ediam ((fun x => z x i) '' A e) := Finset.sum_comm
    _ ≤ ∑ _i ∈ K, B := Finset.sum_le_sum (fun i _ => hB i)
    _ = K.card*B := by simp

end PlanarHalving.CompactLabels
namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal

theorem finiteMeasure_subsequence_dependent
    {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
    (μ : ℕ → ∀ i, FiniteMeasure (X i)) (C : ι → ℝ≥0)
    (hbound : ∀ n i, (μ n i).mass ≤ C i) :
    ∃ (φ : ℕ → ℕ) (ν : ∀ i, FiniteMeasure (X i)), StrictMono φ ∧
      ∀ i, Tendsto (fun n => μ (φ n) i) atTop (𝓝 (ν i)) := by
  let F : ℕ → ∀ i : ι, (Icc (0 : ℝ≥0) (C i)) × ProbabilityMeasure (X i) :=
    fun n i => (⟨(μ n i).mass,zero_le,hbound n i⟩,(μ n i).normalize)
  obtain ⟨g,φ,hφ,hg⟩ := CompactSpace.tendsto_subseq F
  refine ⟨φ,fun i => (g i).1.val • (g i).2.toFiniteMeasure,hφ,?_⟩
  intro i
  have hi := (tendsto_pi_nhds.mp hg) i
  have hm := continuous_subtype_val.tendsto _ |>.comp ((continuous_fst.tendsto (g i)).comp hi)
  have hn := (ProbabilityMeasure.toFiniteMeasure_isEmbedding (X i)).continuous.tendsto _ |>.comp
    ((continuous_snd.tendsto (g i)).comp hi)
  have ht := hm.smul hn
  convert ht using 1
  funext n
  exact (μ (φ n) i).self_eq_mass_smul_normalize

end PlanarHalving.Limits
namespace PlanarHalving.TimeWindows
open Set
open scoped unitInterval

def Before (A B : Window) : Prop :=
  UniformPartition.boundary (2^A.1) A.2.succ ≤ UniformPartition.boundary (2^B.1) B.2.castSucc

lemma stop_le_start (R : ℕ) [NeZero R] {A B : Window} (hAB : Before A B) :
    stop R A ≤ start R B := cut_mono _ hAB

end PlanarHalving.TimeWindows
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows MeasureTheory Limits
open scoped unitInterval NNReal ENNReal
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.timeWindow_disjoint (S : @System n R k a P) [NeZero R] [NeZero a]
    {A B : Window} (hAB : Before A B) :
    Disjoint (S.timeWindow A).edges (S.timeWindow B).edges := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heA heB
  let v : ↥S.edges := ⟨e,S.timeWindow_edges A heA⟩
  have hA := (mem_carrier_iff R A (S.trace v.property).batch).mp ((S.timeWindow_mem A v).mp heA)
  have hB := (mem_carrier_iff R B (S.trace v.property).batch).mp ((S.timeWindow_mem B v).mp heB)
  have hh := stop_le_start R hAB
  omega

lemma System.timeWindow_graph_gap (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    {A B : Window} (hAB : Before A B) {F H : Finset Point}
    (G : (S.timeWindow A).FullGraphs F) (G' : (S.timeWindow B).FullGraphs H) :
    G.upper < G'.lower := by
  apply G.upper_lt.trans_le
  apply le_trans _ G'.lower_lt.le
  change S.slope ⟨start R A+length R A, _⟩ ≤ S.slope ⟨start R B+0,_⟩
  apply S.increasing.monotone
  change start R A+length R A ≤ start R B+0
  rw [start_add_length,Nat.add_zero]
  exact stop_le_start R hAB

noncomputable def System.windowCrossings (S : @System n R k a P) [NeZero R] (A B : Window) :
    Finset ((Fin n × Fin n) × (Fin n × Fin n)) := by
  classical
  exact S.drawing.crossings.filter (fun w =>
    (w.1 ∈ (S.timeWindow A).edges ∧ w.2 ∈ (S.timeWindow B).edges) ∨
    (w.2 ∈ (S.timeWindow A).edges ∧ w.1 ∈ (S.timeWindow B).edges))

lemma System.windowCrossings_sub (S : @System n R k a P) [NeZero R] (A B : Window) :
    S.windowCrossings A B ⊆ S.drawing.crossings := Finset.filter_subset ..

noncomputable def System.windowCrossPoint (S : @System n R k a P) [NeZero R] (A B : Window)
    (w : ↥(S.windowCrossings A B)) : Point :=
  S.drawing.crossingPoint ⟨w.val,S.windowCrossings_sub A B w.property⟩

lemma System.windowCrossPoint_injective (S : @System n R k a P) [NeZero R]
    (hP : Generic P) (A B : Window) : Function.Injective (S.windowCrossPoint A B) := by
  intro w v h
  apply Subtype.ext
  exact congrArg (fun v : ↥S.drawing.crossings => v.val)
    (S.drawing.crossingPoint_injective (S.drawing.noMultiple_of_generic hP) h)

lemma System.windowCrossPoint_exterior (S : @System n R k a P) [NeZero R] [NeZero a]
    {A B : Window} (hAB : Before A B) (w : ↥(S.windowCrossings A B)) :
    S.windowCrossPoint A B w ∈ S.drawing.exteriorCrossings (S.timeWindow A).edges ∧
    S.windowCrossPoint A B w ∈ S.drawing.exteriorCrossings (S.timeWindow B).edges := by
  classical
  let v : ↥S.drawing.crossings := ⟨w.val,S.windowCrossings_sub A B w.property⟩
  have hw := (Finset.mem_filter.mp w.property).2
  have hd := Finset.disjoint_left.mp (S.timeWindow_disjoint hAB)
  have hA : (v.val.1 ∈ (S.timeWindow A).edges ∧ v.val.2 ∉ (S.timeWindow A).edges) ∨
      (v.val.2 ∈ (S.timeWindow A).edges ∧ v.val.1 ∉ (S.timeWindow A).edges) := by
    rcases hw with hw | hw
    · exact Or.inl ⟨hw.1,fun hh => hd hh hw.2⟩
    · exact Or.inr ⟨hw.1,fun hh => hd hh hw.2⟩
  have hB : (v.val.1 ∈ (S.timeWindow B).edges ∧ v.val.2 ∉ (S.timeWindow B).edges) ∨
      (v.val.2 ∈ (S.timeWindow B).edges ∧ v.val.1 ∉ (S.timeWindow B).edges) := by
    rcases hw with hw | hw
    · exact Or.inr ⟨hw.2,hd hw.1⟩
    · exact Or.inl ⟨hw.2,hd hw.1⟩
  exact ⟨Finset.mem_image.mpr ⟨v,by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hA,rfl⟩,
    Finset.mem_image.mpr ⟨v,by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hB,rfl⟩⟩

lemma System.windowCrossPoint_graph (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    {A B : Window} (w : ↥(S.windowCrossings A B))
    {F H : Finset Point} (G : (S.timeWindow A).FullGraphs F) (G' : (S.timeWindow B).FullGraphs H) :
    (∃ i, G.graph i (S.windowCrossPoint A B w).1 = (S.windowCrossPoint A B w).2) ∧
    ∃ j, G'.graph j (S.windowCrossPoint A B w).1 = (S.windowCrossPoint A B w).2 := by
  classical
  let v : ↥S.drawing.crossings := ⟨w.val,S.windowCrossings_sub A B w.property⟩
  have hm := S.drawing.crossingPoint_mem v
  have hw := (Finset.mem_filter.mp w.property).2
  rcases hw with hw | hw
  · exact ⟨⟨_,G.edge _ hw.1 _ (openSegment_subset_segment ℝ _ _ hm.1)⟩,
      ⟨_,G'.edge _ hw.2 _ (openSegment_subset_segment ℝ _ _ hm.2)⟩⟩
  · exact ⟨⟨_,G.edge _ hw.1 _ (openSegment_subset_segment ℝ _ _ hm.2)⟩,
      ⟨_,G'.edge _ hw.2 _ (openSegment_subset_segment ℝ _ _ hm.1)⟩⟩

theorem System.window_crossing_slots (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) :
    ∃ slots : ↥(S.windowCrossings A B) → Fin (a*n) × Fin (a*n),
      Function.Injective slots ∧ ∀ w,
        dist (S.labels hP (S.windowCrossPoint A B w) A,S.labels hP (S.windowCrossPoint A B w) B)
          (UniformPartition.gridPoint (a*n) (slots w)) ≤ 2/(a*n : ℕ) := by
  classical
  obtain ⟨G,hG,hGE⟩ := S.rankFamily_spec hP A hA
  obtain ⟨H,hH,hHE⟩ := S.rankFamily_spec hP B hB
  let pt := S.windowCrossPoint A B
  have hinc (w : ↥(S.windowCrossings A B)) := S.windowCrossPoint_graph w G H
  let slots : ↥(S.windowCrossings A B) → Fin (a*n) × Fin (a*n) := fun w =>
    (⟨slot G.graph (pt w),by simpa using slot_lt_card G.graph (hinc w).1⟩,
      ⟨slot H.graph (pt w),by simpa using slot_lt_card H.graph (hinc w).2⟩)
  refine ⟨slots,?_,?_⟩
  · intro u v huv
    apply S.windowCrossPoint_injective hP A B
    apply pair_slots_injOn G.graph H.graph G.slopes H.slopes (S.timeWindow_graph_gap hAB G H)
      (range pt) (by rintro _ ⟨w,rfl⟩; exact hinc w) (mem_range_self u) (mem_range_self v)
    exact congrArg (fun p : Fin (a*n) × Fin (a*n) => (p.1.val,p.2.val)) huv
  · intro w
    rw [Prod.dist_eq,max_le_iff]
    have hext := S.windowCrossPoint_exterior hAB w
    constructor
    · change |(S.rankFamily hP A).value (pt w)-(slot G.graph (pt w) : ℝ)/(a*n : ℕ)| ≤ _
      simpa only [Nat.cast_mul] using hGE _ hext.1
    · change |(S.rankFamily hP B).value (pt w)-(slot H.graph (pt w) : ℝ)/(a*n : ℕ)| ≤ _
      simpa only [Nat.cast_mul] using hHE _ hext.2

end PlanarHalving.Batches
namespace PlanarHalving.Batches
open MeasureTheory Set Limits TimeWindows PlaneGraph
open scoped NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.vertexMeasure_mass_le (S : @System n R k a P) [NeZero n]
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) : (S.vertexMeasure z).mass ≤ 1 := by
  rw [System.vertexMeasure,mass_weightedAtoms]
  have hcard : Fintype.card ↥S.vertices ≤ n := by simpa using S.vertices.card_le_univ
  calc
    _ ≤ (n : ℝ≥0)⁻¹ * n := mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) zero_le
    _ = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n))

noncomputable def System.windowCrossMeasure (S : @System n R k a P) [NeZero R]
    (A B : Window) {X : Type*} [MeasurableSpace X] (z : Point → X) : FiniteMeasure X :=
  weightedAtoms (((a*n : ℕ) : ℝ≥0)^2)⁻¹ (fun w => z (S.windowCrossPoint A B w))

lemma System.windowCrossMeasure_mass_le (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    (hP : Generic P) (A B : Window) {X : Type*} [MeasurableSpace X] (z : Point → X) :
    (S.windowCrossMeasure A B z).mass ≤ 2 := by
  rw [System.windowCrossMeasure,mass_weightedAtoms,Fintype.card_coe]
  have hc : (S.windowCrossings A B).card ≤ 2*(a*n)^2 := by
    calc
      _ ≤ S.drawing.crossings.card := Finset.card_le_card (S.windowCrossings_sub A B)
      _ ≤ 2*a^2*S.vertices.card^2 := S.crossing_cap hP.1 (Generic.x_injective hP)
          (S.drawing.noMultiple_of_generic hP)
      _ ≤ 2*a^2*n^2 := by gcongr; exact S.vertices.card_le_univ.trans (by simp)
      _ = 2*(a*n)^2 := by ring
  have hM : (((a*n : ℕ) : ℝ≥0)^2) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne n)))
  calc
    _ ≤ (((a*n : ℕ) : ℝ≥0)^2)⁻¹ * (2*((a*n : ℕ) : ℝ≥0)^2) := by
      gcongr
      exact_mod_cast hc
    _ = 2 := by rw [mul_left_comm,inv_mul_cancel₀ hM,mul_one]

end PlanarHalving.Batches
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

structure Configuration where
  n : ℕ
  R : ℕ
  k : ℕ
  a : ℕ
  n_pos : 0 < n
  R_pos : 0 < R
  a_pos : 0 < a
  point : Fin n → Point
  generic : Generic point
  system : @System n R k a point

instance (F : Configuration) : NeZero F.n := ⟨ne_of_gt F.n_pos⟩
instance (F : Configuration) : NeZero F.R := ⟨ne_of_gt F.R_pos⟩
instance (F : Configuration) : NeZero F.a := ⟨ne_of_gt F.a_pos⟩

noncomputable def Configuration.label (F : Configuration) : Point → Labels := F.system.labels F.generic

lemma Configuration.continuous_label (F : Configuration) : Continuous F.label :=
  F.system.continuous_labels F.generic

noncomputable def Configuration.points (F : Configuration) : FiniteMeasure Labels :=
  weightedAtoms (F.n : ℝ≥0)⁻¹ (F.label ∘ F.point)
noncomputable def Configuration.vertices (F : Configuration) (J : Window) : FiniteMeasure Labels :=
  (F.system.timeWindow J).vertexMeasure (F.label ∘ F.point)
noncomputable def Configuration.edgeTime (F : Configuration) : FiniteMeasure (Labels×I) :=
  F.system.labelTimeMeasure (F.label ∘ F.point)
noncomputable def Configuration.crossings (F : Configuration) (A B : Window) : FiniteMeasure Labels :=
  F.system.windowCrossMeasure A B F.label
noncomputable def Configuration.timeRestrict (F : Configuration) (J : Window) : FiniteMeasure (Labels×I) :=
  ⟨(F.edgeTime : Measure (Labels×I)).restrict (Prod.snd ⁻¹' carrier J),inferInstance⟩

lemma Configuration.points_mass (F : Configuration) : F.points.mass=1 := by
  rw [Configuration.points,mass_weightedAtoms,Fintype.card_fin]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne F.n))
lemma Configuration.vertices_mass_le (F : Configuration) (J : Window) : (F.vertices J).mass ≤ 1 :=
  (F.system.timeWindow J).vertexMeasure_mass_le _
lemma Configuration.edgeTime_mass (F : Configuration) : F.edgeTime.mass=1 := F.system.labelTimeMeasure_mass _
lemma Configuration.crossings_mass_le (F : Configuration) (A B : Window) : (F.crossings A B).mass ≤ 2 :=
  F.system.windowCrossMeasure_mass_le F.generic A B _
lemma Configuration.timeRestrict_mass_le (F : Configuration) (J : Window) : (F.timeRestrict J).mass ≤ 1 := by
  rw [← F.edgeTime_mass]
  apply ENNReal.coe_le_coe.mp
  simp only [FiniteMeasure.ennreal_mass]
  change (F.edgeTime : Measure (Labels×I)).restrict (Prod.snd ⁻¹' carrier J) univ ≤
    (F.edgeTime : Measure (Labels×I)) univ
  exact Measure.restrict_le_self _

end PlanarHalving.RankLimits

end OAI
