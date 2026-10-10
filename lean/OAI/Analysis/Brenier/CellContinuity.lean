import OAI.Analysis.Brenier.CellGeometry

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace Problem358

/-- The closed cell of an affine score, before restriction to the source set. -/
def scoreCell {d : ℕ} {ι : Type*} (y : ι → E d) (c : ι → ℝ) (i : ι) : Set (E d) :=
  {x | ∀ j, inner ℝ (y j) x + c j ≤ inner ℝ (y i) x + c i}

theorem measurableSet_scoreCell {d : ℕ} {ι : Type*} [Countable ι]
    (y : ι → E d) (c : ι → ℝ) (i : ι) : MeasurableSet (scoreCell y c i) := by
  simp only [scoreCell, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (by fun_prop) (by fun_prop)

/-- A strict limiting comparison has an eventually constant truth value. -/
theorem eventually_le_iff_of_tendsto_ne {β : Type*} {l : Filter β}
    {f g : β → ℝ} {a b : ℝ} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (hab : a ≠ b) :
    ∀ᶠ n in l, f n ≤ g n ↔ a ≤ b := by
  rcases lt_or_gt_of_ne hab with h | h
  · filter_upwards [hf.eventually_lt hg h] with n hn
    simp only [le_of_lt hn, le_of_lt h]
  · filter_upwards [hg.eventually_lt hf h] with n hn
    simp only [not_le_of_gt hn, not_le_of_gt h]

/-- Away from limiting ties, membership in a finite affine cell stabilizes. -/
theorem eventually_mem_scoreCell_iff {d : ℕ} {ι β : Type*} [Finite ι]
    {l : Filter β} {ys : β → ι → E d} {cs : β → ι → ℝ}
    {y : ι → E d} {c : ι → ℝ} (i : ι) (x : E d)
    (hy : ∀ j, Tendsto (fun n => ys n j) l (𝓝 (y j)))
    (hc : ∀ j, Tendsto (fun n => cs n j) l (𝓝 (c j)))
    (htie : ∀ j, j ≠ i → inner ℝ (y j) x + c j ≠ inner ℝ (y i) x + c i) :
    ∀ᶠ n in l, x ∈ scoreCell (ys n) (cs n) i ↔ x ∈ scoreCell y c i := by
  have hcomp : ∀ j, ∀ᶠ n in l,
      (inner ℝ (ys n j) x + cs n j ≤ inner ℝ (ys n i) x + cs n i) ↔
        inner ℝ (y j) x + c j ≤ inner ℝ (y i) x + c i := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · exact eventually_le_iff_of_tendsto_ne
        (((hy j).inner tendsto_const_nhds).add (hc j))
        (((hy i).inner tendsto_const_nhds).add (hc i)) (htie j hji)
  filter_upwards [Filter.eventually_all.mpr hcomp] with n hn
  exact forall_congr' hn

/-- Distinct limiting slopes make affine-cell membership stabilize almost everywhere. -/
theorem ae_eventually_mem_scoreCell_iff {d : ℕ} {ι β : Type*} [Finite ι]
    (K : Set (E d)) {l : Filter β} {ys : β → ι → E d} {cs : β → ι → ℝ}
    {y : ι → E d} {c : ι → ℝ} (i : ι) (hinj : Function.Injective y)
    (hy : ∀ j, Tendsto (fun n => ys n j) l (𝓝 (y j)))
    (hc : ∀ j, Tendsto (fun n => cs n j) l (𝓝 (c j))) :
    ∀ᵐ x ∂uniformMeasure K, ∀ᶠ n in l,
      x ∈ scoreCell (ys n) (cs n) i ↔ x ∈ scoreCell y c i := by
  filter_upwards [ae_all_affine_eq_imp_slope_eq K y c] with x hx
  apply eventually_mem_scoreCell_iff i x hy hc
  intro j hji heq
  exact hji (hinj (hx j i heq))

/-- Cell masses converge under convergence of sites and intercepts, provided only
that the limiting sites are distinct and the uniform source is finite. -/
theorem tendsto_uniformMeasure_scoreCell {d : ℕ} {ι β : Type*} [Finite ι]
    (K : Set (E d))
    {l : Filter β} [l.IsCountablyGenerated]
    {ys : β → ι → E d} {cs : β → ι → ℝ} {y : ι → E d} {c : ι → ℝ}
    (i : ι) (hinj : Function.Injective y)
    (hy : ∀ j, Tendsto (fun n => ys n j) l (𝓝 (y j)))
    (hc : ∀ j, Tendsto (fun n => cs n j) l (𝓝 (c j))) :
    Tendsto (fun n => uniformMeasure K (scoreCell (ys n) (cs n) i)) l
      (𝓝 (uniformMeasure K (scoreCell y c i))) := by
  let := uniformMeasure_finite K
  exact tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure l
    (measurableSet_scoreCell y c i) (fun n => measurableSet_scoreCell (ys n) (cs n) i)
    (ae_eventually_mem_scoreCell_iff K i hinj hy hc)

/-- Joint continuity in all affine coefficients at configurations with distinct sites. -/
theorem continuousAt_uniformMeasure_scoreCell {d : ℕ} {ι : Type*} [Finite ι]
    (K : Set (E d))
    (y : ι → E d) (c : ι → ℝ) (i : ι) (hinj : Function.Injective y) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      uniformMeasure K (scoreCell p.1 p.2 i)) (y, c) := by
  apply tendsto_uniformMeasure_scoreCell K i hinj
  · intro j
    exact ((continuous_apply j).comp continuous_fst).continuousAt
  · intro j
    exact ((continuous_apply j).comp continuous_snd).continuousAt

/-- Dominated convergence for an integrable function over varying measurable sets
whose membership stabilizes almost everywhere. -/
theorem tendsto_setIntegral_of_ae_eventually_mem
    {X V β : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : Measure X} {l : Filter β} [l.IsCountablyGenerated]
    {sets : β → Set X} {s : Set X} (hsets : ∀ n, MeasurableSet (sets n))
    (hs : MeasurableSet s) {f : X → V} (hf : Integrable f μ)
    (hmem : ∀ᵐ x ∂μ, ∀ᶠ n in l, x ∈ sets n ↔ x ∈ s) :
    Tendsto (fun n => ∫ x in sets n, f x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => (sets n).indicator f x) l
      (𝓝 (s.indicator f x)) := by
    filter_upwards [hmem] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with n hn
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs, Set.indicator_of_mem (hn.mpr hxs)]
    · have hxn : x ∉ sets n := fun h => hxs (hn.mp h)
      simp only [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxn]
  have h := tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    (Eventually.of_forall fun n => hf.aestronglyMeasurable.indicator (hsets n))
    (Eventually.of_forall fun n => ae_of_all μ fun x => norm_indicator_le_norm_self f x)
    hf.norm hlim
  simpa only [integral_indicator (hsets _), integral_indicator hs] using h

/-- Integrals over affine cells, including their first moments, converge jointly
in all coefficients whenever the limiting slopes are distinct. -/
theorem tendsto_setIntegral_scoreCell {d : ℕ} {ι β V : Type*} [Finite ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Set (E d)) {l : Filter β} [l.IsCountablyGenerated]
    {ys : β → ι → E d} {cs : β → ι → ℝ} {y : ι → E d} {c : ι → ℝ}
    (i : ι) (hinj : Function.Injective y)
    (hy : ∀ j, Tendsto (fun n => ys n j) l (𝓝 (y j)))
    (hc : ∀ j, Tendsto (fun n => cs n j) l (𝓝 (c j)))
    {f : E d → V} (hf : Integrable f (uniformMeasure K)) :
    Tendsto (fun n => ∫ x in scoreCell (ys n) (cs n) i, f x ∂uniformMeasure K) l
      (𝓝 (∫ x in scoreCell y c i, f x ∂uniformMeasure K)) :=
  tendsto_setIntegral_of_ae_eventually_mem
    (fun n => measurableSet_scoreCell (ys n) (cs n) i) (measurableSet_scoreCell y c i)
    hf (ae_eventually_mem_scoreCell_iff K i hinj hy hc)

/-- Joint continuity of any integrable moment of a finite affine cell. -/
theorem continuousAt_setIntegral_scoreCell {d : ℕ} {ι V : Type*} [Finite ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι)
    (hinj : Function.Injective y) {f : E d → V} (hf : Integrable f (uniformMeasure K)) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      ∫ x in scoreCell p.1 p.2 i, f x ∂uniformMeasure K) (y, c) := by
  apply tendsto_setIntegral_scoreCell K i hinj
  · intro j
    exact ((continuous_apply j).comp continuous_fst).continuousAt
  · intro j
    exact ((continuous_apply j).comp continuous_snd).continuousAt
  · exact hf

/-- Distinctness of a finite family of sites persists locally. -/
theorem eventually_injective_sites {d : ℕ} {ι : Type*} [Finite ι]
    (y : ι → E d) (c : ι → ℝ) (hinj : Function.Injective y) :
    ∀ᶠ p : (ι → E d) × (ι → ℝ) in 𝓝 (y, c), Function.Injective p.1 := by
  have hp : ∀ i j, ∀ᶠ p : (ι → E d) × (ι → ℝ) in 𝓝 (y, c),
      i ≠ j → p.1 i ≠ p.1 j := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have hopen : IsOpen {p : (ι → E d) × (ι → ℝ) | p.1 i ≠ p.1 j} :=
        isOpen_ne_fun (by fun_prop) (by fun_prop)
      filter_upwards [hopen.mem_nhds (hinj.ne hij)] with p hp
      exact fun _ => hp
  filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hp i))]
    with p hp
  intro i j hij
  by_contra hne
  exact hp i j hne hij

/-- The configurations on which the finite-cell differential calculus is used
(distinct sites and strictly positive cell masses) form an open set. -/
theorem isOpen_distinct_positive_scoreCell {d : ℕ} {ι : Type*} [Finite ι]
    (K : Set (E d)) :
    IsOpen {p : (ι → E d) × (ι → ℝ) |
      Function.Injective p.1 ∧ ∀ i, 0 < uniformMeasure K (scoreCell p.1 p.2 i)} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨y, c⟩ ⟨hinj, hpos⟩
  have hp : ∀ i, ∀ᶠ p : (ι → E d) × (ι → ℝ) in 𝓝 (y, c),
      0 < uniformMeasure K (scoreCell p.1 p.2 i) := by
    intro i
    exact (continuousAt_uniformMeasure_scoreCell K y c i hinj).eventually
      (lt_mem_nhds (hpos i))
  filter_upwards [eventually_injective_sites y c hinj, Filter.eventually_all.mpr hp]
    with p hi hm
  exact ⟨hi, hm⟩

end Problem358

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- The geometric closed cell is the score cell restricted to the source body. -/
theorem closedCell_eq_inter_scoreCell
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι) :
    closedCell K y c i = K ∩ scoreCell y c i := by
  ext x
  simp only [closedCell, scoreCell, mem_ofPred_eq, mem_inter_iff]
  simp only [real_inner_comm x]

/-- The two cell conventions agree almost everywhere for the uniform source. -/
theorem closedCell_ae_eq_scoreCell {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) :
    closedCell K y c i =ᵐ[uniformMeasure K] scoreCell y c i := by
  filter_upwards [UniformSource.ae_mem hK] with x hx
  apply propext
  simp only [closedCell_eq_inter_scoreCell, mem_inter_iff, hx, true_and]

/-- Restricting the uniform source is independent of the cell convention. -/
theorem restrict_closedCell_eq_scoreCell {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) :
    (uniformMeasure K).restrict (closedCell K y c i) =
      (uniformMeasure K).restrict (scoreCell y c i) :=
  Measure.restrict_congr_set (closedCell_ae_eq_scoreCell hK y c i)

/-- Closed-cell masses are exactly the score-cell masses. -/
theorem uniformMeasure_closedCell_eq_scoreCell {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) :
    uniformMeasure K (closedCell K y c i) = uniformMeasure K (scoreCell y c i) :=
  measure_congr (closedCell_ae_eq_scoreCell hK y c i)

/-- Joint continuity of the actual geometric closed-cell mass at distinct sites. -/
theorem continuousAt_uniformMeasure_closedCell [Finite ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) (hinj : Function.Injective y) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      uniformMeasure K (closedCell K p.1 p.2 i)) (y, c) := by
  simpa only [uniformMeasure_closedCell_eq_scoreCell hK] using
    continuousAt_uniformMeasure_scoreCell K y c i hinj

/-- Real-valued closed-cell masses are jointly continuous at distinct sites. -/
theorem continuousAt_real_closedCell [Finite ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) (hinj : Function.Injective y) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      (uniformMeasure K).real (closedCell K p.1 p.2 i)) (y, c) := by
  let := uniformMeasure_finite K
  change ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
    (uniformMeasure K (closedCell K p.1 p.2 i)).toReal) (y, c)
  exact (ENNReal.tendsto_toReal
    (measure_ne_top (uniformMeasure K) (closedCell K y c i))).comp
    (continuousAt_uniformMeasure_closedCell hK y c i hinj)

/-- Cell integral continuity transfers to the geometric closed-cell convention. -/
theorem continuousAt_setIntegral_closedCell [Finite ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) (hinj : Function.Injective y)
    {f : E d → V} (hf : Integrable f (uniformMeasure K)) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      ∫ x in closedCell K p.1 p.2 i, f x ∂uniformMeasure K) (y, c) := by
  simpa only [restrict_closedCell_eq_scoreCell hK] using
    continuousAt_setIntegral_scoreCell K y c i hinj hf

/-- The actual first moment of a closed cell is jointly continuous. -/
theorem continuousAt_firstMoment_closedCell [Finite ι]
    {K : Set (E d)} (hK : IsCompact K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) (hinj : Function.Injective y) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      ∫ x in closedCell K p.1 p.2 i, x ∂uniformMeasure K) (y, c) :=
  continuousAt_setIntegral_closedCell hK.measurableSet y c i hinj
    (UniformSource.integrable_continuousOn hK continuous_id.continuousOn)

/-- The admissible locus used by geometric cell calculus is open, in the real-mass
convention of the normalized implicit-function construction. -/
theorem isOpen_distinct_positive_real_closedCell [Finite ι]
    {K : Set (E d)} (hK : MeasurableSet K) :
    IsOpen {p : (ι → E d) × (ι → ℝ) |
      Function.Injective p.1 ∧ ∀ i, 0 < (uniformMeasure K).real (closedCell K p.1 p.2 i)} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨y, c⟩ ⟨hinj, hpos⟩
  have hp : ∀ i, ∀ᶠ p : (ι → E d) × (ι → ℝ) in 𝓝 (y, c),
      0 < (uniformMeasure K).real (closedCell K p.1 p.2 i) := by
    intro i
    exact (continuousAt_real_closedCell hK y c i hinj).eventually
      (lt_mem_nhds (hpos i))
  filter_upwards [eventually_injective_sites y c hinj, Filter.eventually_all.mpr hp]
    with p hi hm
  exact ⟨hi, hm⟩

/-- All positive cell masses simultaneously stay between half and twice their
original masses in a neighborhood of a distinct-site configuration. -/
theorem eventually_real_closedCell_comparable [Finite ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (hinj : Function.Injective y)
    (hpos : ∀ i, 0 < (uniformMeasure K).real (closedCell K y c i)) :
    ∀ᶠ p : (ι → E d) × (ι → ℝ) in 𝓝 (y, c), ∀ i,
      (uniformMeasure K).real (closedCell K y c i) / 2 <
        (uniformMeasure K).real (closedCell K p.1 p.2 i) ∧
      (uniformMeasure K).real (closedCell K p.1 p.2 i) <
        2 * (uniformMeasure K).real (closedCell K y c i) := by
  apply Filter.eventually_all.mpr
  intro i
  have hn : Ioo ((uniformMeasure K).real (closedCell K y c i) / 2)
      (2 * (uniformMeasure K).real (closedCell K y c i)) ∈
      𝓝 ((uniformMeasure K).real (closedCell K y c i)) :=
    Ioo_mem_nhds (by linarith [hpos i]) (by linarith [hpos i])
  exact (continuousAt_real_closedCell hK y c i hinj) hn

end Problem358.CellGeometry

end

end OAI
