import OAI.GroupTheory.PolycyclicRecognition.Analysis.ThreeProbeConcentration

namespace OAI

/-! # Joint selection from product-measure concentration

Fubini selection retains a compact set of quarter mass satisfying the
product bounds for all three finite prefix families.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

theorem finite_dependent_bad_union_tendsto_zero
    {X : ℕ → Type*} {J : Type*} [∀ n, MeasurableSpace (X n)] [Fintype J]
    (μ : ∀ n, Measure (X n)) (bad : ∀ n, J → Set (X n))
    (hlim : ∀ j, Tendsto (fun n => μ n (bad n j)) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (⋃ j, bad n j)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds _
    (fun _ => zero_le) (fun n => measure_iUnion_fintype_le (μ n) (bad n))
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ => hlim j)


theorem dependent_bad_distance_triangle_tendsto_zero
    {X : ℕ → Type*} {S : Type*} [∀ n, MeasurableSpace (X n)] [PseudoMetricSpace S]
    (μ : ∀ n, Measure (X n)) (f g h : ∀ n, X n → S)
    (hfg : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    (hgh : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ n {x | ε ≤ dist (g n x) (h n x)}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => μ n {x | ε ≤ dist (f n x) (h n x)}) atTop (𝓝 0) := by
  have hb (n : ℕ) : μ n {x | ε ≤ dist (f n x) (h n x)} ≤
      μ n {x | ε / 2 ≤ dist (f n x) (g n x)} +
        μ n {x | ε / 2 ≤ dist (g n x) (h n x)} := by
    apply (measure_mono (fun x hx => ?_)).trans (measure_union_le _ _)
    by_cases hf : ε / 2 ≤ dist (f n x) (g n x)
    · exact Or.inl hf
    · right
      have hh := dist_triangle (f n x) (g n x) (h n x)
      have hx' : ε ≤ dist (f n x) (h n x) := hx
      change ε / 2 ≤ dist (g n x) (h n x)
      linarith [lt_of_not_ge hf]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds _ (fun _ => zero_le) hb
  simpa only [zero_add] using (hfg (ε / 2) (half_pos hε)).add (hgh (ε / 2) (half_pos hε))


theorem exists_compact_probes_from_supported_product_profiles
    {X S : Type*} [MeasurableSpace X] [TopologicalSpace S]
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → S) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure S)
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (profile n)) atTop (𝓝 limitLaw))
    {f : S} (hf : f ∈ (limitLaw : Measure S).support)
    (U : ℕ → Set S) (hU : ∀ j, IsOpen (U j)) (hfU : ∀ j, f ∈ U j)
    (bad : ∀ n, ℕ → Set (X × Y n)) (hbad : ∀ n j, MeasurableSet (bad n j))
    (hproduct : ∀ j,
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n)) (bad n j))
        atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ ∀ᶠ n in atTop,
      ∃ x, profile n x ∈ U (k n) ∧ ∃ K : Set (Y n), IsCompact K ∧
        K ⊆ {y | (x, y) ∉ bad n (k n)} ∧ (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) K := by
  have hpos (j : ℕ) : ∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ n in atTop,
      c ≤ (μ : Measure X) (profile n ⁻¹' U j) := by
    obtain ⟨c, hc, he⟩ := eventual_positive_mass_of_supported_weak_limit hlim hf (hU j) (hfU j)
    refine ⟨ENNReal.ofReal c, ENNReal.ofReal_pos.mpr hc, he.mono ?_⟩
    intro n hn
    rw [ProbabilityMeasure.map_apply' μ (hp n).aemeasurable (hU j).measurableSet] at hn
    exact (ENNReal.ofReal_le_ofReal hn).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))
  exact eventually_exists_compact_conditioned_probes
    (fun _ => (μ : Measure X)) (fun n => (ν n : Measure (Y n)))
    (fun n j => profile n ⁻¹' U j) bad (fun n j => hp n (hU j).measurableSet) hbad hpos
    hproduct

theorem exists_supported_product_chain_probe_sequence
    {X S C : Type*} [Nonempty X] [MeasurableSpace X]
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    [HasOuterApproxClosed (S × S)] [Fintype C]
    {Y : ℕ → Type*} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    (carrying : Set X) (hcarrying : MeasurableSet carrying)
    (hfull : (μ : Measure X) carryingᶜ = 0)
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → S × S) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure (S × S))
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (profile n)) atTop (𝓝 limitLaw))
    {f : S × S} (hf : f ∈ (limitLaw : Measure (S × S)).support)
    (chain : ∀ n, X × Y n → C → S) (sheet : C → Bool)
    (hm : ∀ n i, Measurable (fun q : X × Y n =>
      dist (chain n q i) (if sheet i then (profile n q.1).2 else (profile n q.1).1)))
    (hproduct : ∀ i (ε : ℝ), 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain n q i)
          (if sheet i then (profile n q.1).2 else (profile n q.1).1)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop,
        x n ∈ carrying ∧ dist (profile n (x n)) f < ε n ∧
        ∀ y ∈ K n, ∀ i, dist (chain n (x n, y) i)
          (if sheet i then f.2 else f.1) < 2 * ε n := by
  classical
  let tol := fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)
  have htol (j : ℕ) : 0 < tol j := by dsimp [tol]; positivity
  let comparisons := fun n j => ⋃ i : C, {q : X × Y n | tol j ≤
    dist (chain n q i) (if sheet i then (profile n q.1).2 else (profile n q.1).1)}
  let bad := fun n j => Prod.fst ⁻¹' carryingᶜ ∪ comparisons n j
  have hcomparisons (n j) : MeasurableSet (comparisons n j) :=
    MeasurableSet.iUnion (fun i => (isClosed_le continuous_const continuous_id).measurableSet.preimage
      (hm n i))
  have hbad (n j) : MeasurableSet (bad n j) :=
    (measurable_fst hcarrying.compl).union (hcomparisons n j)
  have hproduct' (j : ℕ) :
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n)) (bad n j))
        atTop (𝓝 0) := by
    have hh := finite_dependent_bad_union_tendsto_zero
      (fun n => (μ : Measure X).prod (ν n : Measure (Y n)))
      (fun n i => {q | tol j ≤ dist (chain n q i)
        (if sheet i then (profile n q.1).2 else (profile n q.1).1)})
      (fun i => hproduct i (tol j) (htol j))
    have hzero (n : ℕ) : (μ : Measure X).prod (ν n : Measure (Y n))
        (Prod.fst ⁻¹' carryingᶜ) = 0 := by
      rw [show Prod.fst ⁻¹' carryingᶜ = carryingᶜ ×ˢ (univ : Set (Y n)) by
        ext x; simp]
      rw [Measure.prod_prod, hfull, zero_mul]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds hh (fun _ => zero_le)
    intro n
    exact (measure_union_le _ _).trans (by rw [hzero n, zero_add])
  obtain ⟨k, hk, hselect⟩ := exists_compact_probes_from_supported_product_profiles
    μ ν profile hp limitLaw hlim hf (fun j => ball f (tol j))
    (fun _ => isOpen_ball) (fun j => mem_ball_self (htol j)) bad hbad hproduct'
  let ε := fun n => tol (k n)
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  obtain ⟨x, K, hK, hgood⟩ := choose_compact_good_probe_sequence ν
    (fun n x K => dist (profile n x) f < ε n ∧ K ⊆ {y | (x, y) ∉ bad n (k n)})
    (hselect.mono (by
      intro n hn
      obtain ⟨x, hx, K, hc, hs, hm⟩ := hn
      exact ⟨x, K, hc, ⟨hx, hs⟩, hm⟩))
  refine ⟨ε, x, K, fun n => htol (k n), hε, hK, ?_⟩
  filter_upwards [hgood] with n hn
  have hnonempty : (K n).Nonempty := nonempty_of_measure_ne_zero
    (ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1 / 4).trans (hK n).2.2))
  have hcar : x n ∈ carrying := by
    obtain ⟨y, hy⟩ := hnonempty
    by_contra hx
    exact hn.2 hy (Or.inl hx)
  refine ⟨hcar, hn.1, ?_⟩
  intro y hy i
  have hb : dist (chain n (x n, y) i)
      (if sheet i then (profile n (x n)).2 else (profile n (x n)).1) < ε n := by
    apply lt_of_not_ge
    intro hge
    exact hn.2 hy (Or.inr (mem_iUnion.mpr ⟨i, hge⟩))
  have hp' : dist (if sheet i then (profile n (x n)).2 else (profile n (x n)).1)
      (if sheet i then f.2 else f.1) < ε n := by
    split_ifs
    · exact lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hn.1
    · exact lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) hn.1
  exact (dist_triangle _ _ _).trans_lt (by linarith)

theorem exists_supported_product_affine_probe_sequence
    {X Z W V C : Type*} [Nonempty X] [MeasurableSpace X]
    [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [AddCommGroup V] [Module ℝ V] [Fintype C]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))]
    [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    {Y : ℕ → Type*} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    (carrying : Set X) (hcarrying : MeasurableSet carrying)
    (hfull : (μ : Measure X) carryingᶜ = 0)
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → C(Z, W) × C(Z, W)) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (profile n)) atTop (𝓝 limitLaw))
    {f : C(Z, W) × C(Z, W)} (hf : f ∈ (limitLaw : Measure (C(Z, W) × C(Z, W))).support)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : Bool → W)
    (haffine : ∀ s z, (if s then f.2 else f.1) z = A (q z) + b s)
    (chain : ∀ n, X × Y n → C → C(Z, W)) (sheet : C → Bool)
    (hm : ∀ n i, Measurable (fun p : X × Y n =>
      dist (chain n p i) (if sheet i then (profile n p.1).2 else (profile n p.1).1)))
    (hproduct : ∀ i (ε : ℝ), 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain n q i)
          (if sheet i then (profile n q.1).2 else (profile n q.1).1)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop, x n ∈ carrying ∧
        (∀ s z, ‖(if s then (profile n (x n)).2 else (profile n (x n)).1) z -
          (A (q z) + b s)‖ < ε n) ∧
        ∀ y ∈ K n, ∀ i z,
          ‖chain n (x n, y) i z - (A (q z) + b (sheet i))‖ < 2 * ε n := by
  obtain ⟨ε, x, K, hεpos, hε, hK, he⟩ := exists_supported_product_chain_probe_sequence
    μ ν carrying hcarrying hfull profile hp limitLaw hlim hf chain sheet hm hproduct
  refine ⟨ε, x, K, hεpos, hε, hK, he.mono ?_⟩
  intro n hn
  refine ⟨hn.1, ?_, ?_⟩
  · intro s z
    rw [← haffine s z, ← dist_eq_norm]
    apply (ContinuousMap.dist_apply_le_dist z).trans_lt
    have hdist : dist (if s then (profile n (x n)).2 else (profile n (x n)).1)
        (if s then f.2 else f.1) ≤ dist (profile n (x n)) f := by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.dist_eq]
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact hdist.trans_lt hn.2.1
  · intro y hy i z
    rw [← haffine (sheet i) z, ← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist z).trans_lt (hn.2.2 y hy i)

theorem exists_supported_three_product_affine_probe_sequence
    {X Z W V : Type*} [Nonempty X] [MeasurableSpace X]
    [TopologicalSpace Z] [CompactSpace Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]
    [BorelSpace (C(Z, W) × C(Z, W))]
    [HasOuterApproxClosed (C(Z, W) × C(Z, W))]
    {Y : ℕ → Type*} [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    [∀ n, Nonempty (Y n)]
    (μ : ProbabilityMeasure X) (ν : ∀ n, ProbabilityMeasure (Y n))
    (carrying : Set X) (hcarrying : MeasurableSet carrying)
    (hfull : (μ : Measure X) carryingᶜ = 0)
    [∀ n, (ν n : Measure (Y n)).InnerRegular]
    (profile : ℕ → X → C(Z, W) × C(Z, W)) (hp : ∀ n, Measurable (profile n))
    (limitLaw : ProbabilityMeasure (C(Z, W) × C(Z, W)))
    (hlim : Tendsto (fun n => ProbabilityMeasure.map μ (profile n)) atTop (𝓝 limitLaw))
    {f : C(Z, W) × C(Z, W)} (hf : f ∈ (limitLaw : Measure (C(Z, W) × C(Z, W))).support)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : Bool → W)
    (haffine : ∀ s z, (if s then f.2 else f.1) z = A (q z) + b s)
    {N₀ N₁ N₂ : ℕ}
    (chain₀ : ∀ n, X × Y n → Fin (N₀ + 1) → C(Z, W))
    (chain₁ : ∀ n, X × Y n → Fin (N₁ + 1) → C(Z, W))
    (chain₂ : ∀ n, X × Y n → Fin (N₂ + 1) → C(Z, W))
    (hm₀ : ∀ n j, Measurable (fun p => chain₀ n p j))
    (hm₁ : ∀ n j, Measurable (fun p => chain₁ n p j))
    (hm₂ : ∀ n j, Measurable (fun p => chain₂ n p j))
    (hstart : ∀ n p, chain₂ n p 0 = chain₁ n p (Fin.last N₁))
    (hc₀ : ∀ j ε, 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain₀ n q j) (profile n q.1).1}) atTop (𝓝 0))
    (hc₁ : ∀ j ε, 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain₁ n q j) (profile n q.1).2}) atTop (𝓝 0))
    (hc₂ : ∀ j ε, 0 < ε →
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain₂ n q j) (chain₂ n q 0)}) atTop (𝓝 0)) :
    ∃ (ε : ℕ → ℝ) (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop, x n ∈ carrying ∧
        (∀ s z, ‖(if s then (profile n (x n)).2 else (profile n (x n)).1) z -
          (A (q z) + b s)‖ < ε n) ∧
        (∀ y ∈ K n, ∀ j z, ‖chain₀ n (x n, y) j z - (A (q z) + b false)‖ < 2 * ε n) ∧
        (∀ y ∈ K n, ∀ j z, ‖chain₁ n (x n, y) j z - (A (q z) + b true)‖ < 2 * ε n) ∧
        ∀ y ∈ K n, ∀ j z, ‖chain₂ n (x n, y) j z - (A (q z) + b true)‖ < 2 * ε n := by
  let C := Fin (N₀ + 1) ⊕ (Fin (N₁ + 1) ⊕ Fin (N₂ + 1))
  let chain : ∀ n, X × Y n → C → C(Z, W) := fun n p =>
    Sum.elim (chain₀ n p) (Sum.elim (chain₁ n p) (chain₂ n p))
  let sheet : C → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have hm (n : ℕ) (j : C) : Measurable (fun p => dist (chain n p j)
      (if sheet j then (profile n p.1).2 else (profile n p.1).1)) := by
    rcases j with j | j | j
    · exact continuous_dist.measurable.comp
        ((hm₀ n j).prodMk (((hp n).fst).comp measurable_fst))
    · exact continuous_dist.measurable.comp
        ((hm₁ n j).prodMk (((hp n).snd).comp measurable_fst))
    · exact continuous_dist.measurable.comp
        ((hm₂ n j).prodMk (((hp n).snd).comp measurable_fst))
  have hc (j : C) (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => (μ : Measure X).prod (ν n : Measure (Y n))
        {q | ε ≤ dist (chain n q j)
          (if sheet j then (profile n q.1).2 else (profile n q.1).1)}) atTop (𝓝 0) := by
    rcases j with j | j | j
    · exact hc₀ j ε hε
    · exact hc₁ j ε hε
    · apply dependent_bad_distance_triangle_tendsto_zero
        (fun n => (μ : Measure X).prod (ν n : Measure (Y n)))
        (fun n q => chain₂ n q j)
        (fun n q => chain₁ n q (Fin.last N₁))
        (fun n q => (profile n q.1).2) _ (fun ε hε => hc₁ _ ε hε) ε hε
      intro δ hδ
      simpa only [hstart] using hc₂ j δ hδ
  obtain ⟨ε, x, K, hεpos, hε, hK, he⟩ := exists_supported_product_affine_probe_sequence
    μ ν carrying hcarrying hfull profile hp limitLaw hlim hf q A b haffine chain sheet hm hc
  refine ⟨ε, x, K, hεpos, hε, hK, he.mono ?_⟩
  intro n hn
  exact ⟨hn.1, hn.2.1,
    fun y hy j z => hn.2.2 y hy (Sum.inl j) z,
    fun y hy j z => hn.2.2 y hy (Sum.inr (Sum.inl j)) z,
    fun y hy j z => hn.2.2 y hy (Sum.inr (Sum.inr j)) z⟩

end PolycyclicRecognition

end

end OAI
