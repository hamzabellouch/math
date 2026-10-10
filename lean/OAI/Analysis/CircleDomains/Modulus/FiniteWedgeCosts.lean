import OAI.Analysis.CircleDomains.Sobolev.WedgeIntegrability
import OAI.Analysis.CircleDomains.Selection.TerminalCounts

namespace OAI

/-!
# The complete finite-list random wedge cost

The actual spatial wedge integrals are integrable random variables.
Summing their independent-pair estimates gives a mean bound uniform in
the staircase width, with an error proportional to the grid spacing.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

noncomputable def staircaseWidth (h : ℝ) (k : ℕ) : ℝ :=
  h / 8 * reciprocalGridStep k

theorem staircaseWidth_pos {h : ℝ} (hh : 0 < h) (k : ℕ) :
    0 < staircaseWidth h k := mul_pos (by positivity) (reciprocalGridStep_pos k)

theorem staircaseWidth_lt {h : ℝ} (hh : 0 < h) (k : ℕ) :
    staircaseWidth h k < h / 4 := by
  have hle := mul_le_mul_of_nonneg_left (reciprocalGridStep_le_one k)
    (by positivity : 0 ≤ h / 8)
  dsimp only [staircaseWidth]
  nlinarith

theorem staircaseWidth_tendsto_zero (h : ℝ) :
    Tendsto (staircaseWidth h) atTop (𝓝 0) := by
  change Tendsto (fun k => h / 8 * reciprocalGridStep k) atTop (𝓝 0)
  simpa only [mul_zero] using reciprocalGridStep_tendsto_zero.const_mul (h / 8)

noncomputable def staircasePairCost {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {n : ℕ} (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ) (h δ : ℝ) (i j : Fin n) (θ : Fin n → ℝ) : ℝ :=
  ∫ z, |planarWedge
    (staircaseCovector h δ (χ z) (θ i) (x i z) (u i z) (c z))
    (staircaseCovector h δ (χ z) (θ j) (x j z) (u j z) (c z))| ∂μ

noncomputable def staircaseWedgeCost {X P : Type*} [MeasurableSpace X] [Fintype P]
    (μ : Measure X) {n : ℕ} (pairs : P → Fin n × Fin n)
    (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ) (h δ : ℝ) (θ : Fin n → ℝ) : ℝ :=
  ∑ p, staircasePairCost μ u c x χ h δ (pairs p).1 (pairs p).2 θ

theorem integrable_staircasePairCost
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ] {n : ℕ}
    (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ) (x : Fin n → X → ℝ) (χ : X → ℝ)
    (hu : ∀ i, Measurable (u i)) (hc : Measurable c)
    (hx : ∀ i, Measurable (x i)) (hχ : Measurable χ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    {i j : Fin n} (hij : i ≠ j)
    (hbound : Integrable (fun z => |planarWedge (u i z) (u j z)| +
      h * (|planarWedge (u i z) (c z)| + |planarWedge (c z) (u j z)|)) μ) :
    Integrable (staircasePairCost μ u c x χ h δ i j)
      (Measure.pi (fun _ : Fin n => shiftLaw h)) := by
  let := shiftLaw_isProbabilityMeasure hh
  have hjoint := integrable_staircase_pair_density (u i) (u j) c (x i) (x j) χ
    (hu i) (hu j) hc (hx i) (hx j) hχ hh hδ hδh hχ0 hχ1 hbound
  exact (measurePreserving_grid_pair (shiftLaw h) hij).integrable_comp_of_integrable
    hjoint.integral_prod_left

theorem staircaseWedgeCost_nonneg
    {X P : Type*} [MeasurableSpace X] [Fintype P] (μ : Measure X) {n : ℕ}
    (pairs : P → Fin n × Fin n) (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ)
    (x : Fin n → X → ℝ) (χ : X → ℝ) (h δ : ℝ) (θ : Fin n → ℝ) :
    0 ≤ staircaseWedgeCost μ pairs u c x χ h δ θ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))

/-- The finite-list mean estimate, with no joint-integrability premise.
The original pairwise wedges and cutoff correction terms suffice. -/
theorem integrable_staircaseWedgeCost_and_mean_le
    {X P : Type*} [MeasurableSpace X] [Fintype P] {μ : Measure X} [SFinite μ] {n : ℕ}
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ) (x : Fin n → X → ℝ) (χ : X → ℝ)
    (hu : ∀ i, Measurable (u i)) (hc : Measurable c)
    (hx : ∀ i, Measurable (x i)) (hχ : Measurable χ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hbase : ∀ p, Integrable (fun z => |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)|) μ)
    (herr : ∀ p, Integrable (fun z => |planarWedge (u (pairs p).1 z) (c z)| +
      |planarWedge (c z) (u (pairs p).2 z)|) μ) :
    Integrable (staircaseWedgeCost μ pairs u c x χ h δ)
        (Measure.pi (fun _ : Fin n => shiftLaw h)) ∧
      (∫ θ, staircaseWedgeCost μ pairs u c x χ h δ θ
        ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
        (∑ p, ∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂μ) +
          h * (∑ p, ∫ z, |planarWedge (u (pairs p).1 z) (c z)| +
            |planarWedge (c z) (u (pairs p).2 z)| ∂μ) := by
  have hb p := (hbase p).add ((herr p).const_mul h)
  have hi p := integrable_staircasePairCost u c x χ hu hc hx hχ
    hh hδ hδh hχ0 hχ1 (hpairs p) (hb p)
  refine ⟨integrable_finsetSum _ (fun p _ => hi p), ?_⟩
  unfold staircaseWedgeCost
  rw [integral_finsetSum _ (fun p _ => hi p)]
  calc
    _ ≤ ∑ p, ∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| +
        h * (|planarWedge (u (pairs p).1 z) (c z)| +
          |planarWedge (c z) (u (pairs p).2 z)|) ∂μ := by
      apply Finset.sum_le_sum
      intro p _
      exact expected_integrated_grid_pair_wedge_le (hpairs p)
        (u (pairs p).1) (u (pairs p).2) c (x (pairs p).1) (x (pairs p).2) χ
        hh hδ hδh hχ0 hχ1
        (integrable_staircase_pair_density _ _ _ _ _ _
          (hu _) (hu _) hc (hx _) (hx _) hχ hh hδ hδh hχ0 hχ1 (hb p)) (hb p)
    _ = _ := by
      simp only [integral_add (hbase _) ((herr _).const_mul h), integral_const_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The grid-selection stage with the actual constructed wedge cost,
actual terminal set, and explicit sequence of widths tending to zero.
Its spatial hypotheses are the original square-integrable covectors
and a small original wedge sum outside the retained core. -/
theorem exists_grid_for_actual_wedge_cost
    {X P S : Type*} [MeasurableSpace X] [Fintype P] [Countable S]
    {μ : Measure X} [SFinite μ] {n : ℕ}
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (u : Fin n → X → ℝ × ℝ) (c : X → ℝ × ℝ) (x : Fin n → X → ℝ) (χ : X → ℝ)
    (hu : ∀ i, Measurable (u i)) (hc : Measurable c)
    (hx : ∀ i, Measurable (x i)) (hχ : Measurable χ)
    (hu2 : ∀ i, MemLp (u i) 2 μ) (hc2 : MemLp c 2 μ)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (Q : ℕ → (Fin n → ℝ) → Prop)
    (hQ : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, Q N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hsmall : (∑ p, ∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂μ) < η / 4) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < ρ ∧ Q N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).ncard : ℝ) < η ∧
      ∃ᶠ k in atTop, staircaseWedgeCost μ pairs u c x χ (reciprocalGridStep N)
        (staircaseWidth (reciprocalGridStep N) k) θ < η := by
  have hbase p := integrable_abs_planarWedge_of_memLp (hu2 (pairs p).1) (hu2 (pairs p).2)
  have herr p := (integrable_abs_planarWedge_of_memLp (hu2 (pairs p).1) hc2).add
    (integrable_abs_planarWedge_of_memLp hc2 (hu2 (pairs p).2))
  let W : ℕ → ℕ → (Fin n → ℝ) → ℝ := fun N k =>
    staircaseWedgeCost μ pairs u c x χ (reciprocalGridStep N)
      (staircaseWidth (reciprocalGridStep N) k)
  have hestimate N k := integrable_staircaseWedgeCost_and_mean_le pairs hpairs
    u c x χ hu hc hx hχ (reciprocalGridStep_pos N)
    (staircaseWidth_pos (reciprocalGridStep_pos N) k)
    (staircaseWidth_lt (reciprocalGridStep_pos N) k) hχ0 hχ1 hbase herr
  have hlimit := ((reciprocalGridStep_tendsto_zero.mul_const
    (∑ p, ∫ z, |planarWedge (u (pairs p).1 z) (c z)| +
      |planarWedge (c z) (u (pairs p).2 z)| ∂μ)).const_add
        (∑ p, ∫ z, |planarWedge (u (pairs p).1 z) (u (pairs p).2 z)| ∂μ))
  simp only [zero_mul, add_zero] at hlimit
  have hmean : ∀ᶠ N in atTop, ∀ k, (∫ θ, W N k θ ∂reciprocalGridLaw n N) < η / 4 := by
    filter_upwards [hlimit.eventually_lt_const hsmall] with N hN k
    exact (hestimate N k).2.trans_lt hN
  exact exists_grid_with_finite_terminals_and_good_widths F hF pairs hpairs a b
    hwidth hwidth2 W Q hη hρ (fun N k => (hestimate N k).1)
    (fun N k => Filter.Eventually.of_forall
      (staircaseWedgeCost_nonneg μ pairs u c x χ _ _)) hQ hmean

end CircleDomainRigidity.FiniteTransfer

end OAI
