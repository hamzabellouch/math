import OAI.Probability.SLE.BoundaryDensity

namespace OAI

/-! Simultaneous bounded adapted logarithmic Loewner coordinates. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge.Multipoint

lemma measurable_clipped_multipoint_velocity
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Q : ℝ → Ω → (ι → ℂ × ℝ)) (U : ℝ → Ω → ℝ)
    (hQ : Measurable (fun p : ℝ × Ω => Q p.1 p.2))
    (hU : Measurable (fun p : ℝ × Ω => U p.1 p.2))
    (lo hi : ℝ) (hle : lo ≤ hi) :
    Measurable (fun p : ℝ × Ω => fun i =>
      clippedLogLoewnerField lo hi hle (U p.1 p.2) (Q p.1 p.2 i)) := by
  apply Measurable.of_eval
  intro i
  have hqi : Measurable (fun p : ℝ × Ω => Q p.1 p.2 i) :=
    (measurable_pi_apply i).comp hQ
  have hf : Measurable (fun p : ℝ × (ℂ × ℝ) =>
      clippedLogLoewnerField lo hi hle p.1 p.2) :=
    (continuous_clippedLogLoewnerField lo hi hle).measurable
  have hp : Measurable (fun p : ℝ × Ω => (U p.1 p.2,Q p.1 p.2 i)) := hU.prodMk hqi
  change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
    (fun p : ℝ × Ω => (U p.1 p.2,Q p.1 p.2 i)))
  exact hf.comp hp

theorem exists_clipped_multipoint_state
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ lo hi : ℝ) (hle : lo ≤ hi) (q₀ : ι → ℂ × ℝ) :
    ∃ (L : ℝ≥0) (Q V : ℝ → Ω → (ι → ℂ × ℝ)),
      Measurable (fun p : ℝ × Ω => Q p.1 p.2) ∧
      Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun t : ℝ≥0 => Q t) ∧
      (∀ ω, LipschitzWith L (fun t => Q t ω)) ∧
      Measurable (fun p : ℝ × Ω => V p.1 p.2) ∧
      (∀ t ω, ‖V t ω‖ ≤ L) ∧
      (∀ ω, ∀ᵐ t : ℝ, 0 < t → HasDerivAt (fun u => Q u ω) (V t ω) t) ∧
      (∀ ω t, 0 ≤ t → HasDerivWithinAt (fun u => Q u ω) (V t ω) (Ici 0) t) ∧
      (∀ ω, Q 0 ω = q₀) ∧
      (∀ t ω i, V t ω i = clippedLogLoewnerField lo hi hle
        (Real.sqrt κ*B t.toNNReal ω) (Q t ω i)) := by
  classical
  let c (i : ι) : ClippedLogSolution B hm κ lo hi hle (q₀ i) :=
    Classical.choice (exists_clippedLogSolution B hm hBm hBc κ lo hi hle (q₀ i))
  clear_value c
  obtain ⟨L₀, K₀, hbound, _⟩ := clippedLogLoewnerField_bounds lo hi hle
  let L : ℝ≥0 := L₀ + ∑ i, (c i).L
  let Q := fun t ω i => (c i).Q t ω
  let V := fun t ω i => clippedLogLoewnerField lo hi hle
    (Real.sqrt κ*B t.toNNReal ω) (Q t ω i)
  have hLi (i : ι) : (c i).L ≤ L := by
    change (c i).L ≤ L₀+∑ j, (c j).L
    exact (Finset.single_le_sum (fun j _ => (zero_le : 0 ≤ (c j).L)) (Finset.mem_univ i)).trans
      (le_add_left le_rfl)
  have hL₀ : L₀ ≤ L := le_add_of_nonneg_right (by positivity)
  have hQm : Measurable (fun p : ℝ × Ω => Q p.1 p.2) :=
    Measurable.of_eval (fun i => (c i).measurable)
  have hQadapt (t : ℝ≥0) (i : ι) :
      @Measurable Ω (ℂ × ℝ)
        ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)) t) _
        (fun ω => Q t ω i) := (c i).adapted t
  have hUm : Measurable (fun p : ℝ × Ω => Real.sqrt κ*B p.1.toNNReal p.2) :=
    (hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)).const_mul _
  refine ⟨L, Q, V, hQm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    let : MeasurableSpace Ω := (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) t
    exact Measurable.of_eval (hQadapt t)
  · intro ω
    apply LipschitzWith.of_dist_le_mul
    intro t u
    apply (dist_pi_le_iff (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
    intro i
    exact ((c i).lipschitz ω).dist_le_mul t u |>.trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hLi i) dist_nonneg)
  · exact measurable_clipped_multipoint_velocity Q
      (fun t ω => Real.sqrt κ * B t.toNNReal ω) hQm hUm lo hi hle
  · intro t ω
    apply (pi_norm_le_iff_of_nonneg L.coe_nonneg).mpr
    intro i
    change ‖clippedLogLoewnerField lo hi hle
      (Real.sqrt κ * B t.toNNReal ω) (Q t ω i)‖ ≤ (L : ℝ)
    have hb := hbound (Real.sqrt κ * B t.toNNReal ω) (Q t ω i)
    exact hb.trans (by exact_mod_cast hL₀)
  · intro ω
    exact Eventually.of_forall fun t ht => hasDerivAt_pi.mpr fun i =>
      ((c i).derivative ω t ht.le).hasDerivAt (Ici_mem_nhds ht)
  · intro ω t ht
    exact hasDerivWithinAt_pi.mpr (fun i => (c i).derivative ω t ht)
  · intro ω
    funext i
    exact (c i).initial ω
  · intro t ω i
    rfl

end SLEExactGauge.Multipoint

end

end OAI
