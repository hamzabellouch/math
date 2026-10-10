import OAI.NumberTheory.DukePrimeDegree.Dynamics.ErgodicL2Averages

namespace OAI

/-!
# Identifying the constant ergodic average

The constant obtained from the L2 mean ergodic theorem is the integral
of the original observable. Integration is represented by pairing with
the constant-one vector, so passage to the limit is continuous in L2.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

/-- Constant observables as actual L2 vectors. -/
def constantL2 (μ : Measure X) [IsFiniteMeasure μ] (c : ℝ) : Lp ℝ 2 μ :=
  (memLp_const c : MemLp (fun _ : X => c) 2 μ).toLp (fun _ => c)

lemma constantL2_ae (μ : Measure X) [IsFiniteMeasure μ] (c : ℝ) :
    (constantL2 μ c : X → ℝ) =ᵐ[μ] fun _ => c :=
  (memLp_const c).coeFn_toLp

/-- Integration is the continuous L2 pairing with the constant one. -/
def meanL2 (μ : Measure X) [IsFiniteMeasure μ] : Lp ℝ 2 μ →L[ℝ] ℝ :=
  innerSL ℝ (constantL2 μ 1)

lemma meanL2_apply (μ : Measure X) [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    meanL2 μ f = ∫ x, f x ∂μ := by
  change inner ℝ (constantL2 μ 1) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [constantL2_ae μ 1] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_one]

lemma meanL2_constant (μ : Measure X) [IsProbabilityMeasure μ] (c : ℝ) :
    meanL2 μ (constantL2 μ c) = c := by
  rw [meanL2_apply]
  exact integral_eq_const (constantL2_ae μ c)

lemma meanL2_koopman (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) :
    meanL2 μ (Lp.compMeasurePreserving T hT f) = meanL2 μ f := by
  rw [meanL2_apply, meanL2_apply]
  calc
    _ = ∫ x, f (T x) ∂μ := integral_congr_ae (Lp.coeFn_compMeasurePreserving f hT)
    _ = ∫ x, f x ∂μ := by
      have hfmap : AEStronglyMeasurable (fun x => f x) (μ.map T) := by
        rw [hT.map_eq]
        exact Lp.aestronglyMeasurable f
      have he := integral_map (μ := μ) (φ := T) (f := fun x => f x)
        hT.measurable.aemeasurable hfmap
      rw [hT.map_eq] at he
      exact he.symm

lemma meanL2_iterate (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) (n : ℕ) :
    meanL2 μ ((Lp.compMeasurePreserving T hT)^[n] f) = meanL2 μ f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', meanL2_koopman, ih]

lemma meanL2_birkhoffAverage (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ)
    (n : ℕ) (hn : n ≠ 0) :
    meanL2 μ (birkhoffAverage ℝ (Lp.compMeasurePreserving T hT) id n f) = meanL2 μ f := by
  simp only [birkhoffAverage, birkhoffSum, map_smul, map_sum, meanL2_iterate,
    id_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- The L2 limit is the original integral, with no generic-point
hypothesis. -/
theorem L2_orbit_average_tendsto_integral
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Ergodic T μ) (f : Lp ℝ 2 μ) :
    Tendsto (fun N => birkhoffAverage ℝ (Lp.compMeasurePreserving T hT.toMeasurePreserving)
      id N f) atTop (𝓝 (constantL2 μ (∫ x, f x ∂μ))) := by
  obtain ⟨c, hc⟩ := exists_constant_L2_orbit_average μ T hT f
  change Tendsto _ atTop (𝓝 (constantL2 μ c)) at hc
  have hmean := (meanL2 μ).continuous.tendsto (constantL2 μ c) |>.comp hc
  have hsame : Tendsto
      (fun N => meanL2 μ (birkhoffAverage ℝ
        (Lp.compMeasurePreserving T hT.toMeasurePreserving) id N f))
      atTop (𝓝 (meanL2 μ f)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (meanL2_birkhoffAverage μ T hT.toMeasurePreserving f n (Nat.ne_of_gt hn)).symm
  have he : meanL2 μ (constantL2 μ c) = meanL2 μ f :=
    tendsto_nhds_unique hmean hsame
  rw [meanL2_constant, meanL2_apply] at he
  rwa [he] at hc

end DukePrimeDegree

end

end OAI
