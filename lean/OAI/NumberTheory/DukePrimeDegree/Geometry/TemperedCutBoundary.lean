import OAI.NumberTheory.DukePrimeDegree.Geometry.ExponentialCutBoundary
import OAI.NumberTheory.DukePrimeDegree.Geometry.TemperedChartRadius

namespace OAI

/-! # Boundary avoidance up to the actual orbit height

The proper height grows sublinearly without an integrability assumption.
It is therefore eventually below a sufficiently slow linear cutoff,
where the exponential boundary budget is summable.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace DukePrimeDegree

theorem ae_eventually_avoid_cuts_up_to_height
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1)
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Measurable (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hbound : ∀ m i k, μ (realBoundaryStrip (f m i) (c m i) ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (D m*(1/2:ℝ)^k))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsize : ∀ m, (N m:ℝ≥0∞)*ENNReal.ofReal (D m) ≤
      ENNReal.ofReal (K*Real.exp (C*(m:ℝ)))) :
    ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, ∀ m ≤ H (T^[k] x), ∀ i,
      (1/4:ℝ)^k < |f m i (T^[k] x)-c m i| := by
  let δ := Real.log 2/(2*(C+1))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCp : 0 < C+1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdecay : C*δ < Real.log 2 := by
    calc
      _ ≤ (C+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = Real.log 2/2 := by dsimp [δ]; field_simp
      _ < _ := by linarith
  let L (k : ℕ) := ⌊δ*(k:ℝ)⌋₊
  have hL (k : ℕ) : (L k:ℝ) ≤ δ*(k:ℝ) := Nat.floor_le (by positivity)
  have havoid := ae_eventually_avoid_exponential_cut_levels μ hT N f hf c D hD hbound
    L hC hK hsize hL hdecay
  filter_upwards [havoid,ae_height_div_tendsto_zero μ hT H hH hstep] with x hx hsub
  filter_upwards [hx,hsub.eventually (gt_mem_nhds hδ),eventually_ge_atTop 1]
    with k hk hsmall hkp
  have hkp' : 0 < (k:ℝ) := by exact_mod_cast hkp
  have hheight : H (T^[k] x) ≤ L k := by
    apply Nat.le_floor
    exact ((div_lt_iff₀ hkp').mp hsmall).le
  intro m hm i
  exact hk m (hm.trans hheight) i

end DukePrimeDegree

end

end OAI
