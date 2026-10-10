import Mathlib
import OAI.Probability.Ballisticity.Estimates.GridOccupation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

def heightTubeEndpointEvent (Y : ℕ → ℝ) (H : ℕ) (L R : ℝ) : Prop :=
  (∀ j ≤ H, |Y j| ≤ L) ∧ |Y H| ≤ R

lemma measurableSet_heightTubeEndpointEvent {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) (hY : ∀ j, Measurable (Y j)) (H : ℕ) (L R : ℝ) :
    MeasurableSet {x | heightTubeEndpointEvent (fun j => Y j x) H L R} := by
  change MeasurableSet ({x | ∀ j ≤ H, |Y j x| ≤ L} ∩ {x | |Y H x| ≤ R})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (hY j).abs measurable_const
  · exact measurableSet_le (hY H).abs measurable_const

lemma heightPolygon_window_implies_tube (Y : ℕ → ℝ) (r n : ℝ) (hr : 0 < r) (hn : 0 < n)
    (B L ρ δ : ℝ) (hBL : B ≤ L) (τ : unitInterval)
    (hg : ‖heightPolygon Y r n 2‖ < B)
    (he : ∀ t : unitInterval, dist t τ ≤ δ → |heightPolygon Y r n 2 t| < ρ)
    (ht : dist (layerGridPoint (2*n) ⌊n⌋₊) τ ≤ δ) :
    heightTubeEndpointEvent Y ⌊n⌋₊ (L*r) (ρ*r) := by
  have h2n : 0 < 2*n := by positivity
  have hj (j : ℕ) (h : j ≤ ⌊n⌋₊) : (j:ℝ) ≤ 2*n := by
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    have hfloor := Nat.floor_le hn.le
    linarith
  have heval (j : ℕ) (h : j ≤ ⌊n⌋₊) : heightPolygon Y r n 2 (layerGridPoint (2*n) j)=Y j/r := by
    apply heightPolygon_grid _ _ _ _ h2n.le
    rw [layerGridPoint_coe h2n (hj j h),mul_div_cancel₀ _ h2n.ne']
  constructor
  · intro j h
    have hh := (heightPolygon Y r n 2).norm_coe_le_norm (layerGridPoint (2*n) j)
    rw [heval j h,Real.norm_eq_abs,abs_div,abs_of_pos hr] at hh
    exact ((div_le_iff₀ hr).mp (hh.trans (hg.le.trans hBL)))
  · have hh := he _ ht
    rw [heval ⌊n⌋₊ le_rfl,abs_div,abs_of_pos hr] at hh
    exact ((div_lt_iff₀ hr).mp hh).le

lemma half_layer_grid_tendsto (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun i => layerGridPoint (2*n i) ⌊n i⌋₊) atTop
      (𝓝 (⟨(1:ℝ)/2,by norm_num,by norm_num⟩ : unitInterval)) := by
  apply layerGridPoint_tendsto
  have hh := ((tendsto_nat_floor_mul_div_atTop (by norm_num : (0:ℝ)≤1)).comp hn).div_const 2
  convert hh using 1
  simp only [one_mul,Function.comp_def]
  funext i
  ring

end DirectionalTransience

end

end

end OAI
