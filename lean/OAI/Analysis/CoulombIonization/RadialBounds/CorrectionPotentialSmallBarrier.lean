import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierDilationBarrier

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

lemma potential_tendsto_zero_of_shrinking_support {ι : Type*} {F : Filter ι}
    {ρ : ι → TFSpace → ℝ} {a : ι → ℝ} {x : TFSpace} (hx : x ≠ 0)
    (hm : ∀ j, Measurable (ρ j)) (hi : ∀ j, Integrable (ρ j))
    (hn : ∀ j z, 0 ≤ ρ j z)
    (hs : ∀ j z, a j < ‖z‖ → ρ j z = 0)
    (ha : Tendsto a F (𝓝 0)) (hMass : Tendsto (fun j => ∫ z, ρ j z) F (𝓝 0)) :
    Tendsto (fun j => tfPotential (ρ j) x) F (𝓝 0) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply potential_tendsto_zero_of_local_mass (L := fun _ => 0)
    (b := ‖x‖/2) (by positivity) hm hi hn _ tendsto_const_nhds hMass
  filter_upwards [ha.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < ‖x‖/2))] with j hj
  intro z hz
  have hnorm : ‖x‖ ≤ ‖x-z‖+‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-z) z
  have hzs : a j < ‖z‖ := by change a j < ‖x‖/2 at hj; linarith
  rw [hs j z hzs]

lemma bounded_compact_mass_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {L S : ℝ} (_hL : 0 ≤ L) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ L)
    (hs : ∀ z, S < ‖z‖ → ρ z = 0) :
    Integrable ρ ∧ (∫ z, ρ z) ≤ volume.real (closedBall (0:TFSpace) S)*L := by
  have hmajor : ∀ z, ρ z ≤ (closedBall (0:TFSpace) S).indicator (fun _ => L) z := by
    intro z
    by_cases hz : ‖z‖ ≤ S
    · rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hz)]
      exact hb z
    · rw [indicator_of_notMem (by simpa only [mem_closedBall_zero_iff] using hz),hs z (lt_of_not_ge hz)]
  have hI : Integrable ((closedBall (0:TFSpace) S).indicator (fun _ => L)) :=
    (integrableOn_const (C := L) measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hρ : Integrable ρ := hI.mono' hm.aestronglyMeasurable (ae_of_all _ fun z => by
    simpa only [Real.norm_of_nonneg (hn z)] using hmajor z)
  refine ⟨hρ,(integral_mono hρ hI hmajor).trans_eq ?_⟩
  rw [integral_indicator measurableSet_closedBall,setIntegral_const,smul_eq_mul]

lemma potential_tendsto_zero_of_compact_bound {ι : Type*} {F : Filter ι}
    {ρ : ι → TFSpace → ℝ} {L : ι → ℝ} {S : ℝ} (x : TFSpace)
    (hm : ∀ j, Measurable (ρ j)) (hL : ∀ j, 0 ≤ L j)
    (hn : ∀ j z, 0 ≤ ρ j z) (hb : ∀ j z, ρ j z ≤ L j)
    (hs : ∀ j z, S < ‖z‖ → ρ j z = 0) (hlim : Tendsto L F (𝓝 0)) :
    Tendsto (fun j => tfPotential (ρ j) x) F (𝓝 0) := by
  have hi := fun j => bounded_compact_mass_le (hm j) (hL j) (hn j) (hb j) (hs j)
  apply potential_tendsto_zero_of_local_mass (b := 1) (by norm_num) hm
    (fun j => (hi j).1) hn (Eventually.of_forall fun j z _ => hb j z) hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [mul_zero] using hlim.const_mul (volume.real (closedBall (0:TFSpace) S)))
  · exact Eventually.of_forall fun j => integral_nonneg (hn j)
  · exact Eventually.of_forall fun j => (hi j).2

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

def annularApproximationError (l a S : ℝ) (x : TFSpace) : ℝ :=
  {x : TFSpace | a ≤ ‖x‖ ∧ ‖x‖ ≤ S}.indicator (fun x => l⁻¹^8/‖x‖^6) x

lemma annularApproximationError_measurable (l a S : ℝ) :
    Measurable (annularApproximationError l a S) :=
  (measurable_const.div (measurable_norm.pow_const 6)).indicator
    ((measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const))

lemma annularApproximationError_nonneg (l a S : ℝ) (x : TFSpace) :
    0 ≤ annularApproximationError l a S x :=
  indicator_nonneg (fun _ _ => div_nonneg (by positivity) (by positivity)) _

lemma annularApproximationError_support (l a S : ℝ) (x : TFSpace) (hx : S < ‖x‖) :
    annularApproximationError l a S x = 0 :=
  indicator_of_notMem (fun h => (not_le.mpr hx) h.2) _

lemma annularApproximationError_bound {l a S : ℝ} (hl : 0 < l) (ha : 1/(2*l) ≤ a)
    (x : TFSpace) : annularApproximationError l a S x ≤ 64*l⁻¹^2 := by
  by_cases hx : a ≤ ‖x‖ ∧ ‖x‖ ≤ S
  · rw [annularApproximationError,indicator_of_mem (show x ∈ {x : TFSpace | a ≤ ‖x‖ ∧ ‖x‖ ≤ S} from hx)]
    have hnear : 0 < 1/(2*l) := by positivity
    calc
      _ ≤ l⁻¹^8/(1/(2*l))^6 := div_le_div_of_nonneg_left (by positivity)
        (pow_pos hnear 6) (pow_le_pow_left₀ hnear.le (ha.trans hx.1) 6)
      _ = _ := by field_simp [hl.ne']; ring
  · rw [annularApproximationError,indicator_of_notMem (show x ∉ {x : TFSpace | a ≤ ‖x‖ ∧ ‖x‖ ≤ S} from hx)]
    positivity

lemma annular_correction_potential_tendsto_zero {ι : Type*} {F : Filter ι}
    {l a : ι → ℝ} {S : ℝ} (x : TFSpace)
    (hl : ∀ j, 0 < l j) (ha : ∀ j, 1/(2*l j) ≤ a j) (ht : Tendsto l F atTop) :
    Tendsto (fun j => tfPotential (annularApproximationError (l j) (a j) S) x) F (𝓝 0) := by
  apply potential_tendsto_zero_of_compact_bound (L := fun j => 64*(l j)⁻¹^2) x
    (fun j => annularApproximationError_measurable _ _ _) (fun _ => by positivity)
    (fun j => annularApproximationError_nonneg _ _ _)
    (fun j => annularApproximationError_bound (hl j) (ha j))
    (fun j => annularApproximationError_support _ _ _)
  simpa using ((tendsto_inv_atTop_zero.comp ht).pow 2).const_mul (64:ℝ)

end CoulombAnalysis

end

end OAI
