import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTowerBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierOuterWeakBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.NuclearDilationBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierDilation_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma reaction_dilation {b : ℝ} (hb : 0 < b) (k t : ℝ) :
    reaction k (b^4*t) = b^6*reaction k t := by
  have hm : max (b^4*t) 0 = b^4*max t 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg hb.le 4),mul_zero]
  have hp : (b^4)^(3/2:ℝ) = b^6 := by
    rw [←Real.rpow_natCast b 4,←Real.rpow_mul hb.le]
    norm_num [Real.rpow_natCast]
  rw [reaction,hm,Real.mul_rpow (pow_nonneg hb.le 4) (le_max_right _ _),hp,reaction]
  ring

lemma innerSource_dilation {b : ℝ} (hb : 0 < b) (r : ℝ) (μ p : TFSpace → ℝ)
    (x : TFSpace) : tfDilation b (innerSource r μ p) x =
      innerSource (r/b) (tfDilation b μ) (tfDilation b p) x := by
  have he : ‖b • x‖ < r ↔ ‖x‖ < r/b := by
    rw [norm_smul,Real.norm_of_nonneg hb.le,lt_div_iff₀ hb,mul_comm]
  simp only [tfDilation,innerSource,he]
  split_ifs <;> ring

lemma outerCoefficient_dilation {b : ℝ} (hb : 0 < b) (r : ℝ) (x : TFSpace) :
    outerCoefficient r (b • x) = outerCoefficient (r/b) x := by
  have he : r ≤ ‖b • x‖ ↔ r/b ≤ ‖x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hb.le,div_le_iff₀ hb,mul_comm]
  simp only [outerCoefficient,he]

lemma outerBarrier_dilation {b : ℝ} (hb : 0 < b) (B r : ℝ) (x : TFSpace) :
    b^4*outerBarrier B r (b • x) = outerBarrier B (r/b) x := by
  simp only [outerBarrier,norm_smul,Real.norm_of_nonneg hb.le]
  field_simp

theorem barrier_weak_dilation {b Z k r : ℝ} (hb : 0 < b)
    {a μ p : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r μ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x))) :
    WeakNuclearLowerOn univ (b^3*Z)
      (fun x => nuclearField (b^3*Z) x+b^4*a (b • x))
      (fun x => innerSource (r/b) (tfDilation b μ) (tfDilation b p) x+
        outerCoefficient (r/b) x*reaction k (nuclearField (b^3*Z) x+b^4*a (b • x))) := by
  have hh := weakNuclearLower_dilation hb hw
  have hf (x : TFSpace) : b^4*(nuclearField Z (b • x)+a (b • x)) =
      nuclearField (b^3*Z) x+b^4*a (b • x) := by
    rw [mul_add,nuclearField_dilation hb]
  apply (hh.congr_field (fun x _ => hf x)).congr_source
  intro x _
  change b^6*(innerSource r μ p (b • x)+
    outerCoefficient r (b • x)*reaction k (nuclearField Z (b • x)+a (b • x))) = _
  rw [mul_add,←show tfDilation b (innerSource r μ p) x = b^6*innerSource r μ p (b • x) from rfl,
    innerSource_dilation hb,outerCoefficient_dilation hb]
  rw [←hf, reaction_dilation hb]
  ring

end CoulombBarrier

end Work_BarrierDilation_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma local_coulomb_majorant {ρ : TFSpace → ℝ} {x : TFSpace} {b L : ℝ}
    (hb : 0 < b) (hn : ∀ z, 0 ≤ ρ z)
    (hlocal : ∀ z, ‖x-z‖ < b → ρ z ≤ L) (z : TFSpace) :
    ρ z/‖x-z‖ ≤ L*truncatedCoulomb b (x-z)+ρ z/b := by
  by_cases hz : ‖x-z‖ < b
  · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hz)]
    have hh := mul_le_mul_of_nonneg_right (hlocal z hz) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [mul_nonneg (hn z) (inv_pos.mpr hb).le]
  · rw [truncatedCoulomb,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hz),mul_zero,zero_add]
    exact div_le_div_of_nonneg_left (hn z) hb (le_of_not_gt hz)

lemma local_bounded_potential_integrable {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    (hi : Integrable ρ) {x : TFSpace} {b L : ℝ} (hb : 0 < b)
    (hn : ∀ z, 0 ≤ ρ z) (hlocal : ∀ z, ‖x-z‖ < b → ρ z ≤ L) :
    Integrable (fun z => ρ z/‖x-z‖) := by
  have hk : Integrable (fun z => truncatedCoulomb b (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable b).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable b)
  apply ((hk.const_mul L).add (hi.div_const b)).mono'
    (hm.div (measurable_const.sub measurable_id).norm).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z / ‖x-z‖‖ ≤ L*truncatedCoulomb b (x-z)+ρ z/b
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
    exact local_coulomb_majorant hb hn hlocal z

theorem local_bounded_potential_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    (hi : Integrable ρ) {x : TFSpace} {b L : ℝ} (hb : 0 < b)
    (hn : ∀ z, 0 ≤ ρ z) (hlocal : ∀ z, ‖x-z‖ < b → ρ z ≤ L) :
    tfPotential ρ x ≤ 2*Real.pi*L*b^2+(∫ z, ρ z)/b := by
  have hk : Integrable (fun z => truncatedCoulomb b (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable b).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable b)
  calc
    _ ≤ ∫ z, L*truncatedCoulomb b (x-z)+ρ z/b := integral_mono
      (local_bounded_potential_integrable hm hi hb hn hlocal)
      ((hk.const_mul L).add (hi.div_const b)) (local_coulomb_majorant hb hn hlocal)
    _ = _ := by
      rw [integral_add (hk.const_mul L) (hi.div_const b),integral_const_mul,
        integral_div,integral_sub_left_eq_self,truncatedCoulomb,integral_indicator measurableSet_ball]
      simp only [one_div]
      rw [integral_coulomb_ball hb]
      ring

theorem potential_tendsto_zero_of_local_mass {ι : Type*} {F : Filter ι}
    {ρ : ι → TFSpace → ℝ} {L : ι → ℝ} {x : TFSpace} {b : ℝ} (hb : 0 < b)
    (hm : ∀ j, Measurable (ρ j)) (hi : ∀ j, Integrable (ρ j))
    (hn : ∀ j z, 0 ≤ ρ j z)
    (hlocal : ∀ᶠ j in F, ∀ z, ‖x-z‖ < b → ρ j z ≤ L j)
    (hL : Tendsto L F (𝓝 0)) (hMass : Tendsto (fun j => ∫ z, ρ j z) F (𝓝 0)) :
    Tendsto (fun j => tfPotential (ρ j) x) F (𝓝 0) := by
  have hupper : Tendsto (fun j => 2*Real.pi*L j*b^2+(∫ z, ρ j z)/b) F (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_div,zero_add] using
      ((hL.const_mul (2*Real.pi)).mul_const (b^2)).add (hMass.div_const b)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun j => tfPotential_nonneg (ae_of_all _ (hn j)) x
  · filter_upwards [hlocal] with j hj
    exact local_bounded_potential_le (hm j) (hi j) hb (hn j) hj

end CoulombAnalysis

end

end OAI
