import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

/-! # The exact period and mean of the cold stripes -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetGeometry

def stripeLine (p : ℝ) (a : Bool) : Set ℝ :=
  {x | ∃ k : ℤ, ((k:ℝ)+(if a then 0 else 1/2))*p < x ∧
    x < ((k:ℝ)+(if a then 0 else 1/2)+1/4)*p}

theorem stripeAtPeriod_mem_iff (p : ℝ) (a : Bool) (y : VelocityWeight.Transverse) :
    y ∈ stripeAtPeriod p a ↔ y 0 ∈ stripeLine p a := Iff.rfl

theorem stripeLine_measurable (p : ℝ) (a : Bool) : MeasurableSet (stripeLine p a) := by
  unfold stripeLine
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion (fun k => measurableSet_Ioo)

theorem stripeLine_add_period (p x : ℝ) (a : Bool) :
    x+p ∈ stripeLine p a ↔ x ∈ stripeLine p a := by
  constructor
  · rintro ⟨k,hk₁,hk₂⟩
    refine ⟨k-1,?_,?_⟩ <;> push_cast <;> nlinarith
  · rintro ⟨k,hk₁,hk₂⟩
    refine ⟨k+1,?_,?_⟩ <;> push_cast <;> nlinarith

theorem stripeLine_indicator_periodic (p : ℝ) (a : Bool) :
    Function.Periodic ((stripeLine p a).indicator (fun _ => (1:ℝ))) p := by
  intro x
  classical
  by_cases hx : x ∈ stripeLine p a
  · rw [indicator_of_mem hx,indicator_of_mem ((stripeLine_add_period p x a).mpr hx)]
  · rw [indicator_of_notMem hx,indicator_of_notMem (mt (stripeLine_add_period p x a).mp hx)]

theorem stripeLine_on_cell {p : ℝ} (hp : 0 < p) (a : Bool) {x : ℝ}
    (hx : x ∈ Ioc 0 p) :
    x ∈ stripeLine p a ↔ x ∈ Ioo ((if a then 0 else 1/2)*p)
      (((if a then 0 else 1/2)+1/4)*p) := by
  constructor
  · rintro ⟨k,hk₁,hk₂⟩
    have hc₀ : (0:ℝ) ≤ (if a then 0 else 1/2) := by split <;> norm_num
    have hc₁ : (if a then 0 else 1/2) ≤ (3/4:ℝ) := by split <;> norm_num
    have hk : k = 0 := by
      rcases lt_trichotomy k 0 with hn | hz | hn
      · have hn' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        have hmul := mul_nonpos_of_nonpos_of_nonneg
          (show (k:ℝ)+(if a then 0 else 1/2)+1/4 ≤ 0 by linarith) hp.le
        linarith [hx.1]
      · exact hz
      · have hn' : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
        have hmul := mul_le_mul_of_nonneg_right
          (show (1:ℝ) ≤ (k:ℝ)+(if a then 0 else 1/2) by linarith) hp.le
        linarith [hx.2]
    simpa only [hk,Int.cast_zero,zero_add,mem_Ioo] using And.intro hk₁ hk₂
  · intro hx
    exact ⟨0,by simpa using hx.1,by simpa using hx.2⟩

theorem stripeLine_integral_period {p : ℝ} (hp : 0 < p) (a : Bool) :
    (∫ x in 0..p, (stripeLine p a).indicator (fun _ => (1:ℝ)) x) = p/4 := by
  let c : ℝ := if a then 0 else 1/2
  have hc₀ : 0 ≤ c := by dsimp [c]; split <;> norm_num
  have hc₁ : c+1/4 ≤ (1:ℝ) := by dsimp [c]; split <;> norm_num
  have hsub : Ioo (c*p) ((c+1/4)*p) ⊆ Ioc 0 p := by
    intro x hx
    exact ⟨(mul_nonneg hc₀ hp.le).trans_lt hx.1,
      hx.2.le.trans (by nlinarith)⟩
  rw [intervalIntegral.integral_of_le hp.le]
  calc
    _ = ∫ x in Ioc 0 p, (Ioo (c*p) ((c+1/4)*p)).indicator (fun _ => (1:ℝ)) x := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      classical
      by_cases hy : x ∈ stripeLine p a
      · rw [indicator_of_mem hy,indicator_of_mem ((stripeLine_on_cell hp a hx).mp hy)]
      · rw [indicator_of_notMem hy,indicator_of_notMem (mt (stripeLine_on_cell hp a hx).mpr hy)]
    _ = volume.real (Ioo (c*p) ((c+1/4)*p) ∩ Ioc 0 p) := by
      rw [integral_indicator_const (1:ℝ) measurableSet_Ioo,smul_eq_mul,mul_one,
        measureReal_restrict_apply measurableSet_Ioo]
    _ = p/4 := by
      rw [inter_eq_left.mpr hsub,Real.volume_real_Ioo]
      rw [max_eq_left (by nlinarith : 0 ≤ (c+1/4)*p-c*p)]
      ring

end BoltzmannNonuniqueness.JetGeometry

end

end OAI
