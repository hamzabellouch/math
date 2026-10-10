import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierQuantitativeStepBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_transfer_weak {a ρ p q : TFSpace → ℝ} {Z k r S lam M P Q : ℝ}
    (hr : 0 < r) (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x ∈ ball (0 : TFSpace) S, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-lam)+4*Real.pi*q x) :
    WeakLaplacianLowerOn (ball 0 S) (fun x => a x+tfPotential ρ x-tfPotential (fun y => p y+q y) x)
      (fun x => outerCoefficient r x*(reaction k (nuclearField Z x+a x)-
        reaction k (nuclearField Z x-tfPotential ρ x-lam))) := by
  let χ := outerCoefficient r
  let U : TFSpace → ℝ := fun x => nuclearField Z x+a x
  let F : TFSpace → ℝ := fun x => nuclearField Z x-tfPotential ρ x-lam
  let h : TFSpace → ℝ := fun x => innerSource r ρ p x+χ x*reaction k (U x)
  let e : TFSpace → ℝ := fun x => p x+q x
  have hem : Measurable e := hpm.add hqm
  have hei : Integrable e := hpi.add hqi
  have heN : ∀ x, 0 ≤ e x := fun x => add_nonneg (hpn x) (hqn x)
  have heB : ∀ x, e x ≤ P+Q := fun x => add_le_add (hpb x) (hqb x)
  have hePQ : 0 ≤ P+Q := add_nonneg hP hQ
  have hpot := (bounded_L1_potential_lipschitz hρm hρi hM hρn hρb).continuous
  have hhs : LocallyIntegrable h := nuclear_source_locallyIntegrable Z k hr
    (innerSource_locallyIntegrable hρi.locallyIntegrable hpi.locallyIntegrable r)
    (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r) ha
  have hzero : LocallyIntegrable (fun _ : TFSpace => (0 : ℝ)) := locallyIntegrable_zero
  have hUr : LocallyIntegrable (fun x => χ x*reaction k (U x)) := by
    simpa only [zero_add] using nuclear_source_locallyIntegrable Z k hr hzero
      (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r) ha
  have hFr : LocallyIntegrable (fun x => χ x*reaction k (F x)) := by
    have hfr₀ : LocallyIntegrable (fun x => χ x*reaction k
        (nuclearField Z x+(-tfPotential ρ x-lam))) := by
      simpa only [zero_add,Pi.sub_apply,Pi.neg_apply,χ] using nuclear_source_locallyIntegrable Z k hr hzero
        (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r)
        (hpot.neg.sub continuous_const)
    have heq : (fun x => χ x*reaction k (nuclearField Z x+(-tfPotential ρ x-lam))) =
        (fun x => χ x*reaction k (F x)) := by
      funext x
      congr 1
      dsimp only [F]
      congr 1
      ring
    rwa [heq] at hfr₀
  have htarget : LocallyIntegrable (fun x => χ x*(reaction k (U x)-reaction k (F x))) := by
    convert hUr.sub hFr using 1
    funext x
    simp only [Pi.sub_apply,mul_sub]
  have hbase := (weakNuclearLower_add_iff Z ha.locallyIntegrable).mp hw
  have hw₁ := hbase.add_bounded_L1_potential ha.locallyIntegrable hhs hρm hρi hM hρn hρb 1
  have hu₁ : LocallyIntegrable (fun x => a x+1*tfPotential ρ x) :=
    (ha.add (continuous_const.mul hpot)).locallyIntegrable
  have hh₁ : LocallyIntegrable (fun x => h x-1*(4*Real.pi)*ρ x) :=
    hhs.sub (hρi.locallyIntegrable.smul (1*(4*Real.pi)))
  have hw₂ := hw₁.add_bounded_L1_potential hu₁ hh₁ hem hei hePQ heN heB (-1)
  have hh₂ : LocallyIntegrable (fun x => (h x-1*(4*Real.pi)*ρ x)-(-1)*(4*Real.pi)*e x) :=
    hh₁.sub (hei.locallyIntegrable.smul ((-1)*(4*Real.pi)))
  have hs := (hw₂.mono_set (subset_univ (ball (0 : TFSpace) S))).source_mono hh₂ htarget
    (fun x hx => ?_)
  · apply hs.congr_field
    intro x _
    simp only [one_mul,neg_one_mul]
    rfl
  · by_cases hxr : ‖x‖ < r
    · dsimp only [χ,h,e,innerSource,outerCoefficient]
      rw [ite_eq_left hxr,ite_eq_right (not_le_of_gt hxr)]
      nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le (hqn x)]
    · have hc := hd x hx (le_of_not_gt hxr)
      dsimp only [χ,h,e,innerSource,outerCoefficient]
      rw [ite_eq_right hxr,ite_eq_left (le_of_not_gt hxr)]
      change 1*(reaction k (U x)-reaction k (F x)) ≤
        (4*Real.pi*(0-p x)+1*reaction k (U x)-1*(4*Real.pi)*ρ x)-(-1)*(4*Real.pi)*(p x+q x)
      change 4*Real.pi*ρ x ≤ reaction k (F x)+4*Real.pi*q x at hc
      linarith

end CoulombBarrier

end

end OAI
