import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CorrectionPotentialSmallBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTransferGlobal
import OAI.Analysis.CoulombIonization.FieldAnalysis.CorrectedFieldCharge

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_charge_bound {a ρ p : TFSpace → ℝ} {Z k r l S M P C : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hal : 1/(2*l) ≤ r) (hk : 0 ≤ k)
    (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x, r ≤ ‖x‖ → ‖x‖ ≤ S →
      ρ x ≤ k*(max (nuclearField Z x-tfPotential ρ x-1) 0)^(3/2:ℝ)+l⁻¹^8/‖x‖^6)
    (hlo : ∀ x, r ≤ ‖x‖ → 0 ≤ nuclearField Z x+a x)
    (hu : ∀ x, r ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4) :
    (∫ x, ρ x)-Z ≤ (∫ x, p x)+
      volume.real (closedBall (0:TFSpace) S)*(64*l⁻¹^2)+(∫ x in {x : TFSpace | S < ‖x‖}, ρ x) := by
  let q₀ := annularApproximationError l r S
  let E : Set TFSpace := {x | S < ‖x‖}
  let q : TFSpace → ℝ := fun x => q₀ x+E.indicator ρ x
  have hEm : MeasurableSet E := measurableSet_lt measurable_const measurable_norm
  have hq₀m : Measurable q₀ := annularApproximationError_measurable _ _ _
  have hq₀n : ∀ x, 0 ≤ q₀ x := annularApproximationError_nonneg _ _ _
  have hq₀b : ∀ x, q₀ x ≤ 64*l⁻¹^2 := annularApproximationError_bound hl hal
  have hq₀i := bounded_compact_mass_le hq₀m (by positivity : 0 ≤ 64*l⁻¹^2)
    hq₀n hq₀b (annularApproximationError_support _ _ _)
  have htm : Measurable (E.indicator ρ) := hρm.indicator hEm
  have hti : Integrable (E.indicator ρ) := hρi.indicator hEm
  have htn : ∀ x, 0 ≤ E.indicator ρ x := fun x => indicator_nonneg (fun z _ => hρn z) x
  have htb : ∀ x, E.indicator ρ x ≤ M := by
    intro x
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]; exact hρb x
    · rw [indicator_of_notMem hx]; exact hM
  have hqm : Measurable q := hq₀m.add htm
  have hqi : Integrable q := hq₀i.1.add hti
  have hqn : ∀ x, 0 ≤ q x := fun x => add_nonneg (hq₀n x) (htn x)
  have hqb : ∀ x, q x ≤ 64*l⁻¹^2+M := fun x => add_le_add (hq₀b x) (htb x)
  have hcomp : ∀ x, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-1)+4*Real.pi*q x := by
    intro x hx
    by_cases hxS : ‖x‖ ≤ S
    · have hq0 : q₀ x = l⁻¹^8/‖x‖^6 := indicator_of_mem (show x ∈ {x : TFSpace | r ≤ ‖x‖ ∧ ‖x‖ ≤ S} from ⟨hx,hxS⟩) _
      have ht0 : E.indicator ρ x = 0 := indicator_of_notMem (show x ∉ E from not_lt.mpr hxS) _
      dsimp [q]
      rw [hq0,ht0,add_zero,reaction]
      have hh := mul_le_mul_of_nonneg_left (hd x hx hxS) (by positivity : (0:ℝ) ≤ 4*Real.pi)
      nlinarith only [hh]
    · have ht0 : E.indicator ρ x = ρ x := indicator_of_mem (show x ∈ E from lt_of_not_ge hxS) _
      have hqρ : ρ x ≤ q x := by dsimp [q]; rw [ht0]; exact le_add_of_nonneg_left (hq₀n x)
      have hreac : 0 ≤ reaction k (nuclearField Z x-tfPotential ρ x-1) := by
        unfold reaction; positivity
      have hh := mul_le_mul_of_nonneg_left hqρ (by positivity : (0:ℝ) ≤ 4*Real.pi)
      linarith
  have htrans := barrier_transfer_global hr (by norm_num : (0:ℝ) ≤ 1) hk ha
    hρm hρi hM hρn hρb hpm hpi hP hpn hpb hqm hqi (by positivity) hqn hqb hw hcomp hu
  have heqn : ∀ x, 0 ≤ p x+q x := fun x => add_nonneg (hpn x) (hqn x)
  have hcharge := corrected_field_charge hr hρm hρi hM hρn hρb
    (hpm.add hqm) (hpi.add hqi) heqn (fun x hx => (hlo x hx).trans (htrans x))
  change (∫ x, ρ x)-Z ≤ ∫ x, p x+q x at hcharge
  rw [integral_add hpi hqi] at hcharge
  have hqmass : (∫ x, q x) ≤ volume.real (closedBall (0:TFSpace) S)*(64*l⁻¹^2)+
      (∫ x in E, ρ x) := by
    rw [show (∫ x, q x) = (∫ x, q₀ x)+(∫ x, E.indicator ρ x) from integral_add hq₀i.1 hti,
      integral_indicator hEm]
    linarith only [hq₀i.2]
  linarith

end CoulombBarrier

end

end OAI
