import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierLimitPositiveBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.SelectedBarrierTransferBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem selected_barriers_limit_positive {ι : Type*} {F : Filter ι} [NeBot F]
    {s r l Z : ι → ℝ} {a μ p : ι → TFSpace → ℝ} {k B C : ℝ}
    {F_lim : TFSpace → ℝ}
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i)
    (hs0 : Tendsto s F (𝓝 0)) (hr0 : Tendsto (fun i => r i/s i) F (𝓝 0))
    (hl : ∀ i, 0 < l i) (hl0 : Tendsto l F atTop)
    (hal : ∀ i, 1/(2*l i) ≤ r i/s i) (hk : 0 ≤ k) (hC : 0 ≤ C)
    (ha : ∀ i, Continuous (a i))
    (hμm : ∀ i, Measurable (μ i)) (hμi : ∀ i, Integrable (μ i))
    (hμn : ∀ i x, 0 ≤ μ i x) (hμb : ∀ i, ∃ M ≥ 0, ∀ x, μ i x ≤ M)
    (hpm : ∀ i, Measurable (p i)) (hpi : ∀ i, Integrable (p i))
    (hpn : ∀ i x, 0 ≤ p i x) (hpb : ∀ i, ∃ P ≥ 0, ∀ x, p i x ≤ P)
    (hpSupport : ∀ i x, r i < ‖x‖ → p i x = 0)
    (hpMass : ∀ i, (∫ x, p i x) ≤ 1)
    (hweak : ∀ i, WeakNuclearLowerOn univ (Z i)
      (fun x => nuclearField (Z i) x+a i x)
      (fun x => innerSource (r i) (μ i) (p i) x+
        outerCoefficient (r i) x*reaction k (nuclearField (Z i) x+a i x)))
    (hlower : ∀ i y, r i ≤ ‖y‖ → outerBarrier B (r i) y ≤ nuclearField (Z i) y+a i y)
    (hupper : ∀ i y, r i ≤ ‖y‖ → nuclearField (Z i) y+a i y ≤ C/‖y‖^4)
    (hTF : ∀ i x, r i/s i ≤ ‖x‖ → ‖x‖ ≤ l i →
      tfDilation (s i) (μ i) x ≤
        k*(max (nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x-1) 0)^(3/2:ℝ)+
          (l i)⁻¹^8/‖x‖^6)
    (hconv : ∀ S : ℝ, 0 < S → TendstoUniformlyOn
      (fun i x => nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x)
      F_lim F (sphere (0:TFSpace) S))
    (hdecay : ∀ ε > 0, ∃ R > 0, ∀ x : TFSpace, R ≤ ‖x‖ → |F_lim x| < ε) :
    ∀ x : TFSpace, x ≠ 0 → B/‖x‖^4 ≤ F_lim x := by
  apply positive_limit_of_eventual_barrier_transfer
    (U := fun i x => nuclearField ((s i)^3*Z i) x+(s i)^4*a i (s i • x))
    (L := fun S i x => tfPotential (fun y => tfDilation (s i) (p i) y+
      annularApproximationError (l i) (r i/s i) S y) x)
    hC hr0 (fun i => scaled_barrier_lower (hs i) (hlower i))
    (fun i => scaled_barrier_upper (hs i) (hupper i)) hconv
    (fun S _ x hx => literal_barrier_correction_tendsto_zero S hs hs0 hr0 hl hl0 hal
      hpm hpi hpn hpb hpSupport hpMass x hx) hdecay
  intro S hS
  filter_upwards [hl0.eventually (eventually_ge_atTop S)] with i hi
  intro c hc hb
  obtain ⟨M,hM,hMb⟩ := hμb i
  obtain ⟨P,hP,hPb⟩ := hpb i
  apply selected_scaled_barrier_transfer_ball (hr i) (hs i) (hl i) hS (hal i) hk hc
    (ha i) (hμm i) (hμi i) hM (hμn i) hMb (hpm i) (hpi i) hP (hpn i) hPb
    (hweak i) (fun x hx hxs => hTF i x hx (hxs.trans hi))
  intro x hx
  have hh := hb x hx
  linarith only [hh]

end CoulombBarrier

end

end OAI
