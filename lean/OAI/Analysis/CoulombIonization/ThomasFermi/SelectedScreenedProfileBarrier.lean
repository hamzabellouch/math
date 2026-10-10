import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ScreenedLimitDynamicsBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.AnnularApproximationLimitBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.SelectedBarrierLimitBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.WeakSingularProfileBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

def tfDensityCoefficient : ℝ := (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹
lemma tfDensityCoefficient_pos : 0 < tfDensityCoefficient := by
  unfold tfDensityCoefficient
  have hh := tfKinetic_pos
  positivity
lemma tfDensityCoefficient_reaction : 4*Real.pi*tfDensityCoefficient = tfReactionCoefficient := rfl
end CoulombAnalysis

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem selected_screened_profile {ι : Type*} {F : Filter ι} [NeBot F]
    {s r l Z : ι → ℝ} {a μ p : ι → TFSpace → ℝ} {B C Ccap R q : ℝ}
    {F_lim : TFSpace → ℝ}
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i)
    (hs0 : Tendsto s F (𝓝 0)) (hr0 : Tendsto (fun i => r i/s i) F (𝓝 0))
    (hl : ∀ i, 0 < l i) (hl0 : Tendsto l F atTop)
    (hal : ∀ i, 1/(2*l i) ≤ r i/s i)
    (hB : 0 < B) (hC : 0 ≤ C) (hCcap : 0 ≤ Ccap) (hR : 0 < R)
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
        outerCoefficient (r i) x*reaction tfDensityCoefficient (nuclearField (Z i) x+a i x)))
    (hlower : ∀ i y, r i ≤ ‖y‖ → outerBarrier B (r i) y ≤ nuclearField (Z i) y+a i y)
    (hupper : ∀ i y, r i ≤ ‖y‖ → nuclearField (Z i) y+a i y ≤ C/‖y‖^4)
    (hTF : ∀ i x, r i/s i ≤ ‖x‖ → ‖x‖ ≤ l i →
      |tfDilation (s i) (μ i) x-
        tfDensityCoefficient*(max (nuclearField ((s i)^3*Z i) x-
          tfPotential (tfDilation (s i) (μ i)) x-1) 0)^(3/2:ℝ)| ≤ (l i)⁻¹^8/‖x‖^6)
    (hcont : ContinuousOn F_lim {0}ᶜ)
    (hconv : ∀ K : Set TFSpace, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn
      (fun i x => nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x)
      F_lim F K)
    (hcap : ∀ᶠ i in F, ∀ x, r i/s i ≤ ‖x‖ → ‖x‖ ≤ l i →
      nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x ≤ 1+Ccap/‖x‖^4)
    (hq : Tendsto (fun i => (s i)^3*(Z i-∫ x, μ i x)) F (𝓝 q))
    (htail : Tendsto (fun i => ∫ x in {x : TFSpace | R < ‖x‖}, tfDilation (s i) (μ i) x)
      F (𝓝 0)) :
    EqOn F_lim tfInfiniteField {0}ᶜ ∧ q = tfResidualCharge := by
  have hscaled (i : ι) : ∃ M ≥ 0, ∀ x, tfDilation (s i) (μ i) x ≤ M := by
    obtain ⟨M,hM,hMb⟩ := hμb i
    exact ⟨(s i)^6*M,mul_nonneg (by positivity) hM,
      fun x => mul_le_mul_of_nonneg_left (hMb _) (by positivity)⟩
  have hcaplim := annular_upper_cap_limit hr0 hl0 hconv hcap
  have hq' : Tendsto (fun i => (s i)^3*Z i-∫ x, tfDilation (s i) (μ i) x) F (𝓝 q) := by
    simpa only [tfDilation_mass (hs _),mul_sub] using hq
  have hdyn := screened_limit_dynamics hR hCcap
    (fun i => tfDilation_measurable (hμm i))
    (fun i => tfDilation_integrable (hs i) (hμi i))
    (fun i => tfDilation_nonneg (hμn i)) hscaled hcont hconv
    (fun _ hK hK0 => annular_tf_error_local hr0 hl0 hTF hK hK0) hq' htail hcaplim
  have hsphere (S : ℝ) (hS : 0 < S) : TendstoUniformlyOn
      (fun i x => nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x)
      F_lim F (sphere (0:TFSpace) S) := by
    apply hconv _ (isCompact_sphere _ _)
    intro x hx hx0
    rw [mem_sphere_zero_iff_norm,hx0,norm_zero] at hx
    exact hS.ne' hx.symm
  have hpositive := selected_barriers_limit_positive hs hr hs0 hr0 hl hl0 hal
    tfDensityCoefficient_pos.le hC ha hμm hμi hμn hμb hpm hpi hpn hpb hpSupport hpMass
    hweak hlower hupper (fun i x hx hx' => by
      have hh := (abs_le.mp (hTF i x hx hx')).2
      linarith only [hh]) hsphere hdyn.2.2.2
  apply weak_limit_identification hR hB hCcap hcont _ hdyn.2.1 hdyn.2.2.1 hpositive hcaplim
  simpa only [tfDensityCoefficient_reaction] using hdyn.1

end CoulombBarrier

end

end OAI
