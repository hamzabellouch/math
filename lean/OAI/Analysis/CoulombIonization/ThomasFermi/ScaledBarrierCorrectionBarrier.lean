import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BoundedL1PotentialBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.CorrectionPotentialSmallBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfDilation_measurable {b : ℝ} {ρ : TFSpace → ℝ} (hm : Measurable ρ) :
    Measurable (tfDilation b ρ) :=
  measurable_const.mul (hm.comp (continuous_const_smul b).measurable)

lemma tfDilation_integrable {b : ℝ} (hb : 0 < b) {ρ : TFSpace → ℝ}
    (hi : Integrable ρ) : Integrable (tfDilation b ρ) :=
  (hi.comp_smul hb.ne').const_mul _

lemma tfDilation_nonneg {b : ℝ} {ρ : TFSpace → ℝ} (hn : ∀ x, 0 ≤ ρ x) :
    ∀ x, 0 ≤ tfDilation b ρ x := fun x => mul_nonneg (by positivity) (hn _)

lemma tfDilation_support {b r : ℝ} (hb : 0 < b) {ρ : TFSpace → ℝ}
    (hs : ∀ x, r < ‖x‖ → ρ x = 0) :
    ∀ x, r/b < ‖x‖ → tfDilation b ρ x = 0 := by
  intro x hx
  rw [tfDilation,hs _ (by
    rw [norm_smul,Real.norm_of_nonneg hb.le]
    exact (div_lt_iff₀ hb).mp hx |>.trans_eq (mul_comm _ _)),mul_zero]

lemma selected_scaled_error_potential_tendsto_zero {ι : Type*} {F : Filter ι}
    {s r : ι → ℝ} {p : ι → TFSpace → ℝ}
    (hs : ∀ i, 0 < s i) (hs0 : Tendsto s F (𝓝 0))
    (ha : Tendsto (fun i => r i/s i) F (𝓝 0))
    (hm : ∀ i, Measurable (p i)) (hi : ∀ i, Integrable (p i))
    (hn : ∀ i x, 0 ≤ p i x) (hsp : ∀ i x, r i < ‖x‖ → p i x = 0)
    (hMass : ∀ i, (∫ x, p i x) ≤ 1) (x : TFSpace) (hx : x ≠ 0) :
    Tendsto (fun i => tfPotential (tfDilation (s i) (p i)) x) F (𝓝 0) := by
  apply potential_tendsto_zero_of_shrinking_support hx
    (fun i => tfDilation_measurable (hm i)) (fun i => tfDilation_integrable (hs i) (hi i))
    (fun i => tfDilation_nonneg (hn i)) (fun i => tfDilation_support (hs i) (hsp i)) ha
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_pow (by norm_num : 3 ≠ 0)] using hs0.pow 3)
  · exact Eventually.of_forall fun i => integral_nonneg (tfDilation_nonneg (hn i))
  · apply Eventually.of_forall
    intro i
    rw [tfDilation_mass (hs i)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hMass i) (pow_nonneg (hs i).le 3)

lemma tfPotential_add_bounded {p q : TFSpace → ℝ} {P Q : ℝ}
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q) (x : TFSpace) :
    tfPotential (fun y => p y+q y) x = tfPotential p x+tfPotential q x := by
  simp only [tfPotential,add_div]
  exact integral_add (bounded_L1_potential_integrable hpm hpi hP hpn hpb x)
    (bounded_L1_potential_integrable hqm hqi hQ hqn hqb x)

theorem literal_barrier_correction_tendsto_zero {ι : Type*} {F : Filter ι}
    {s r l : ι → ℝ} {p : ι → TFSpace → ℝ} (S : ℝ)
    (hs : ∀ i, 0 < s i) (hs0 : Tendsto s F (𝓝 0))
    (ha : Tendsto (fun i => r i/s i) F (𝓝 0))
    (hl : ∀ i, 0 < l i) (hl0 : Tendsto l F atTop)
    (hal : ∀ i, 1/(2*l i) ≤ r i/s i)
    (hm : ∀ i, Measurable (p i)) (hi : ∀ i, Integrable (p i))
    (hn : ∀ i x, 0 ≤ p i x) (hb : ∀ i, ∃ P ≥ 0, ∀ x, p i x ≤ P)
    (hsp : ∀ i x, r i < ‖x‖ → p i x = 0)
    (hMass : ∀ i, (∫ x, p i x) ≤ 1) (x : TFSpace) (hx : x ≠ 0) :
    Tendsto (fun i => tfPotential (fun y => tfDilation (s i) (p i) y+
      annularApproximationError (l i) (r i/s i) S y) x) F (𝓝 0) := by
  have he (i : ι) : tfPotential (fun y => tfDilation (s i) (p i) y+
      annularApproximationError (l i) (r i/s i) S y) x =
      tfPotential (tfDilation (s i) (p i)) x+
      tfPotential (annularApproximationError (l i) (r i/s i) S) x := by
    obtain ⟨P,hP,hbp⟩ := hb i
    have hqm := annularApproximationError_measurable (l i) (r i/s i) S
    have hqn := annularApproximationError_nonneg (l i) (r i/s i) S
    have hqb := annularApproximationError_bound (S := S) (hl i) (hal i)
    have hqs := annularApproximationError_support (l i) (r i/s i) S
    have hqi := (bounded_compact_mass_le hqm (by positivity : 0 ≤ 64*(l i)⁻¹^2) hqn hqb hqs).1
    exact tfPotential_add_bounded (tfDilation_measurable (hm i))
      (tfDilation_integrable (hs i) (hi i)) (mul_nonneg (pow_nonneg (hs i).le 6) hP)
      (tfDilation_nonneg (hn i)) (fun y => mul_le_mul_of_nonneg_left (hbp _) (by positivity))
      hqm hqi (by positivity) hqn hqb x
  simp_rw [he]
  have hp := selected_scaled_error_potential_tendsto_zero hs hs0 ha hm hi hn hsp hMass x hx
  have hq := annular_correction_potential_tendsto_zero (S := S) x hl hal hl0
  simpa only [add_zero] using hp.add hq

end CoulombAnalysis

end

end OAI
