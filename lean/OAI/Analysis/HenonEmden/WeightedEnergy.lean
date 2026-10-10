import OAI.Analysis.HenonEmden.RootRecovery

namespace OAI

section WeightedEnergy

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap

lemma compactSupport_of_outer_zero {n : ℕ} {F : Space n → ℝ}
    (hF : ∀ x, 2 ≤ ‖x‖ → F x=0) : HasCompactSupport F := by
  apply HasCompactSupport.intro (K := closedBall 0 2) (isCompact_closedBall _ _)
  intro x hx
  exact hF x (not_lt.mp (fun hh => hx (mem_closedBall_zero_iff.mpr hh.le)))

lemma compactSupport_eta (n : ℕ) : HasCompactSupport (eta n : Space n → ℝ) :=
  compactSupport_of_outer_zero (fun _ hx => eta_eq_zero hx)
lemma compactSupport_w (n : ℕ) : HasCompactSupport (w n : Space n → ℝ) :=
  compactSupport_of_outer_zero (fun _ hx => w_outer n hx)
lemma compactSupport_weight {n : ℕ} (κ : ℝ) (e : sphere (0:Space n) 1) :
    HasCompactSupport (weight volume κ e) :=
  compactSupport_of_outer_zero (fun _ hx => weight_outer volume κ e hx)

lemma IsSolution.integrable_source_energy_weight {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun x => χ x*source u q B x*u x) := by
  have hl := ((h.source_f_locallyIntegrable hn).mul_continuous h.continuous_u).mul_continuous hχ
  have hi := hl.integrableOn_isCompact hχc
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (hi.congr_fun (fun x _ => by ring) (isClosed_tsupport χ).measurableSet)
  intro x hx
  apply subset_tsupport χ
  intro hz
  exact hx (by simp [hz])

def weightedEnergy {n : ℕ} (χ u : Space n → ℝ) (q B : ℝ) : ℝ :=
  ∫ x, χ x*source u q B x*u x

def weightedEnergyN {n : ℕ} (χ u : Space n → ℝ) (q B : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (χ x*source u q B x*u x)

lemma weightedEnergyN_nonneg {n : ℕ} {χ u : Space n → ℝ} {q B : ℝ}
    (hχ : ∀ x, 0 ≤ χ x) (hu : ∀ x, 0 ≤ u x) : 0 ≤ weightedEnergy χ u q B := by
  exact integral_nonneg (fun x => mul_nonneg (mul_nonneg (hχ x) (source_nonneg hu q B x)) (hu x))

lemma IsSolution.weightedEnergyN_eq {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    weightedEnergyN χ u q B = ENNReal.ofReal (weightedEnergy χ u q B) := by
  exact (ofReal_integral_eq_lintegral_ofReal (h.integrable_source_energy_weight hn hχ hχc)
    (ae_of_all _ fun x => mul_nonneg (mul_nonneg (hχ0 x)
      (source_nonneg (fun y => (h.positive_u y).le) q B x)) (h.positive_u x).le)).symm

lemma IsSolution.weightedEnergyN_finite {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) : weightedEnergyN χ u q B ≠ ⊤ :=
  (h.integrable_source_energy_weight hn hχ hχc).lintegral_lt_top.ne

end HenonLaneEmden
end
end WeightedEnergy

end OAI
