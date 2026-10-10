import OAI.Combinatorics.BalancedRyser.Probability.SimultaneousDrift
import OAI.Combinatorics.BalancedRyser.Selection.SelectionTrueCountConcentration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace Balanced.Selection.Process

def trackJumpCoefficient (p : Parameters) : ℝ :=
  (2 + p.Pstar) / p.smin +
    (3 + p.C * (p.Pstar + 1 / p.a)) / (p.smin * p.a / 3)

theorem trackJumpCoefficient_pos {p : Parameters} (hp : p.Admissible) :
    0 < trackJumpCoefficient p := by
  have hP := Parameters.Pstar_pos hp
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hC := hp.2.1
  unfold trackJumpCoefficient
  positivity

theorem trackJumpBounds_le {p : Parameters} (hp : p.Admissible) {q : ℕ} (hq : 1 ≤ q) :
    domainTrackJumpBound p q ≤ trackJumpCoefficient p * (q : ℝ) ^ (1 / 8 : ℝ) ∧
    degreeTrackJumpBound p q ≤ trackJumpCoefficient p * (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hP := Parameters.Pstar_pos hp
  have hs : 0 < p.smin := Real.exp_pos _
  have ha := (Parameters.a_bounds hp).1
  have hC := hp.2.1
  have hb : 0 < p.smin * p.a / 3 := by positivity
  have hpow : 1 ≤ (q : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hq) (by norm_num)
  have hcoef : 0 < p.C * (p.Pstar + 1 / p.a) := by positivity
  have hd : (2 + p.Pstar) / p.smin ≤ trackJumpCoefficient p := by
    unfold trackJumpCoefficient
    exact le_add_of_nonneg_right (by positivity)
  have hv : (3 + p.C * (p.Pstar + 1 / p.a)) / (p.smin * p.a / 3) ≤
      trackJumpCoefficient p := by
    unfold trackJumpCoefficient
    exact le_add_of_nonneg_left (by positivity)
  constructor
  · calc
      domainTrackJumpBound p q ≤
          (2 + p.Pstar) / p.smin * (q : ℝ) ^ (1 / 8 : ℝ) := by
        unfold domainTrackJumpBound
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hs.le
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hd (by positivity)
  · calc
      degreeTrackJumpBound p q ≤
          (3 + p.C * (p.Pstar + 1 / p.a)) / (p.smin * p.a / 3) *
            (q : ℝ) ^ (1 / 8 : ℝ) := by
        unfold degreeTrackJumpBound
        rw [div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ hb.le
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hv (by positivity)

theorem source_azuma_exp_le {q T : ℕ} {L K : ℝ}
    (hq : 0 < q) (hT : 1 ≤ T) (hTq : T ≤ 3 * q)
    (hL : 0 < L) (hK : 0 < K) (hLK : L ≤ K * (q : ℝ) ^ (1 / 8 : ℝ)) :
    Real.exp (-((q : ℝ) ^ (4 / 5 : ℝ) / 2) ^ 2 /
      (8 * (T : ℝ) * L ^ 2)) ≤
      Real.exp (-((q : ℝ) ^ (7 / 20 : ℝ) / (96 * K ^ 2))) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hTR : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hTqR : (T : ℝ) ≤ 3 * q := by exact_mod_cast hTq
  have hden : 8 * (T : ℝ) * L ^ 2 ≤
      8 * (3 * (q : ℝ)) * (K * (q : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := by
    gcongr
  have hdiv := div_le_div_of_nonneg_left
    (sq_nonneg ((q : ℝ) ^ (4 / 5 : ℝ) / 2))
    (by positivity : 0 < 8 * (T : ℝ) * L ^ 2) hden
  rw [selection_azuma_exponent hqR hK] at hdiv
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg hdiv

def trackConcentrationError (p : Parameters) (q : ℕ) : ℝ :=
  48 * (q : ℝ) ^ 3 *
    Real.exp (-((q : ℝ) ^ (7 / 20 : ℝ) / (96 * (trackJumpCoefficient p) ^ 2)))

theorem trackConcentrationError_nonneg (p : Parameters) (q : ℕ) :
    0 ≤ trackConcentrationError p q := by
  unfold trackConcentrationError
  positivity

theorem tendsto_trackConcentrationError {p : Parameters} (hp : p.Admissible) :
    Tendsto (trackConcentrationError p) atTop (𝓝 0) := by
  have hK := trackJumpCoefficient_pos hp
  have hc : 0 < 1 / (96 * (trackJumpCoefficient p) ^ 2) := by positivity
  convert tendsto_selection_simultaneous_error 48 hc using 1
  funext q
  unfold trackConcentrationError
  congr 2
  ring

end Balanced.Selection.Process

end

end OAI
