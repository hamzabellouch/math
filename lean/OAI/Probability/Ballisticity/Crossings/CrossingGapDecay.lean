import Mathlib
import OAI.Probability.Ballisticity.Crossings.CrossingEstimate
import OAI.Probability.Ballisticity.Crossings.CrossingGap
import OAI.Probability.Ballisticity.Estimates.RapidDecay

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma polynomial_box_card_bound {d : ℕ} (C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    (2*(⌈C*(N+1:ℝ)^2⌉₊:ℝ)+1)^d ≤ (2*C+3)^d*(N+1:ℝ)^(2*d) := by
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ C*(N+1:ℝ)^2)).le
  have hNsq : (1:ℝ) ≤ (N+1:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ ((2*C+3)*(N+1:ℝ)^2)^d := pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = _ := by rw [mul_pow,← pow_mul]

lemma bad_crossing_rapidDecay {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    RapidDecay (fun N => (environmentLaw ν).real (badCrossingEvent e N (1/2))) := by
  apply rapidDecay_of_power_bounds (fun _ => measureReal_nonneg)
  intro D hD
  filter_upwards [crossing_estimate hd ν hue e htrans D hD] with N hN
  exact hN.le

lemma crossingGap_rapidDecay {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    RapidDecay (fun N => (annealedLaw ν).real (CrossingGap e N)) := by
  obtain ⟨C,ε,hC,hε,hε1,hconf⟩ := spatial_confinement ν hue e htrans
  have hbad := (bad_crossing_rapidDecay hd ν hue e htrans).shift (fun _ => measureReal_nonneg) 1
  have hgeom := (rapidDecay_geometric (1-ε) (by linarith) (by linarith)).const_mul (2*d:ℕ)
  have hbox := (hbad.pow_mul (2*d)).const_mul ((2*C+3)^d)
  have hexp := rapidDecay_stretchedExp (1/2) 1 (by norm_num) (by norm_num)
  apply ((hgeom.add hbox).add hexp).of_le (fun _ => measureReal_nonneg)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hh := annealed_crossingGap_bound ν e htrans N (by omega) (C*(N+1:ℝ)^2)
  have hc := hconf N
  have hb := mul_le_mul_of_nonneg_right (polynomial_box_card_bound (d := d) C hC.le N)
    (show 0 ≤ (environmentLaw ν).real (badCrossingEvent e (N+1) (1/2)) from measureReal_nonneg)
  have he := descending_probability_bound N
  simp only [Nat.cast_add,Nat.cast_one,neg_one_mul] at hh he ⊢
  exact hh.trans (add_le_add (add_le_add hc (by simpa only [mul_assoc] using hb)) he)

end DirectionalTransience

end

end OAI
