import Mathlib
import OAI.Probability.Ballisticity.Crossings.StripExitBound
import OAI.Probability.Ballisticity.Crossings.CrossingGapDecay

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma strip_box_card_bound {d : ℕ} (m H : ℕ) (hH : 0 < H) :
    (latticeBox (d := d) (m*H^2)).card ≤ (2*m+1)^d*H^(2*d) := by
  rw [card_latticeBox]
  calc
    _ ≤ ((2*m+1)*H^2)^d := Nat.pow_le_pow_left (by nlinarith [sq_pos_of_pos hH]) _
    _ = _ := by rw [mul_pow,← pow_mul]

lemma upward_probability_bound (N : ℕ) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    (1-κ*((N+1:ℕ):ℝ)^(-(1/2:ℝ)))^(N+1) ≤
      Real.exp (-κ*((N+1:ℕ):ℝ)^(1/2:ℝ)) := by
  have hn : (0:ℝ) < (N+1:ℕ) := by positivity
  have h1 : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have ha := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hb : κ*((N+1:ℕ):ℝ)^(-(1/2:ℝ)) ≤ 1 :=
    (mul_le_of_le_one_left (by positivity) hκ1).trans ha
  calc
    _ ≤ (Real.exp (- (κ*((N+1:ℕ):ℝ)^(-(1/2:ℝ)))))^(N+1) :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hh : ((N+1:ℕ):ℝ)*((N+1:ℕ):ℝ)^(-(1/2:ℝ)) = ((N+1:ℕ):ℝ)^(1/2:ℝ) := by
        calc
          _ = ((N+1:ℕ):ℝ)^(1:ℝ)*((N+1:ℕ):ℝ)^(-(1/2:ℝ)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hn]; norm_num
      nlinarith

lemma stripTime_rapidDecay {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℕ, 0 < A ∧ RapidDecay (fun N =>
      (annealedLaw ν).real (StripUntil e (N+1) (A*(N+1)^(2*d+1)))) := by
  obtain ⟨C,ε,hC,hε,hε1,hconf⟩ := spatial_confinement ν hue e htrans
  obtain ⟨κ,hκ,hωκ⟩ := environment_uniform_elliptic ν hue
  have hκ1 : κ ≤ 1 := by
    obtain ⟨ω,hω⟩ := hωκ.exists
    exact (hω 0 e).trans (row_entry_le_one (ω 0) e)
  let m : ℕ := ⌈4*C⌉₊
  let A : ℕ := (2*m+1)^d
  have hA : 0 < A := by dsimp [A]; positivity
  have hm : 4*C ≤ (m:ℝ) := Nat.le_ceil _
  have hgeom := ((rapidDecay_geometric (1-ε) (by linarith) (by linarith)).shift
    (fun _ => by positivity) 1).const_mul (2*d:ℕ)
  have hbad := (((bad_crossing_rapidDecay hd ν hue e htrans).shift
    (fun _ => measureReal_nonneg) 1).pow_mul (2*d)).const_mul A
  have hexp := ((rapidDecay_stretchedExp (1/2) κ (by norm_num) (by exact_mod_cast hκ)).pow_mul (2*d)).const_mul A
  refine ⟨A,hA,((hgeom.add hbad).add hexp).of_le (fun _ => measureReal_nonneg) ?_⟩
  apply Eventually.of_forall
  intro N
  let H := N+1
  have hH : 0 < H := by dsimp [H]; omega
  have hH' : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hM : C*((H:ℝ)+1)^2 ≤ (m*H^2:ℕ) := by
    push_cast
    have hs : ((H:ℝ)+1)^2 ≤ 4*(H:ℝ)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hs hC.le
    nlinarith [sq_nonneg (H:ℝ)]
  have hcard := strip_box_card_bound (d := d) m H hH
  have hT : (latticeBox (d := d) (m*H^2)).card*H ≤ A*H^(2*d+1) := by
    simpa only [pow_succ,mul_assoc] using Nat.mul_le_mul_right H hcard
  have hh := annealed_stripUntil_bound ν e H (A*H^(2*d+1)) H (m*H^2) hH
    (C*((H:ℝ)+1)^2) hM hT κ hκ1 hωκ
  have hc := hconf H
  have hb := mul_le_mul_of_nonneg_right (show ((latticeBox (d := d) (m*H^2)).card:ℝ) ≤ (A*H^(2*d):ℕ) by exact_mod_cast hcard)
    (show 0 ≤ (environmentLaw ν).real (badCrossingEvent e H (1/2)) from measureReal_nonneg)
  have he := upward_probability_bound N κ (by positivity) (by exact_mod_cast hκ1)
  have he' : ((latticeBox (d := d) (m*H^2)).card:ℝ)*(1-(κ:ℝ)*(H:ℝ)^(-(1/2:ℝ)))^H ≤
      (A*H^(2*d):ℕ)*Real.exp (-(κ:ℝ)*(H:ℝ)^(1/2:ℝ)) :=
    mul_le_mul (by exact_mod_cast hcard) he (by
      apply pow_nonneg
      have ha := Real.rpow_le_one_of_one_le_of_nonpos hH' (by norm_num : -(1/2:ℝ) ≤ 0)
      have hh := (mul_le_of_le_one_left (by positivity : 0 ≤ (H:ℝ)^(-(1/2:ℝ)))
        (show (κ:ℝ) ≤ 1 by exact_mod_cast hκ1)).trans ha
      linarith) (by positivity)
  have hbnd := hh.trans (add_le_add (add_le_add hc hb) he')
  simpa only [H,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_pow,mul_assoc] using hbnd

end DirectionalTransience

end

end OAI
