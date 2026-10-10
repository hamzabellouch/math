import OAI.MeasureTheory.Falconer.Geometry.DyadicPacking
import OAI.MeasureTheory.Falconer.Measures.WeakLimit
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem exists_containing_square (E : Set Plane) (hE : IsCompact E) :
    ∃ Q : DyadicSquare, 0 < Q.side ∧ E ⊆ Q.carrier := by
  obtain ⟨R,hR,hbound⟩ := hE.isBounded.exists_pos_norm_lt
  refine ⟨⟨-R,-R,2*R⟩,by positivity,?_⟩
  intro z hz
  have h0 : |z 0| < R := (PiLp.norm_apply_le z 0).trans_lt (hbound z hz)
  have h1 : |z 1| < R := (PiLp.norm_apply_le z 1).trans_lt (hbound z hz)
  obtain ⟨h0l,h0r⟩ := abs_lt.mp h0
  obtain ⟨h1l,h1r⟩ := abs_lt.mp h1
  change -R ≤ z 0 ∧ z 0 < -R+2*R ∧ -R ≤ z 1 ∧ z 1 < -R+2*R
  exact ⟨h0l.le,by linarith,h1l.le,by linarith⟩

theorem exists_dyadic_scale {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L) :
    ∃ n : ℕ, r ≤ L/(2 : ℝ)^n ∧ L/(2 : ℝ)^n < 2*r := by
  obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hL) ((div_le_one hL).mpr hrL)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have hh := (div_le_iff₀ hL).mp hhi
  have hl := (lt_div_iff₀ hL).mp hlo
  simp only [div_pow, one_pow, pow_succ] at hh hl
  refine ⟨n,by simpa only [one_div, mul_comm, ← div_eq_mul_inv] using hh,?_⟩
  have heq : 1/(2 : ℝ)^n*(1/2)*L = (L/(2 : ℝ)^n)/2 := by ring
  rw [heq] at hl
  linarith

theorem eventual_ball_bounds_of_dyadic (Q : DyadicSquare) (hQ : 0 < Q.side)
    (s : ℝ) (hs : 0 < s) (c : ℝ) (hc : 0 < c)
    (μ : ℕ → ProbabilityMeasure Plane)
    (hcarry : ∀ K, (μ K : Measure Plane) Q.carrierᶜ = 0)
    (hb : ∀ K, ∀ p : List (Bool × Bool), p.length ≤ K →
      (μ K : Measure Plane) (Q.descendant p).carrier ≤
        ENNReal.ofReal (c⁻¹*(Q.descendant p).side^s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Plane, ∀ r > 0, ∀ᶠ K in atTop,
      (μ K : Measure Plane) (ball x r) ≤ ENNReal.ofReal (C*r^s) := by
  let C := max (16*c⁻¹*(2 : ℝ)^s) (Q.side^s)⁻¹
  have hside : 0 < Q.side^s := Real.rpow_pos_of_pos hQ s
  have hC : 0 < C := (inv_pos.mpr hside).trans_le (le_max_right _ _)
  refine ⟨C,hC,fun x r hr => ?_⟩
  by_cases hrQ : r ≤ Q.side
  · obtain ⟨n,hrn,hnr⟩ := exists_dyadic_scale hQ hr hrQ
    filter_upwards [eventually_ge_atTop n] with K hK
    have hball := dyadic_ball_measure_le Q hQ (μ K) (hcarry K) s c⁻¹
      (by positivity) n (fun p hp => hb K p (hp ▸ hK)) x hrn
    apply hball.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ Q.side/(2 : ℝ)^n) hnr.le hs.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le] at hp
    calc
      16*c⁻¹*(Q.side/(2 : ℝ)^n)^s ≤ 16*c⁻¹*((2 : ℝ)^s*r^s) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (16*c⁻¹*(2 : ℝ)^s)*r^s := by ring
      _ ≤ C*r^s := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · apply Filter.Eventually.of_forall
    intro K
    have hpow := Real.rpow_le_rpow hQ.le (le_of_not_ge hrQ) hs.le
    have hlarge : 1 ≤ C*r^s := by
      calc
        1 = (Q.side^s)⁻¹ * Q.side^s := (inv_mul_cancel₀ hside.ne').symm
        _ ≤ (Q.side^s)⁻¹*r^s := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ C*r^s := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    calc
      (μ K : Measure Plane) (ball x r) ≤ (μ K : Measure Plane) univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (C*r^s) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hlarge

theorem frostman_probability (E : Set Plane) (hE : IsCompact E)
    {s : ℝ≥0} (hs : 0 < s) (hd : (s : ℝ≥0∞) < dimH E) :
    ∃ ζ : ProbabilityMeasure Plane, (ζ : Measure Plane) Eᶜ = 0 ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x : Plane, ∀ r > 0,
        (ζ : Measure Plane) (ball x r) ≤ ENNReal.ofReal (C*r^(s : ℝ)) := by
  obtain ⟨Q,hQ,hEQ⟩ := exists_containing_square E hE
  obtain ⟨c,hc,μ,hμ⟩ := exists_dyadic_probability_sequence E hE hs hd Q hQ hEQ
  have hcarry : ∀ K, (μ K : Measure Plane) Q.carrierᶜ = 0 := fun K =>
    measure_mono_null (compl_subset_compl.mpr hEQ) (hμ K).1
  obtain ⟨C,hC,hball⟩ := eventual_ball_bounds_of_dyadic Q hQ s
    (by exact_mod_cast hs) c hc μ hcarry (fun K => (hμ K).2)
  obtain ⟨ζ,hζ,hbound⟩ := frostman_of_eventual_ball_bounds E hE μ (fun K => (hμ K).1) s C hball
  exact ⟨ζ,hζ,C,hC,hbound⟩

end PlanarFalconer

end OAI
