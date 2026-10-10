import OAI.NumberTheory.Jacobsthal.Primes.PrimeCompactWeights

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RetainedIntervalUpper

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeCumulativeBound PrimeRatioBins ContinuousRatioBins
open PrimeHistories PrimeKilledChain ContinuousKilledBins FinitePathMeasures
open LowStateHorizon ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def retainedInterval (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) (a b : ℝ) : Finset ℕ := by
  classical
  exact (children w ell S i s r cap closed).filter (fun p => a ≤ childRatio w r p ∧ childRatio w r p ≤ b)

noncomputable def retainedIntervalTilt (w ell S : ℝ) (i : Side) (s r cap : ℝ) (closed : Bool) (a b : ℝ) : ℝ :=
  ∑ p ∈ retainedInterval w ell S i s r cap closed a b, primeTilt w r i s p

theorem retained_subset_closed {w ell S s r cap a b : ℝ} {i : Side} {closed : Bool}
    (hw : 1 < w) (ha : 0 < a) (hab : a ≤ b) :
    retainedInterval w ell S i s r cap closed a b ⊆ closedBin w r a b := by
  classical
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hchild,hat,htb⟩
  have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hchild).1).2
  have hint := (closed_interval_iff (r:=r) ha hab (PrimeRatioBins.primeExponent_pos hw hprime)).mp ⟨hat,htb⟩
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_,hprime⟩,hat,htb⟩
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  have hreal : (p:ℝ) ≤ w^(r/(a+1)) := (exponent_le_iff hw hp0).mp hint.2
  exact (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) _).le).mpr hreal

theorem short_interval_lower_exponent {w ell S s r cap a b : ℝ} {i : Side} {closed : Bool}
    (hell : 1 ≤ ell) (hs : Valid i s) (ha : 0 < a) (hab : a ≤ b) (hwidth : b-a ≤ 1)
    (hne : (retainedInterval w ell S i s r cap closed a b).Nonempty) :
    (1/2:ℝ) ≤ r/(b+1) := by
  classical
  obtain ⟨p,hp⟩ := hne
  rcases Finset.mem_filter.mp hp with ⟨hchild,hat,htb⟩
  have ht0 := valid_pos (child_valid hs hchild)
  have hx : 1 < primeExponent w p := hell.trans_lt (Finset.mem_filter.mp hchild).2.1
  have hmul : (childRatio w r p+1)*primeExponent w p = r := by
    unfold childRatio
    field_simp
    ring
  have hrgt : childRatio w r p+1 < r := by nlinarith
  apply (le_div_iff₀ (by linarith : 0 < b+1)).mpr
  nlinarith

theorem closed_prime_error : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ r a b : ℝ, 0 < r → 0 < a → a ≤ b → 1/2 ≤ r/(b+1) →
      |closedMass w r a b-(Real.log (b+1)-Real.log (a+1))| ≤
        C*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := harmonic_prime_measure
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw r a b hr ha hab hlow
  have hw1 := hw₀.trans_le hw
  have hend : r/(b+1) ≤ r/(a+1) := div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)
  have h := hbound w hw (r/(b+1)) (r/(a+1)) hlow hend true true
  rw [← closedMass_eq_harmonic hw1 ha hab,bin_log_width hr ha hab] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hlow (Real.log_pos hw1).le)) (by linarith)

theorem retained_short_interval_upper : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ i : Side, ∀ s r cap a b : ℝ, ∀ closed : Bool,
      1 ≤ ell → 0 < r → Valid i s → s ≤ S → 0 < a → a ≤ b → b-a ≤ 1 →
      retainedIntervalTilt w ell S i s r cap closed a b ≤
        C*(1+S)^2*((b-a)+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))) := by
  classical
  obtain ⟨c,C,w₀,hc,hC,hw₀,herr⟩ := closed_prime_error
  obtain ⟨D,hD,henv⟩ := multiplier_envelope
  refine ⟨c,D*(1+C),w₀,hc,by positivity,hw₀,?_⟩
  intro w hw ell S i s r cap a b closed hell hr hs hsS ha hab hwidth
  let A := retainedInterval w ell S i s r cap closed a b
  let e := Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))
  by_cases hne : A.Nonempty
  · have hlow := short_interval_lower_exponent hell hs ha hab hwidth hne
    have herror := herr w hw r a b hr ha hab hlow
    have hlog : Real.log (b+1)-Real.log (a+1) ≤ b-a :=
      ((bin_log_width_bounds ha hab).2).trans (div_le_self (sub_nonneg.mpr hab) (by linarith))
    have hraw : closedMass w r a b ≤ (b-a)+C*e := by linarith [(abs_le.mp herror).2]
    have hsub : (∑ p ∈ A,(p:ℝ)⁻¹) ≤ closedMass w r a b :=
      Finset.sum_le_sum_of_subset_of_nonneg (retained_subset_closed (hw₀.trans_le hw) ha hab)
        (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
    have htilt : retainedIntervalTilt w ell S i s r cap closed a b ≤ D*(1+S)^2*(∑ p ∈ A,(p:ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hchild := (Finset.mem_filter.mp hp).1
      have hm := henv S i s (childRatio w r p) hs hsS (Finset.mem_filter.mp hchild).2.2.2.1
      rw [primeTilt_eq_multiplier,mul_comm (D*(1+S)^2)]
      exact mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (Nat.cast_nonneg p))
    calc
      _ ≤ D*(1+S)^2*closedMass w r a b := htilt.trans (mul_le_mul_of_nonneg_left hsub (by positivity))
      _ ≤ D*(1+S)^2*((b-a)+C*e) := mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ (D*(1+C))*(1+S)^2*((b-a)+e) := by
        have hh : 0 ≤ b-a := sub_nonneg.mpr hab
        have he : 0 ≤ e := (Real.exp_pos _).le
        have hm := mul_nonneg (show 0 ≤ D*(1+S)^2 by positivity)
          (show 0 ≤ C*(b-a)+e by positivity)
        nlinarith
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change ∑ p ∈ A, _ ≤ _
    rw [he,Finset.sum_empty]
    have hh : 0 ≤ b-a := sub_nonneg.mpr hab
    positivity

end NumberTheoryLean.RetainedIntervalUpper


end Erdos970

end OAI
