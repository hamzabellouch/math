import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterEulerTail
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLiouvilleTheorem

namespace OAI

/-! Reduction of the Liouville distance estimate to a uniform lower
bound for a Dirichlet L-value ratio. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical LSeries.notation

noncomputable def mrtPrimePowerCutoff (a : ℝ) (X : ℕ) : ℕ :=
  ⌊Real.exp ((Real.log (X:ℝ))^a)⌋₊

lemma mrt_sievePrimesUpTo_floor (x : ℝ) :
    sievePrimesUpTo x=primesUpTo ⌊x⌋₊ := by
  ext p
  simp only [sievePrimesUpTo,primesUpTo,mem_filter,mem_Iic,mem_range,Nat.lt_succ_iff]

lemma mrt_prime_power_tail_cutoff (a : ℝ) (X : ℕ) :
    mrtPrimePowerTail a X=primesUpTo X \ primesUpTo (mrtPrimePowerCutoff a X) := by
  rw [mrtPrimePowerTail,mrtPrimeBand,mrt_sievePrimesUpTo_nat,mrt_sievePrimesUpTo_floor]
  rfl

theorem mrt_prime_power_cutoff_eventually {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    ∀ᶠ X : ℕ in atTop, 1≤Real.log (mrtPrimePowerCutoff a X:ℝ) ∧
      mrtPrimePowerCutoff a X≤X := by
  have hlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun X:ℕ => Real.exp ((Real.log (X:ℝ))^a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp hlog)
  filter_upwards [hlog.eventually (eventually_ge_atTop (1:ℝ)),
    hexp.eventually (eventually_ge_atTop (Real.exp 1+1))] with X hL hE
  have hX0 : (0:ℝ)<X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp (by linarith))
  have hf : Real.exp 1<(mrtPrimePowerCutoff a X:ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp ((Real.log (X:ℝ))^a))
    change _<(⌊Real.exp ((Real.log (X:ℝ))^a)⌋₊:ℝ)
    linarith
  have hf0 : (0:ℝ)< mrtPrimePowerCutoff a X := (Real.exp_pos 1).trans hf
  refine ⟨?_,?_⟩
  · have hh := Real.strictMonoOn_log (Real.exp_pos 1) hf0 hf
    rw [Real.log_exp] at hh
    exact hh.le
  · have hp : Real.exp ((Real.log (X:ℝ))^a)≤(X:ℝ) := by
      calc
        _ ≤ Real.exp (Real.log (X:ℝ)) :=
          Real.exp_le_exp.mpr (Real.rpow_le_self_of_one_le hL ha1)
        _ = _ := Real.exp_log hX0
    have hh := (Nat.floor_le ((Real.exp_pos ((Real.log (X:ℝ))^a)).le)).trans hp
    exact_mod_cast hh

theorem mrt_character_power_tail_LSeries_ratio {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      |(∑p∈mrtPrimePowerTail a X,characterTwist χ t p/(p:ℂ)).re-
        (Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
          Real.log ‖L ↗χ (1+(1/Real.log (mrtPrimePowerCutoff a X:ℝ):ℝ)-
            (t:ℂ)*Complex.I)‖)|≤24+20*halaszMertensConstant := by
  have hlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [mrt_prime_power_cutoff_eventually ha ha1,
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with X hcut hX
  intro q χ t
  rw [mrt_prime_power_tail_cutoff]
  exact mrt_character_prime_tail_LSeries_ratio χ t hcut.1 hX hcut.2

theorem mrt_liouville_distance_from_LSeries_ratio (K : ℝ)
    (hratio : ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0<q →
      (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t|≤X →
        -K≤Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
          Real.log ‖L ↗χ (1+(1/Real.log (mrtPrimePowerCutoff (3/4) X:ℝ):ℝ)-
            (t:ℂ)*Complex.I)‖) :
    ∃ K' : ℝ, 0≤K' ∧ ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0<q →
      (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t|≤X →
        (1/10:ℝ)*Real.log (Real.log (X:ℝ))-K'≤
          squaredDistance liouville (characterTwist χ t) X := by
  apply mrt_liouville_distance_from_prime_tail (K+24+20*halaszMertensConstant)
  have hlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hratio,
    mrt_prime_power_cutoff_eventually (show (0:ℝ)<3/4 by norm_num) (by norm_num),
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with X hr hcut hL
  intro q hq hqX χ t ht
  have hh := (abs_le.mp (mrt_character_prime_tail_LSeries_ratio χ t hcut.1 hL hcut.2)).1
  rw [← mrt_prime_power_tail_cutoff] at hh
  change -(K+24+20*halaszMertensConstant)≤
    (∑ p∈mrtPrimePowerTail (3/4) X,characterTwist χ t p/(p:ℂ)).re
  have hlower := hr q hq hqX χ t ht
  linarith

theorem mrt_liouville_short_of_LSeries_ratio (hMRT : MRTShortExponentialInput) (K : ℝ)
    (hratio : ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0<q →
      (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t|≤X →
        -K≤Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
          Real.log ‖L ↗χ (1+(1/Real.log (mrtPrimePowerCutoff (3/4) X:ℝ):ℝ)-
            (t:ℂ)*Complex.I)‖) :
    MRTLiouvilleShortInput :=
  mrt_liouville_short_of_distance hMRT (mrt_liouville_distance_from_LSeries_ratio K hratio)

end TwoPointCorrelations

end OAI
