import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsGrid
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyNumericUniform

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem adaptiveSmallEuler_le_exp {L Z : ℕ} (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    {u C : ℝ} (hu : 0 ≤ u)
    (hM : (∑p∈highWeightPrimeCutoff (Z^14),1/(p:ℝ)) ≤ Real.log (Real.log (2*(Z^14:ℕ)))+C) :
    adaptiveSmallEuler L u ≤ Real.exp (u*(Real.log (Real.log (2*(Z^14:ℕ)))+C)) := by
  have hsub : (Finset.range (L^4+1)).filter Nat.Prime ⊆ highWeightPrimeCutoff (Z^14) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hLpow : L^4 ≤ Z^14 := (Nat.pow_le_pow_left hLZ 4).trans
      (Nat.pow_le_pow_right hZ (by omega))
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp'.2.pos,by have := Finset.mem_range.mp hp'.1; omega⟩,hp'.2⟩
  unfold adaptiveSmallEuler
  apply (Real.prod_one_add_le_exp_sum _ (f:=fun p:ℕ => u/(p:ℝ)) (fun p => by positivity)).trans
  apply Real.exp_le_exp.mpr
  calc
    _ = u*(∑p∈(Finset.range (L^4+1)).filter Nat.Prime,1/(p:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans hM) hu

theorem eventually_witness_small_euler_cost (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ u K : ℝ,
      0 ≤ u → u ≤ T^(1/100000:ℝ) → T^(3/4:ℝ) ≤ K →
      u*(3*Real.log T+C) ≤ K/10 := by
  filter_upwards [eventually_const_add_log_le_rpow C 3 (by norm_num : (0:ℝ)<1/4),
    eventually_mul_rpow_le_rpow 10 (a:=1/100000+1/4) (b:=3/4) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with T hlog hpow hT
  intro u K hu huup hK
  have hT0 : 0 < T := by linarith
  calc
    _ ≤ u*(T^(1/4:ℝ)/2) := mul_le_mul_of_nonneg_left (by linarith [hlog]) hu
    _ ≤ T^(1/100000:ℝ)*(T^(1/4:ℝ)/2) := mul_le_mul_of_nonneg_right huup (by positivity)
    _ = T^(1/100000+1/4:ℝ)/2 := by rw [←mul_div_assoc,←Real.rpow_add hT0]
    _ ≤ K/10 := by have := Real.rpow_nonneg hT0.le (1/100000+1/4:ℝ); linarith

theorem witness_small_energy_scalar {L : ℕ} (hL : Squarefree L) {z : ℝ}
    (hz : 0 < z) (hsqrt : 2000 ≤ Real.sqrt z)
    (hprimes : ∀p∈L.primeFactors,z ≤ (p:ℝ)) {u : ℝ} (hu : 0 ≤ u)
    (hEuler : adaptiveSmallEuler L u ≤ Real.exp ((L.primeFactors.card:ℝ)/10)) :
    (1+Real.sqrt 2*(1/16:ℝ))^(2*L.primeFactors.card)*
      (reciprocalSqrtDivisorSum L)^2*adaptiveSmallEuler L u ≤
        Real.exp ((L.primeFactors.card:ℝ)/2) := by
  let K := L.primeFactors.card
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hs2 : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 2)).mpr (by norm_num)
  have hW : (1+Real.sqrt 2*(1/16:ℝ))^(2*K) ≤ Real.exp ((K:ℝ)/4) := by
    calc
      _ ≤ (Real.exp (1/8:ℝ))^(2*K) := pow_le_pow_left₀ (by positivity)
        (by linarith [Real.add_one_le_exp (1/8:ℝ)]) _
      _ = _ := by rw [←Real.exp_nat_mul]; congr 1; push_cast; ring
  have hV : (reciprocalSqrtDivisorSum L)^2 ≤ Real.exp ((K:ℝ)/1000) := by
    have hh := pow_le_pow_left₀ (reciprocalSqrtDivisorSum_nonneg L)
      (reciprocalSqrtDivisorSum_le_exp hL hz hprimes) 2
    have hden : (2:ℝ)/Real.sqrt z ≤ 1/1000 := by
      apply (div_le_iff₀ (by linarith : 0 < Real.sqrt z)).mpr
      linarith
    calc
      _ ≤ (Real.exp ((K:ℝ)/Real.sqrt z))^2 := hh
      _ = Real.exp (2*((K:ℝ)/Real.sqrt z)) := by rw [pow_two,←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right hden hK
        convert hh using 1 <;> ring)
  calc
    _ ≤ Real.exp ((K:ℝ)/4)*Real.exp ((K:ℝ)/1000)*Real.exp ((K:ℝ)/10) :=
      mul_le_mul (mul_le_mul hW hV (sq_nonneg _) (Real.exp_pos _).le) hEuler
        (adaptiveSmallEuler_nonneg L hu) (by positivity)
    _ = Real.exp ((K:ℝ)/4+(K:ℝ)/1000+(K:ℝ)/10) := by rw [Real.exp_add,Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_witness_small_family_energies :
    ∀ᶠ T : ℝ in atTop, ∀ Z z L : ℕ,
      1 ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      Squarefree L → L.primeFactors.card=auxiliaryK Z z →
      L ≤ Z → (∀p∈L.primeFactors,z ≤ p) →
      ∀ A : ∀p:ℕ,Finset (ZMod p),
      (∀b∈adaptiveSmallArrayFamily L Z (1/16) A,
        (∑s∈adaptiveSmallSupport L,((((2*gridMomentParameter T:ℕ):ℝ)^2)^s.primeFactors.card)*‖b s‖^2) ≤
          Real.exp (auxiliaryK Z z)) ∧
      (∀b∈adaptiveOffEventArrayFamily L Z (1/16) A (auxiliaryK Z z),
        (∑s∈adaptiveSmallSupport L,((((2*gridMomentParameter T:ℕ):ℝ)^2)^s.primeFactors.card)*‖b s‖^2) ≤
          Real.exp (-(auxiliaryK Z z:ℝ))) := by
  obtain ⟨C,hC,hM⟩ := highWeightPrimeCutoff_reciprocal_upper
  filter_upwards [eventually_witness_small_euler_cost C,eventually_auxiliaryK_bounds,
    eventually_grid_dimension_bound,eventually_parameter_Z_pow_bound,
    eventually_quadratic_energy_sqrt_z,eventually_ge_atTop (2:ℝ),
    eventually_linear_cost_le_exp_K ((2*cutoffFourierBound)^2) (1/2)
      (sq_pos_of_pos (by have := cutoffFourierBound_pos; positivity)) (by norm_num)]
    with T hEuler hK huup hBup hsqrt hT hcost
  intro Z z L hZ hZl hZu hz hzl hzu hL hLK hLZ hprimes A
  let u : ℝ := ((2*gridMomentParameter T:ℕ):ℝ)^2
  have hu : 0 ≤ u := sq_nonneg _
  have hKlow := (hK Z z hZl hZu hz hzl hzu).1
  have hloglog : Real.log (Real.log (2*(Z^14:ℕ))) ≤ 3*Real.log T :=
    high_weight_loglog_le hT (Nat.one_le_pow 14 Z hZ) (by exact_mod_cast hBup Z hZ hZu)
  have heuler : adaptiveSmallEuler L u ≤ Real.exp ((auxiliaryK Z z:ℝ)/10) := by
    apply (adaptiveSmallEuler_le_exp hZ hLZ hu (hM _ (Nat.one_le_pow 14 Z hZ))).trans
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (by linarith [hloglog]) hu).trans
      (hEuler u (auxiliaryK Z z) hu (by simpa only [Nat.cast_pow] using huup) hKlow)
  have hscalar := witness_small_energy_scalar hL (by exact_mod_cast hz : (0:ℝ) < z)
    (hsqrt z hz hzl) (fun p hp => by exact_mod_cast hprimes p hp)
    hu (by simpa only [hLK] using heuler)
  conv at hscalar => rhs; rw [hLK]
  have hconst : (2*cutoffFourierBound)^2 ≤ Real.exp ((auxiliaryK Z z:ℝ)/2) := by
    have hh := hcost (auxiliaryK Z z) hKlow
    have hh' : (2*cutoffFourierBound)^2 ≤ (2*cutoffFourierBound)^2*T := by nlinarith [sq_nonneg (2*cutoffFourierBound)]
    exact hh'.trans (by simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh)
  constructor
  · intro b hb
    apply (adaptiveSmallArrayFamily_energy hL (by norm_num) hu A hb).trans
    calc
      _ = (2*cutoffFourierBound)^2*((1+Real.sqrt 2*(1/16:ℝ))^(2*L.primeFactors.card)*
        (reciprocalSqrtDivisorSum L)^2*adaptiveSmallEuler L u) := by ring
      _ ≤ Real.exp ((auxiliaryK Z z:ℝ)/2)*Real.exp ((auxiliaryK Z z:ℝ)/2) :=
        mul_le_mul hconst hscalar (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (adaptiveSmallEuler_nonneg L hu)) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  · intro b hb
    apply (adaptiveOffEventArrayFamily_energy hL (by norm_num) hu A (auxiliaryK Z z) hb).trans
    calc
      _ = Real.exp (-(9/5:ℝ)*auxiliaryK Z z)*((1+Real.sqrt 2*(1/16:ℝ))^(2*L.primeFactors.card)*
        (reciprocalSqrtDivisorSum L)^2*adaptiveSmallEuler L u) := by ring
      _ ≤ Real.exp (-(9/5:ℝ)*auxiliaryK Z z)*Real.exp ((auxiliaryK Z z:ℝ)/2) :=
        mul_le_mul_of_nonneg_left hscalar (Real.exp_pos _).le
      _ ≤ _ := by rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; have := (Nat.cast_nonneg (auxiliaryK Z z) : (0:ℝ) ≤ _); linarith

end Ostmann.QuadraticCenter

end

end OAI
