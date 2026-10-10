import OAI.NumberTheory.CubicMoment.Estimates.SmoothRankinSaving

namespace OAI

/-! The reciprocal mass of large squarefree divisors composed only of
polylogarithmically small primes. This is the Rankin step for sparse late
stops in the prime decomposition, derived from ordinary prime counting. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_reciprocal_rankin_tail (S U : Finset Eisenstein)
    (hS : ∀ d ∈ S, primary d ∧ Squarefree d)
    (hU : ∀ d ∈ S, primaryPrimeFactors d ⊆ U)
    {Y σ : ℝ} (hY : 0 < Y) (hσ : 0 ≤ σ)
    (hlarge : ∀ d ∈ S, Y ≤ norm d) :
    (∑ d ∈ S, (norm d)⁻¹) ≤
      Y^(-σ)*∏ p ∈ U, (1+norm p^(-(1-σ))) := by
  calc
    _ ≤ ∑ d ∈ S, Y^(-σ)*norm d^(-(1-σ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 := norm_pos_of_ne_zero (primary_ne_zero (hS d hd).1)
      calc
        _ = norm d^(-σ)*norm d^(-(1-σ)) := by
          rw [←Real.rpow_add hd0,show -σ + -(1-σ)=(-1:ℝ) by ring,Real.rpow_neg_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hY (hlarge d hd) (neg_nonpos.mpr hσ))
          (Real.rpow_nonneg hd0.le _)
    _ = Y^(-σ)*(∑ d ∈ S, norm d^(-(1-σ))) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (squarefree_supported_rankin_sum S U hS hU (1-σ)) (Real.rpow_nonneg hY.le _)

lemma prime_shifted_reciprocal_sum {y σ : ℝ} (_hy : 0 < y) (hσ : 0 ≤ σ) :
    (∑ p ∈ primeCutoff y, norm p^(-(1-σ))) ≤
      y^σ*(∑ p ∈ primeCutoff y, (norm p)⁻¹) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp0 := norm_pos_of_ne_zero (mem_primeCutoff.mp hp).1.2.ne_zero
  calc
    _ = norm p^σ*(norm p)⁻¹ := by
      rw [←Real.rpow_neg_one,←Real.rpow_add hp0]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hp0.le (mem_primeCutoff.mp hp).2 hσ) (inv_nonneg.mpr hp0.le)

private lemma power_log_sublinear (a b q : ℝ) (hq : q < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ T^q*(a+b*Real.log T) ≤ ε*T := by
  have hp : 0 < 1-q := sub_pos.mpr hq
  have hconst : (fun _ : ℝ => a) =o[atTop] (fun T => T^(1-q)) := by
    apply isLittleO_const_left.mpr
    right
    apply (tendsto_rpow_atTop hp).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact (Real.norm_of_nonneg (Real.rpow_nonneg hT.le _)).symm
  have hsmall := (hconst.add ((isLittleO_log_rpow_atTop hp).const_mul_left b)).def hε
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with T ht hT
  refine ⟨hT,?_⟩
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hT0.le _)] at ht
  have ht' : a+b*Real.log T ≤ ε*T^(1-q) := (le_abs_self _).trans ht
  calc
    _ ≤ T^q*(ε*T^(1-q)) :=
      mul_le_mul_of_nonneg_left ht' (Real.rpow_nonneg hT0.le _)
    _ = ε*T := by
      rw [←mul_assoc,mul_comm (T^q) ε,mul_assoc,←Real.rpow_add hT0,
        show q+(1-q)=1 by ring,Real.rpow_one]

/-- The precise sparse-divisor consequence needed for late stops.
The exponent depends on the fixed prime cutoff power and divisor size. -/
theorem polylog_smooth_divisor_reciprocal_saving
    (hpnt : PrimaryPrimePNT) {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℝ in atTop,
      ∀ S : Finset Eisenstein,
      (∀ d ∈ S, primary d ∧ Squarefree d) →
      (∀ d ∈ S, X^η ≤ norm d) →
      (∀ d ∈ S, ∀ p ∈ primaryPrimeFactors d, norm p ≤ (Real.log X)^C) →
      (∑ d ∈ S, (norm d)⁻¹) ≤ X^(-δ) := by
  obtain ⟨K,hK,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  let σ : ℝ := (2*C)⁻¹
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hCs : C*σ = 1/2 := by dsimp [σ]; field_simp [hC.ne']
  let δ : ℝ := η*σ/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hy : Tendsto (fun X : ℝ => (Real.log X)^C) atTop atTop :=
    (tendsto_rpow_atTop hC).comp Real.tendsto_log_atTop
  refine ⟨δ,hδ,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp hy).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually
      (power_log_sublinear K (K*C) (1/2) (by norm_num) hδ)] with X hX hlogy hsmall
  intro S hS hlarge hsmooth
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL0 : 0 < Real.log X := Real.log_pos hX
  let y : ℝ := (Real.log X)^C
  have hy0 : 0 < y := Real.rpow_pos_of_pos hL0 C
  change 1 ≤ Real.log y at hlogy
  have hU : ∀ d ∈ S, primaryPrimeFactors d ⊆ primeCutoff y := by
    intro d hd p hp
    exact mem_primeCutoff.mpr ⟨(primaryPrimeFactor_spec (hS d hd).1 hp).1,hsmooth d hd p hp⟩
  have hrec : (∑ p ∈ primeCutoff y, (norm p)⁻¹) ≤ K*(1+C*Real.log (Real.log X)) := by
    have hh := hprime (Real.log y) hlogy
    rw [Real.exp_log hy0] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    have ht := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hlogy)
    have hlog : Real.log y = C*Real.log (Real.log X) := Real.log_rpow hL0 C
    rw [←hlog]
    linarith
  have hprod : (∏ p ∈ primeCutoff y, (1+norm p^(-(1-σ)))) ≤ X^δ := by
    apply (finite_euler_product_le_exp (primeCutoff y) (1-σ)).trans
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    apply (prime_shifted_reciprocal_sum hy0 hσ.le).trans
    apply (mul_le_mul_of_nonneg_left hrec (Real.rpow_nonneg hy0.le _)).trans
    have hp : y^σ = (Real.log X)^(1/2:ℝ) := by
      dsimp [y]
      rw [←Real.rpow_mul hL0.le,hCs]
    rw [hp]
    convert hsmall.2 using 1 <;> ring
  calc
    _ ≤ (X^η)^(-σ)*(∏ p ∈ primeCutoff y, (1+norm p^(-(1-σ)))) :=
      squarefree_reciprocal_rankin_tail S (primeCutoff y) hS hU
        (Real.rpow_pos_of_pos hX0 η) hσ.le hlarge
    _ ≤ (X^η)^(-σ)*X^δ := mul_le_mul_of_nonneg_left hprod
      (Real.rpow_nonneg (Real.rpow_nonneg hX0.le _) _)
    _ = X^(-δ) := by
      rw [←Real.rpow_mul hX0.le,←Real.rpow_add hX0]
      apply congrArg (fun t : ℝ => X^t)
      dsimp [δ]
      ring

end CubicFirstMoment

end

end OAI
