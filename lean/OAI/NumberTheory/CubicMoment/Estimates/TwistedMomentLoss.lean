import OAI.NumberTheory.CubicMoment.Estimates.SmallEulerProduct
import OAI.NumberTheory.CubicMoment.Estimates.TwistedRetainedMoment
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerMoments

namespace OAI

/-! Absorption of the exact small-prime partition and dyadic losses. -/
noncomputable section
namespace CubicFirstMoment

lemma dyad_card_sq_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((idealDyadIndices (fullIdealBall J)).card:ℝ)^2 ≤ C*(2*J)^ε := by
  obtain ⟨C,hC,hlog⟩ := natLog_power_bound 2 hε
  refine ⟨C,hC,?_⟩
  intro J hJ
  have hJ0 : 0 ≤ 2*J := by linarith
  have hn : 1 ≤ ⌊2*J⌋₊ := (Nat.one_le_floor_iff (2*J)).mpr (by linarith)
  have hc : (idealDyadIndices (fullIdealBall J)).card ≤ Nat.log 2 ⌊2*J⌋₊+1 :=
    idealDyadIndices_card_le _ (fun ν hν => (mem_fullIdealBall.mp hν).trans (by linarith))
  have hc' : ((idealDyadIndices (fullIdealBall J)).card:ℝ) ≤ (Nat.log 2 ⌊2*J⌋₊+1:ℕ) := by
    exact_mod_cast hc
  calc
    _ ≤ ((Nat.log 2 ⌊2*J⌋₊+1:ℕ):ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc' 2
    _ ≤ C*(⌊2*J⌋₊:ℝ)^ε := hlog _ hn
    _ ≤ C*(2*J)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hJ0) hε.le) hC.le

 theorem twisted_moment_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : Eisenstein) (J : ℝ), r ≠ 0 → 1 ≤ J →
      ((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J ≤
        C*(2*J)^ε*norm (3*r)^ε := by
  obtain ⟨A,hA,hdyad⟩ := dyad_card_sq_power (show 0 < ε/2 by positivity)
  obtain ⟨B,hB,hparts⟩ := supportedParts_card_small_power (show 0 < ε/4 by positivity)
  refine ⟨A*B^2,by positivity,?_⟩
  intro r J hr hJ
  have h3r : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have hJp : 0 < 2*J := by linarith
  have hNp : 0 < norm (3*r) := lt_of_lt_of_le zero_lt_one (one_le_norm h3r)
  have hprod : 0 < (2*J)*norm (3*r) := mul_pos hJp hNp
  have hp := hparts (3*r) (fullIdealBall (2*J)) (2*J) h3r (by linarith)
    (fun ν hν => mem_fullIdealBall.mp hν)
  have hs : smallTwistMomentLoss r J ≤ B^2*(2*J)^(ε/2)*norm (3*r)^(ε/2) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hp 2).trans_eq
    rw [mul_pow,← Real.rpow_mul_natCast hprod.le]
    have he : ε/4*(2:ℕ) = ε/2 := by norm_num; ring
    rw [he,Real.mul_rpow hJp.le hNp.le]
    ring
  have hnorm : norm (3*r)^(ε/2) ≤ norm (3*r)^ε :=
    Real.rpow_le_rpow_of_exponent_le (one_le_norm h3r) (by linarith)
  calc
    _ ≤ (A*(2*J)^(ε/2))*(B^2*(2*J)^(ε/2)*norm (3*r)^(ε/2)) :=
      mul_le_mul (hdyad J hJ) hs (smallTwistMomentLoss_nonneg r J) (by positivity)
    _ = (A*B^2)*((2*J)^(ε/2)*(2*J)^(ε/2))*norm (3*r)^(ε/2) := by ring
    _ = (A*B^2)*(2*J)^ε*norm (3*r)^(ε/2) := by
      have he : (2*J)^(ε/2)*(2*J)^(ε/2) = (2*J)^ε := by
        rw [← Real.rpow_add hJp]
        congr 1
        ring
      rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)

 theorem twisted_moment_weighted_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : Eisenstein) (N J : ℝ), r ≠ 0 → 1 ≤ N → 1 ≤ J →
      (((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J)*
        (N*(2*J))^(ε/2) ≤ C*(N*(2*J))^ε*norm (3*r)^ε := by
  obtain ⟨C,hC,hbound⟩ := twisted_moment_loss (show 0 < ε/2 by positivity)
  refine ⟨C,hC,?_⟩
  intro r N J hr hN hJ
  have hQ : 0 < N*(2*J) := by positivity
  have h3r : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have hj : (2*J)^(ε/2) ≤ (N*(2*J))^(ε/2) := Real.rpow_le_rpow (by positivity)
    (le_mul_of_one_le_left (by positivity) hN) (by positivity)
  have hn : norm (3*r)^(ε/2) ≤ norm (3*r)^ε :=
    Real.rpow_le_rpow_of_exponent_le (one_le_norm h3r) (by linarith)
  calc
    _ ≤ (C*(2*J)^(ε/2)*norm (3*r)^(ε/2))*(N*(2*J))^(ε/2) :=
      mul_le_mul_of_nonneg_right (hbound r J hr hJ) (by positivity)
    _ ≤ (C*(N*(2*J))^(ε/2)*norm (3*r)^ε)*(N*(2*J))^(ε/2) := by
      have hn0 := Real.rpow_nonneg (norm_nonneg (3*r)) (ε/2)
      gcongr
    _ = (C*norm (3*r)^ε)*((N*(2*J))^(ε/2)*(N*(2*J))^(ε/2)) := by ring
    _ = _ := by
      have he : (N*(2*J))^(ε/2)*(N*(2*J))^(ε/2) = (N*(2*J))^ε := by
        rw [← Real.rpow_add hQ]
        congr 1
        ring
      rw [he]
      ring

end CubicFirstMoment

end

end OAI
