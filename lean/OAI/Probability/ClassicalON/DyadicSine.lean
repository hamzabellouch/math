import OAI.Probability.ClassicalON.AnnulusBlocks

namespace OAI

noncomputable section
open scoped BigOperators
namespace ClassicalON

def dyadicAngle (k : ℕ) (t : ℝ) : ℝ := 2*Real.pi*t/(16*(2:ℝ)^k)

def dyadicLambda (k : ℕ) : ℝ :=
  (2:ℝ)^k * ∑ p : DyadicFreq k,
    (1/(dyadicRadius p:ℝ))^3 * Real.sin (dyadicAngle k (dyadicPoint p).1)

@[simp] theorem dyadicAngle_neg (k : ℕ) (t : ℝ) : dyadicAngle k (-t) = -dyadicAngle k t := by
  unfold dyadicAngle; ring

theorem dyadic_sin_lower (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (hN : t ≤ (2:ℝ)^k) :
    t/(4*(2:ℝ)^k) ≤ Real.sin (dyadicAngle k t) := by
  have hpow : (0:ℝ) < 2^k := by positivity
  have ha : 0 ≤ dyadicAngle k t := by unfold dyadicAngle; positivity
  have hb : dyadicAngle k t ≤ Real.pi/2 := by
    unfold dyadicAngle
    rw [div_le_iff₀ (by positivity : (0:ℝ)<16*2^k)]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hN Real.pi_pos.le]
  have h := Real.mul_le_sin ha hb
  convert h using 1
  unfold dyadicAngle
  field_simp
  ring

theorem dyadicPoint_fst_le_N {k : ℕ} (p : DyadicFreq k) :
    ((dyadicPoint p).1:ℝ) ≤ (2:ℝ)^k := by
  have hr : 2*dyadicRadius p ≤ 2^k := by
    have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) p.1.isLt
    simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hh
  have hp := (dyadicPoint_bounds p).2.1
  have hz : (dyadicPoint p).1 ≤ (2^k:ℕ) := by omega
  exact_mod_cast hz

theorem dyadicLambda_lower (k : ℕ) : (k:ℝ)/2 ≤ dyadicLambda k := by
  have hN : (0:ℝ)<2^k := by positivity
  have hp (p : DyadicFreq k) :
      (1/(dyadicRadius p:ℝ))^2/4 ≤
        (2:ℝ)^k*((1/(dyadicRadius p:ℝ))^3*Real.sin (dyadicAngle k (dyadicPoint p).1)) := by
    have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
    have hpr : (dyadicRadius p:ℝ) ≤ ((dyadicPoint p).1:ℝ) := by exact_mod_cast (dyadicPoint_bounds p).1
    have hs := dyadic_sin_lower k ((dyadicPoint p).1:ℝ) (by linarith) (dyadicPoint_fst_le_N p)
    calc _ = (2:ℝ)^k*((1/(dyadicRadius p:ℝ))^3*((dyadicRadius p:ℝ)/(4*(2:ℝ)^k))) := by field_simp
         _ ≤ _ := by gcongr; exact (div_le_div_of_nonneg_right hpr (by positivity)).trans hs
  unfold dyadicLambda
  rw [Finset.mul_sum]
  calc _ ≤ ∑ p : DyadicFreq k, (1/(dyadicRadius p:ℝ))^2/4 := by
          rw [Fintype.sum_sigma]
          calc _ = ∑ _j : Fin k, (1/2:ℝ) := by simp; ring
               _ ≤ _ := by
                 apply Finset.sum_le_sum
                 intro j _
                 simp only [dyadicRadius, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
                 have hr : (0:ℝ)<(2^j.val:ℕ) := by positivity
                 have hc : 2*((2^j.val:ℕ):ℝ)^2 ≤ (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) := by
                   exact_mod_cast (dyadic_shell_card_bounds j.val).1
                 calc (1/2:ℝ) = (2*((2^j.val:ℕ):ℝ)^2)*((1/((2^j.val:ℕ):ℝ))^2/4) := by field_simp; norm_num
                      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
       _ ≤ _ := Finset.sum_le_sum fun p _ => hp p

def dyadicReflect {k : ℕ} (p : DyadicFreq k) : DyadicFreq k :=
  ⟨p.1, p.2.1, p.2.2.rev⟩

@[simp] theorem dyadicReflect_radius {k : ℕ} (p : DyadicFreq k) :
    dyadicRadius (dyadicReflect p) = dyadicRadius p := rfl

@[simp] theorem dyadicReflect_point {k : ℕ} (p : DyadicFreq k) :
    (dyadicPoint (dyadicReflect p)).2 = -(dyadicPoint p).2 := by
  simp only [dyadicPoint, dyadicReflect, dyadicRadius, Fin.val_rev]
  have h := p.2.2.isLt
  omega

@[simp] theorem dyadicReflect_involution {k : ℕ} (p : DyadicFreq k) :
    dyadicReflect (dyadicReflect p) = p := by
  simp [dyadicReflect]

theorem dyadic_sin_cancel (k : ℕ) :
    (∑ p : DyadicFreq k, (1/(dyadicRadius p:ℝ))^3 *
      Real.sin (dyadicAngle k (dyadicPoint p).2)) = 0 := by
  let e : DyadicFreq k ≃ DyadicFreq k := ⟨dyadicReflect, dyadicReflect, dyadicReflect_involution, dyadicReflect_involution⟩
  have he := Equiv.sum_comp e
    (fun p : DyadicFreq k => (1/(dyadicRadius p:ℝ))^3 * Real.sin (dyadicAngle k (dyadicPoint p).2))
  change (∑ p : DyadicFreq k, (1/(dyadicRadius (dyadicReflect p):ℝ))^3 * Real.sin (dyadicAngle k (dyadicPoint (dyadicReflect p)).2)) = _ at he
  simp only [dyadicReflect_radius, dyadicReflect_point,
    Int.cast_neg, dyadicAngle_neg, Real.sin_neg, mul_neg, Finset.sum_neg_distrib] at he
  linarith

end ClassicalON

end

end OAI
