import OAI.NumberTheory.TotientAsymptotic.TripleSieveDenominator

namespace OAI

/-! Exactly the primes dividing ab(b-a) can merge roots of the three forms. -/
noncomputable section
namespace TotientAsymptotic

def tripleDiscriminant (a b : ℕ) : ℕ := a*b*(b-a)

lemma tripleDiscriminant_pos {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    0 < tripleDiscriminant a b :=
  Nat.mul_pos (Nat.mul_pos ha (ha.trans hab)) (Nat.sub_pos_of_lt hab)

lemma tripleRootCount_of_not_dvd {a b p : ℕ} (hab : a < b) (hp : p.Prime)
    (hd : ¬p ∣ tripleDiscriminant a b) : tripleRootCount p a b = 3 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have ha : ¬p ∣ a := fun h => hd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) (b-a))
  have hb : ¬p ∣ b := fun h => hd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) (b-a))
  have hdiff : ¬p ∣ b-a := fun h => hd (dvd_mul_of_dvd_right h (a*b))
  have hneq : (a:ZMod p) ≠ b := by
    intro he
    apply hdiff
    apply (ZMod.natCast_eq_zero_iff (b-a) p).mp
    rw [Nat.cast_sub hab.le,he,sub_self]
  rw [tripleRootCount_eq_card]
  exact tripleSieveRoots_card_eq_three p a b ha hb hneq

lemma tripleRootCount_bounds (a b p : ℕ) (hp : p.Prime) :
    1 ≤ tripleRootCount p a b ∧ tripleRootCount p a b ≤ 3 := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [tripleRootCount_eq_card]
  exact ⟨Finset.card_pos.mpr ⟨0,zero_mem_tripleSieveRoots p a b⟩,tripleSieveRoots_card_le p a b⟩

lemma tripleSieveWeight_euler_factor {a b p : ℕ} (hab : a < b) (hp : p.Prime)
    (hp3 : 3 < p) : ((p:ℝ)/(p-1))^3 ≤
      (1+tripleSieveWeight a b p)*
        (if p ∣ tripleDiscriminant a b then ((p:ℝ)/(p-1))^2 else 1) := by
  have hpR : (3:ℝ) < p := by exact_mod_cast hp3
  have hb := tripleRootCount_bounds a b p hp
  have hk1 : (1:ℝ) ≤ tripleRootCount p a b := by exact_mod_cast hb.1
  have hk3 : (tripleRootCount p a b:ℝ) ≤ 3 := by exact_mod_cast hb.2
  have he : 1+tripleSieveWeight a b p = (p:ℝ)/(p-tripleRootCount p a b) := by
    rw [tripleSieveWeight,tripleSieveDensity_prime a b p hp]
    field_simp [show (p:ℝ)-(tripleRootCount p a b:ℝ) ≠ 0 by linarith]
    ring
  rw [he]
  split_ifs with hd
  · have hsingle : (p:ℝ)/(p-1) ≤ (p:ℝ)/(p-tripleRootCount p a b) := by
      apply div_le_div_of_nonneg_left (by linarith) (by linarith)
      linarith
    have hh := mul_le_mul_of_nonneg_right hsingle (sq_nonneg ((p:ℝ)/(p-1)))
    nlinarith
  · rw [tripleRootCount_of_not_dvd hab hp hd,mul_one]
    norm_num only [Nat.cast_ofNat]
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos (by linarith : (0:ℝ) < p-1) 3) (by linarith)).mpr
    nlinarith

end TotientAsymptotic

end

end OAI
