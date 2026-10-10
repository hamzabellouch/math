import OAI.Combinatorics.EditDistance.PrimePool
import OAI.Combinatorics.EditDistance.FamilyRecursion

namespace OAI

/-!
# Recursive parameter bounds and exponential lower scales
-/

namespace EditParameters
open EditFamily

def b (k : ℕ) := 100*k
def P (k : ℕ) := (b k)^2
def h (k : ℕ) := 10*k
noncomputable def eta (k : ℕ) : ℝ := 2 * (2 * (P k : ℝ)) ^ (2 * h k) / ((P k) ^ (b k / 2) : ℕ)

lemma prime_parameter_pos {k : ℕ} (hk : 0 < k) : 0 < P k := by
  unfold P b
  positivity

lemma eta_numerator_bound {k : ℕ} (hk : 0 < k) :
    2 * (2 * P k) ^ (2 * h k) * (h k)^k ≤ (P k) ^ (b k / 2) := by
  have hp : 4 ≤ P k := by dsimp [P,b]; nlinarith
  have hh : h k ≤ P k := by dsimp [h,P,b]; nlinarith
  have hpow : (2 * P k)^2 ≤ (P k)^3 := by nlinarith
  have he1 : 2*h k = 2*(10*k) := by rfl
  have he2 : b k / 2 = 50*k := by dsimp [b]; omega
  have htwo : 2 ≤ (P k)^k := le_trans (by omega : 2 ≤ P k)
    (Nat.le_self_pow (by omega) _)
  calc
    2 * (2*P k)^(2*h k) * (h k)^k ≤
        (P k)^k * ((P k)^3)^(10*k) * (P k)^k := by
          rw [he1,pow_mul]
          gcongr
    _ = (P k)^(32*k) := by rw [←pow_mul,←pow_add,←pow_add]; congr 1; omega
    _ ≤ (P k)^(b k / 2) := Nat.pow_le_pow_right (by omega) (by rw [he2]; omega)

lemma eta_le {k : ℕ} (hk : 0 < k) : eta k ≤ 1 / (h k : ℝ)^k := by
  have hp : (0 : ℝ) < ((P k)^(b k/2) : ℕ) := by
    exact_mod_cast pow_pos (prime_parameter_pos hk) _
  have hh : (0 : ℝ) < (h k : ℝ)^k := by dsimp [h]; positivity
  apply (div_le_div_iff₀ hp hh).mpr
  simpa only [one_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    (show (2 : ℝ) * (2*(P k : ℝ))^(2*h k) * (h k : ℝ)^k ≤ ((P k)^(b k/2) : ℕ) by
      exact_mod_cast eta_numerator_bound hk)

lemma budget_bound {k : ℕ} (hk : 0 < k) (s : ℕ) :
    familyBudget (b k) (P k) (h k) s ≤ 2/(h k : ℝ)^s + 2*eta k := by
  have hp : (0 : ℝ) < h k := by dsimp [h]; positivity
  have htwo : (2 : ℝ) ≤ h k := by exact_mod_cast (show 2 ≤ h k by dsimp [h]; omega)
  have he : 0 ≤ eta k := by dsimp [eta]; positivity
  induction s with
  | zero => simp only [familyBudget,pow_zero,div_one]; linarith
  | succ s ih =>
    change eta k + familyBudget (b k) (P k) (h k) s / h k ≤ _
    calc
      _ ≤ eta k + (2/(h k : ℝ)^s+2*eta k)/(h k) := by gcongr
      _ = 2/(h k : ℝ)^(s+1) + (eta k + 2*eta k/(h k)) := by
        rw [pow_succ]; field_simp; ring
      _ ≤ 2/(h k : ℝ)^(s+1) + 2*eta k := by
        have ht : 2*eta k/(h k) ≤ eta k := (div_le_iff₀ hp).mpr (by nlinarith)
        linarith

theorem budget_small {k : ℕ} (hk : 0 < k) :
    familyBudget (b k) (P k) (h k) k ≤ 4/(h k : ℝ)^k := by
  have h1 := budget_bound hk k
  have h2 := eta_le hk
  simp only [div_eq_mul_inv,one_mul] at *
  linarith

def codeBits (k : ℕ) := Nat.clog 2 (familyAlphabet (b k) (P k) k)
def codeWidth (k : ℕ) := 2*codeBits k+3
def encodedLength (k : ℕ) := codeWidth k * familyLength (b k) (P k) k

lemma alphabet_power_bound {k : ℕ} (hk : 0 < k) :
    familyAlphabet (b k) (P k) k ≤ 2^(30*k^2) := by
  have hb : 0 < b k := by dsimp [b]; omega
  have hp : 0 < P k := prime_parameter_pos hk
  have hkb : k ≤ 2^k := Nat.lt_two_pow_self.le
  have hbpow : 2*b k ≤ 2^(k+8) := by
    simp only [pow_add]
    norm_num only [show 2^8=256 by norm_num]
    dsimp [b]
    nlinarith
  have hppow : 2*P k+1 ≤ 2^(2*k+16) := by
    calc
      2*P k+1 ≤ (2*b k)^2 := by dsimp [P]; nlinarith
      _ ≤ (2^(k+8))^2 := Nat.pow_le_pow_left hbpow 2
      _ = _ := by rw [←pow_mul]; congr 1; ring
  calc
    familyAlphabet (b k) (P k) k ≤ (2*P k+1)*(2*b k)^k := familyAlphabet_le hb hp k
    _ ≤ 2^(2*k+16)*(2^(k+8))^k := Nat.mul_le_mul hppow (Nat.pow_le_pow_left hbpow k)
    _ = 2^(k^2+10*k+16) := by rw [←pow_mul,←pow_add]; congr 1; ring
    _ ≤ 2^(30*k^2) := Nat.pow_le_pow_right (by omega) (by nlinarith)

lemma bits_poly {k : ℕ} (hk : 0 < k) : codeBits k ≤ 30*k^2 :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mpr (alphabet_power_bound hk)

lemma width_poly {k : ℕ} (hk : 0 < k) : codeWidth k ≤ 63*k^2 := by
  have ht := bits_poly hk
  dsimp [codeWidth]
  nlinarith

lemma width_pos (k : ℕ) : 0 < codeWidth k := by dsimp [codeWidth]; omega
lemma encodedLength_pos {k : ℕ} (hk : 0 < k) : 0 < encodedLength k :=
  Nat.mul_pos (width_pos k) (familyLength_pos (by dsimp [b]; omega) (prime_parameter_pos hk) k)

lemma length_power_bound (k : ℕ) : familyLength (b k) (P k) k ≤
    (4*(b k)^(100*k+1))^k := by
  have he : b k / 2 = 50*k := by dsimp [b]; omega
  unfold familyLength
  apply Nat.pow_le_pow_left
  calc
    2*(2*b k-1)*(P k)^(b k/2) ≤ 4*b k*(P k)^(b k/2) :=
      Nat.mul_le_mul_right _ (by have := Nat.sub_le (2*b k) 1; omega)
    _ = 4*(b k)^(100*k+1) := by
      dsimp [P]
      rw [he,←pow_mul,pow_succ]
      have he' : 2*(50*k)=100*k := by omega
      rw [he']
      ring

theorem log_length_bound {k : ℕ} (hk : 2 ≤ k) :
    Real.log (encodedLength k : ℝ) ≤ 1000*(k : ℝ)^2*Real.log (k : ℝ) := by
  have hkpos : 0 < k := by omega
  have kr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have kp : (0 : ℝ) < k := by positivity
  have bp : (0 : ℝ) < b k := by dsimp [b]; positivity
  have wp : (0 : ℝ) < codeWidth k := by exact_mod_cast width_pos k
  have np : (0 : ℝ) < familyLength (b k) (P k) k := by
    exact_mod_cast familyLength_pos (by dsimp [b]; omega) (prime_parameter_pos hkpos) k
  have lk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have l2 : Real.log (2 : ℝ) ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) kr
  have l63 : Real.log (63 : ℝ) ≤ 6*Real.log (2 : ℝ) := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ)<63) (by norm_num : (63 : ℝ) ≤ 2^6)
    simpa only [Real.log_pow,Nat.cast_ofNat] using ht
  have l100 : Real.log (100 : ℝ) ≤ 7*Real.log (2 : ℝ) := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ)<100) (by norm_num : (100 : ℝ) ≤ 2^7)
    simpa only [Real.log_pow,Nat.cast_ofNat] using ht
  have l4 : Real.log (4 : ℝ) = 2*Real.log (2 : ℝ) := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have lb : Real.log (b k : ℝ) ≤ 8*Real.log (k : ℝ) := by
    simp only [b,Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (100 : ℝ) ≠ 0) kp.ne']
    linarith
  have lw : Real.log (codeWidth k : ℝ) ≤ 8*Real.log (k : ℝ) := by
    have hw : (codeWidth k : ℝ) ≤ 63*(k : ℝ)^2 := by exact_mod_cast width_poly hkpos
    have hl := Real.log_le_log wp hw
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have ln : Real.log (familyLength (b k) (P k) k : ℝ) ≤
      (k : ℝ)*(Real.log (4 : ℝ)+(100*(k : ℝ)+1)*Real.log (b k : ℝ)) := by
    have hn : (familyLength (b k) (P k) k : ℝ) ≤
        (4*(b k : ℝ)^(100*k+1))^k := by exact_mod_cast length_power_bound k
    have hl := Real.log_le_log np hn
    rw [Real.log_pow,Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hl
    push_cast at hl
    exact hl
  have he : Real.log (encodedLength k : ℝ) =
      Real.log (codeWidth k : ℝ)+Real.log (familyLength (b k) (P k) k : ℝ) := by
    simp only [encodedLength,Nat.cast_mul,Real.log_mul wp.ne' np.ne']
  rw [he]
  calc
    _ ≤ 8*Real.log (k : ℝ)+(k : ℝ)*(2*Real.log (k : ℝ)+
        (100*(k : ℝ)+1)*(8*Real.log (k : ℝ))) := by
      apply add_le_add lw
      apply ln.trans
      gcongr
      linarith
    _ = (800*(k : ℝ)^2+10*(k : ℝ)+8)*Real.log (k : ℝ) := by ring
    _ ≤ 1000*(k : ℝ)^2*Real.log (k : ℝ) := by
      gcongr
      nlinarith

noncomputable def lowerRatio (k : ℕ) : ℝ := ((h k : ℝ)/24)^k/(16*(codeWidth k : ℝ))

lemma log_width_le {k : ℕ} (hk : 0 < k) :
    Real.log (codeWidth k : ℝ) ≤ Real.log (63 : ℝ)+2*Real.log (k : ℝ) := by
  have hw : (codeWidth k : ℝ) ≤ 63*(k : ℝ)^2 := by exact_mod_cast width_poly hk
  have wp : (0 : ℝ) < codeWidth k := by exact_mod_cast width_pos k
  have kp : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := Real.log_le_log wp hw
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

theorem ratio_exponential {k : ℕ} (hk : 24^4 ≤ k) :
    Real.exp ((1/2 : ℝ)*(k : ℝ)*Real.log (k : ℝ)) ≤ lowerRatio k := by
  have hk0 : 0 < k := by norm_num at hk; omega
  have kp : (0 : ℝ) < k := by exact_mod_cast hk0
  have k12 : (12 : ℝ) ≤ k := by exact_mod_cast (show 12 ≤ k by norm_num at hk; omega)
  have k1008 : (1008 : ℝ) ≤ k := by exact_mod_cast (show 1008 ≤ k by norm_num at hk; omega)
  have hn : (0 : ℝ) < h k := by dsimp [h]; positivity
  have wp : (0 : ℝ) < codeWidth k := by exact_mod_cast width_pos k
  have rp : 0 < lowerRatio k := by dsimp [lowerRatio]; positivity
  apply (Real.le_log_iff_exp_le rp).mp
  have lkp : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have l24 : 4*Real.log (24 : ℝ) ≤ Real.log (k : ℝ) := by
    have ht := Real.log_le_log (by norm_num : (0 : ℝ)<24^4)
      (show (24 : ℝ)^4 ≤ k by exact_mod_cast hk)
    simpa only [Real.log_pow,Nat.cast_ofNat] using ht
  have lh : Real.log (k : ℝ) ≤ Real.log (h k : ℝ) := by
    apply Real.log_le_log kp
    dsimp [h]; push_cast; nlinarith
  have lw := log_width_le hk0
  have lconst : Real.log (16 : ℝ)+Real.log (63 : ℝ) ≤ Real.log (k : ℝ) := by
    rw [←Real.log_mul (by norm_num) (by norm_num)]
    norm_num only [show (16 : ℝ)*63=1008 by norm_num]
    exact Real.log_le_log (by norm_num) k1008
  have logeq : Real.log (lowerRatio k) =
      (k : ℝ)*(Real.log (h k : ℝ)-Real.log (24 : ℝ))-
        (Real.log (16 : ℝ)+Real.log (codeWidth k : ℝ)) := by
    dsimp [lowerRatio]
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow,
      Real.log_div hn.ne' (by norm_num),Real.log_mul (by norm_num) wp.ne']
  rw [logeq]
  have h1 := mul_le_mul_of_nonneg_left lh kp.le
  have h2 := mul_le_mul_of_nonneg_left l24 kp.le
  have h3 : 12*Real.log (k : ℝ) ≤ (k : ℝ)*Real.log (k : ℝ) :=
    mul_le_mul_of_nonneg_right k12 lkp
  nlinarith

end EditParameters

end OAI
