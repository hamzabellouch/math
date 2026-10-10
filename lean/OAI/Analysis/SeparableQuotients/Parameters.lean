import OAI.Analysis.SeparableQuotients.PathCoding

namespace OAI

noncomputable section

/- Admissible parameters for the pure s = k + 2 families and mixed s = 2 family, with q = (s + 1) / s. Integer powers avoid rounding noninteger powers. -/
namespace SeparableQuotient.Parameters

open Filter Topology

def d (n : ℕ) : ℕ := n+11

/-- State stores the exponent scale and twice the sum of all earlier lengths. -/
def state (s : ℕ) : ℕ → ℕ × ℕ
  | 0 => ((d 0 + 1) + 1 + d 0 + (d 0)^2, 0)
  | n+1 =>
    let old := state s n
    let B := old.2 + 2 * 2^(s*(s+1)*old.1)
    (old.1 + (B+1)*(d (n+1)+1) + 1 + d (n+1) + (d (n+1))^2, B)

def t (s n : ℕ) : ℕ := (state s n).1
def B (s n : ℕ) : ℕ := (state s n).2
def L (s n : ℕ) : ℕ := 2^(s*(s+1)*t s n)
def m (s n : ℕ) : ℕ := 2^((s-1)*(s+1)*t s n+d n)
def r (s : ℕ) : ℝ := (s:ℝ)/((s:ℝ)-1)
def q (s : ℕ) : ℝ := ((s:ℝ)+1)/(s:ℝ)
def theta (s n : ℕ) : ℝ := (L s n : ℝ) ^ (1/r s) / (m s n : ℝ)

lemma B_zero (s : ℕ) : B s 0 = 0 := rfl
lemma B_succ (s n : ℕ) : B s (n+1) = B s n + 2*L s n := rfl
lemma t_succ (s n : ℕ) : t s (n+1) =
    t s n+(B s (n+1)+1)*(d (n+1)+1)+1+d (n+1)+(d (n+1))^2 := rfl

lemma d_pos (n : ℕ) : 0 < d n := by simp [d]
lemma L_pos (s n : ℕ) : 0 < L s n := pow_pos (by omega) _
lemma m_pos (s n : ℕ) : 0 < m s n := pow_pos (by omega) _

lemma t_bound (s n : ℕ) : (B s n+1)*(d n+1)+1+d n ≤ t s n := by
  cases n with
  | zero => simp [t, B, state]
  | succ n => rw [t_succ]; omega

lemma t_square (s n : ℕ) : (d n)^2 ≤ t s n := by
  cases n with
  | zero => simp [t, state]
  | succ n => rw [t_succ]; omega

lemma t_pos (s n : ℕ) : 0 < t s n := by
  have := t_bound s n
  omega

lemma t_strict (s : ℕ) : StrictMono (t s) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [t_succ]
  omega

lemma B_eq_sum (s n : ℕ) : B s n = 2 * ∑ i ∈ Finset.range n, L s i := by
  induction n with
  | zero => simp [B_zero]
  | succ n ih => rw [B_succ, ih, Finset.sum_range_succ]; ring

lemma L_strict {s : ℕ} (hs : 2 ≤ s) : StrictMono (L s) := by
  intro i j hij
  apply Nat.pow_lt_pow_right (by omega : 1 < 2)
  exact Nat.mul_lt_mul_of_pos_left (t_strict s hij) (by positivity)

lemma m_strict {s : ℕ} (_hs : 2 ≤ s) : StrictMono (m s) := by
  intro i j hij
  apply Nat.pow_lt_pow_right (by omega : 1 < 2)
  have htt := (t_strict s).monotone hij.le
  have hmul := Nat.mul_le_mul_left ((s-1)*(s+1)) htt
  dsimp [d]
  omega

lemma theta_numerator {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    (L s n : ℝ) ^ (1/r s) = (2:ℝ)^((s-1)*(s+1)*t s n) := by
  have hs0 : (s:ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hs1 : 1 ≤ s := by omega
  simp only [L, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  simp only [r, one_div_div, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub hs1]
  field_simp

lemma theta_eq {s : ℕ} (hs : 2 ≤ s) (n : ℕ) : theta s n = (1/2:ℝ)^(d n) := by
  rw [theta, theta_numerator hs]
  simp only [m]
  push_cast
  rw [pow_add, div_mul_eq_div_div, div_self (by positivity : (2:ℝ)^((s-1)*(s+1)*t s n) ≠ 0)]
  exact (one_div_pow _ _).symm

lemma length_qprime_power (s n : ℕ) :
    (L s n : ℝ) ^ (1/((s:ℝ)+1)) = (2:ℝ)^(s*t s n) := by
  have hs1 : (s:ℝ)+1 ≠ 0 := by positivity
  simp only [L, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  push_cast
  field_simp

lemma ratio_eq {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    (L s n : ℝ) / (m s n : ℝ) = (2:ℝ)^((s+1)*t s n) / (2:ℝ)^(d n) := by
  have hsplit : s*(s+1)*t s n = (s-1)*(s+1)*t s n+(s+1)*t s n := by
    calc
      _ = ((s-1)+1)*(s+1)*t s n := by congr 2; omega
      _ = _ := by ring
  simp only [L, m, Nat.cast_pow, Nat.cast_ofNat]
  rw [hsplit, pow_add, pow_add]
  exact mul_div_mul_left _ _ (by positivity)

lemma depth_integer_bound (s n : ℕ) :
    (1+B s n)^(d n) * (1+B s n+2^(s*t s n)) * 2^(d n) ≤ 2^((s+1)*t s n) := by
  let b := B s n
  let u := t s n
  let e := d n
  have ha : 1+b ≤ 2^(b+1) := by
    have h := @Nat.lt_two_pow_self (b+1)
    omega
  have ha1 : 1 ≤ 2^(b+1) := Nat.one_le_pow _ _ (by omega)
  have hc1 : 1 ≤ 2^(s*u) := Nat.one_le_pow _ _ (by omega)
  have hsum : 1+b+2^(s*u) ≤ 2^(b+1+s*u+1) := by
    have hleft : 1+b ≤ 2^(b+1)*2^(s*u) := ha.trans (by nlinarith)
    have hright : 2^(s*u) ≤ 2^(b+1)*2^(s*u) := by nlinarith
    rw [pow_succ, pow_add]
    omega
  have hp := Nat.pow_le_pow_left ha e
  have hstep : (1+b)^e * (1+b+2^(s*u)) * 2^e ≤
      2^((b+1)*e) * 2^(b+1+s*u+1) * 2^e := by
    have hp' : (1+b)^e ≤ 2^((b+1)*e) := by simpa only [pow_mul] using hp
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hp' hsum)
  calc
    _ ≤ 2^((b+1)*e) * 2^(b+1+s*u+1) * 2^e := hstep
    _ = 2^((b+1)*e+(b+1+s*u+1)+e) := by rw [← pow_add, ← pow_add]
    _ ≤ 2^((s+1)*u) := by
      apply Nat.pow_le_pow_right (by omega : 0 < 2)
      have h := t_bound s n
      change (b+1)*(e+1)+1+e ≤ u at h
      nlinarith

lemma depth_bound {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    (1+(B s n:ℝ))^(d n) *
      (1+(B s n:ℝ)+(L s n:ℝ)^(1/((s:ℝ)+1))) ≤ (L s n:ℝ)/(m s n:ℝ) := by
  rw [length_qprime_power, ratio_eq hs]
  apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(d n))).mpr
  exact_mod_cast depth_integer_bound s n

lemma depth_theta_bound {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    (1/8:ℝ)^(d n) ≤ theta s n := by
  rw [theta_eq hs]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

lemma hasSum_theta {s : ℕ} (hs : 2 ≤ s) :
    HasSum (theta s) (1/1024:ℝ) := by
  have hgeom : HasSum (fun n : ℕ => (1/2:ℝ)^n) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) using 1; norm_num
  have h := hgeom.mul_left ((1/2:ℝ)^11)
  have h' : HasSum (theta s) ((1/2:ℝ)^11*2) := h.congr_fun (by
    intro n
    rw [theta_eq hs, d, pow_add, mul_comm])
  norm_num at h' ⊢
  exact h'

lemma theta_sum_small {s : ℕ} (hs : 2 ≤ s) : ∑' n, theta s n < (1/8:ℝ) := by
  rw [(hasSum_theta hs).tsum_eq]
  norm_num

lemma theta_tail {s : ℕ} (hs : 2 ≤ s) (J : ℕ) :
    ∑' n, theta s (J+n) ≤ 4*theta s J := by
  have hgeom : HasSum (fun n : ℕ => (1/2:ℝ)^n) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) using 1; norm_num
  have htail : HasSum (fun n => theta s (J+n)) (2*theta s J) := by
    have h' : HasSum (fun n => theta s (J+n)) (theta s J*2) :=
      (hgeom.mul_left (theta s J)).congr_fun (by
        intro n
        rw [theta_eq hs, theta_eq hs, d, d]
        rw [show J+n+11 = (J+11)+n by omega, pow_add])
    simpa only [mul_comm] using h'
  rw [htail.tsum_eq]
  have hpos : 0 ≤ theta s J := by rw [theta_eq hs]; positivity
  linarith

lemma reciprocal_le_theta {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    1/(m s n:ℝ) ≤ theta s n := by
  rw [theta, theta_numerator hs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact one_le_pow₀ (by norm_num)

lemma reciprocal_sum_small {s : ℕ} (hs : 2 ≤ s) :
    ∑' n, 1/(m s n:ℝ) < (1/8:ℝ) := by
  have hsum := (hasSum_theta hs).summable
  have hrecip : Summable (fun n => 1/(m s n:ℝ)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) (reciprocal_le_theta hs) hsum
  exact (Summable.tsum_le_tsum (reciprocal_le_theta hs) hrecip hsum).trans_lt
    (theta_sum_small hs)

lemma d_div_t_tendsto (s : ℕ) :
    Tendsto (fun n => (d n:ℝ)/(t s n:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity)
    (g := fun n => 1/(d n:ℝ))
  · intro n
    have hd : 0 < (d n:ℝ) := by exact_mod_cast d_pos n
    have ht : 0 < (t s n:ℝ) := by exact_mod_cast t_pos s n
    apply (div_le_div_iff₀ ht hd).mpr
    simpa only [one_mul, ← sq] using (show (d n:ℝ)^2 ≤ (t s n:ℝ) by exact_mod_cast t_square s n)
  · exact (tendsto_add_atTop_iff_nat 11).mpr tendsto_one_div_atTop_nhds_zero_nat

lemma log_ratio_eq {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    Real.log ((L s n:ℝ)/(m s n:ℝ)) / Real.log (L s n:ℝ) =
      1/(s:ℝ) - ((d n:ℝ)/(t s n:ℝ))/((s:ℝ)*((s:ℝ)+1)) := by
  have hs0 : (s:ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hs1 : (s:ℝ)+1 ≠ 0 := by positivity
  have ht : (t s n:ℝ) ≠ 0 := by exact_mod_cast (t_pos s n).ne'
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  rw [ratio_eq hs, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  simp only [L, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  push_cast
  field_simp

lemma parameter_growth {s : ℕ} (hs : 2 ≤ s) :
    Tendsto (fun n => Real.log ((L s n:ℝ)/(m s n:ℝ)) / Real.log (L s n:ℝ))
      atTop (𝓝 (1/(s:ℝ))) := by
  simp_rw [log_ratio_eq hs]
  convert tendsto_const_nhds.sub ((d_div_t_tendsto s).div_const ((s:ℝ)*((s:ℝ)+1))) using 1
  simp

lemma ratio_tendsto_atTop {s : ℕ} (hs : 2 ≤ s) :
    Tendsto (fun n => (L s n:ℝ)/(m s n:ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n => (2:ℝ)^n)
    (fun n => ?_) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  rw [ratio_eq hs]
  apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(d n))).mpr
  rw [← pow_add]
  apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
  have h := t_bound s n
  have hd : n ≤ d n := by simp [d]
  have hsd : 1 ≤ s+1 := by omega
  nlinarith

lemma s_r_conjugate {s : ℕ} (hs : 2 ≤ s) : Real.HolderConjugate (s:ℝ) (r s) :=
  Real.HolderConjugate.conjExponent (by exact_mod_cast (by omega : 1 < s))

lemma sNext_q_conjugate {s : ℕ} (hs : 2 ≤ s) : Real.HolderConjugate ((s:ℝ)+1) (q s) := by
  have hs0 : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have h := Real.HolderConjugate.conjExponent (p := (s:ℝ)+1) (by linarith)
  simpa only [Real.conjExponent, add_sub_cancel_right, q] using h

lemma q_bounds {s : ℕ} (hs : 2 ≤ s) :
    1 < q s ∧ q s < r s ∧ r s < (s:ℝ)+1 ∧ 1/((s:ℝ)+1) < 1/(s:ℝ) := by
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0:ℝ) < s := by linarith
  have hs1 : (0:ℝ) < (s:ℝ)-1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [q, lt_div_iff₀ hs0]; linarith
  · rw [q, r, div_lt_div_iff₀ hs0 hs1]; nlinarith
  · rw [r, div_lt_iff₀ hs1]; nlinarith
  · exact one_div_lt_one_div_of_lt hs0 (by linarith)

end SeparableQuotient.Parameters

namespace SeparableQuotient.Colors
open CoherentClosures

/-- A partition of ω₁ into countably many unbounded fibers. -/
def partitionEquiv : OmegaOne.{0} ≃ ℕ × OmegaOne.{0} :=
  Classical.choice (Cardinal.eq.mp (by
    simp only [OmegaOne, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_nat,
      Cardinal.mk_ord_toType, Cardinal.aleph0_mul_aleph]))

def color (a : OmegaOne.{0}) : ℕ := (partitionEquiv a).1

def inColor (k : ℕ) (a : OmegaOne.{0}) : OmegaOne.{0} := partitionEquiv.symm (k, a)

@[simp] lemma color_inColor (k : ℕ) (a : OmegaOne.{0}) : color (inColor k a) = k := by
  simp [color, inColor]

lemma inColor_injective (k : ℕ) : Function.Injective (inColor k) := by
  intro a b h
  have := partitionEquiv.symm.injective h
  exact (Prod.mk.inj this).2

lemma fiber_unbounded (k : ℕ) (β : OmegaOne.{0}) :
    ∃ a : OmegaOne.{0}, color a = k ∧ β ≤ a := by
  by_contra! h
  have hlt : ∀ a : OmegaOne.{0}, inColor k a < β := fun a => h _ (color_inColor k a)
  let e : OmegaOne.{0} → Set.Iio β := fun a => ⟨inColor k a, hlt a⟩
  have he : Function.Injective e := fun a b hab =>
    inColor_injective k (congrArg Subtype.val hab)
  have hcard := Cardinal.mk_le_of_injective he
  have hsmall := Cardinal.mk_Iio_lt β (by simp [OmegaOne])
  exact (not_le_of_gt hsmall) hcard

end SeparableQuotient.Colors

end

end OAI
