import OAI.Computability.BinPacking.Packing.PackingScalar
import OAI.Computability.BinPacking.Trees.CompletionGeometry

namespace OAI

namespace BinPackingGap.IntegerPackingArithmetic

def widthRadix (D : ℕ) : ℕ := 100 * (D + 1)

def geomDenominator (m R D L : ℕ) : ℕ :=
  160 * (R + 1) ^ m * widthRadix D ^ L

def sizeDenominator (n geom : ℕ) : ℕ :=
  10 ^ 9 * primaryBound * 3 ^ n * geom

def signedNumerator (n geom : ℕ) (p q W : ℤ) : ℤ :=
  200000000 * (primaryBound : ℤ) * 3 ^ n * geom +
    1000000 * 3 ^ n * geom * p + 1000 * geom * q + W

def itemNumerator {n : ℕ} (geom : ℕ) (subclass : Subclass)
    (label : Option (Fin n)) (W : ℤ) : ℤ :=
  signedNumerator n geom (primaryScore subclass) (secondaryScore subclass label) W

theorem widthRadix_pos (D : ℕ) : 0 < widthRadix D := by
  unfold widthRadix
  positivity

theorem geomDenominator_pos (m R D L : ℕ) : 0 < geomDenominator m R D L := by
  unfold geomDenominator
  exact Nat.mul_pos (by positivity) (pow_pos (widthRadix_pos D) L)

theorem sizeDenominator_pos (n geom : ℕ) (hgeom : 0 < geom) :
    0 < sizeDenominator n geom := by
  unfold sizeDenominator primaryBound
  positivity

theorem signedNumerator_ratio (n geom : ℕ) (hgeom : 0 < geom)
    (p q W : ℤ) :
    (signedNumerator n geom p q W : ℚ) / (sizeDenominator n geom : ℚ) =
      1 / 5 + gamma * (p : ℚ) + mu n * (q : ℚ) +
        nu n * ((W : ℚ) / geom) := by
  have hg : (geom : ℚ) ≠ 0 := by exact_mod_cast hgeom.ne'
  have hp : (primaryBound : ℚ) ≠ 0 := by norm_num [primaryBound]
  have hq : (3 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  simp only [signedNumerator, sizeDenominator, nu, mu, gamma]
  push_cast
  field_simp [hg, hp, hq]
  ring

theorem itemNumerator_ratio {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ) :
    (itemNumerator geom subclass label W : ℚ) / (sizeDenominator n geom : ℚ) =
      encodedSize subclass label ((W : ℚ) / geom) := by
  exact signedNumerator_ratio n geom hgeom (primaryScore subclass) (secondaryScore subclass label) W

theorem itemNumerator_pos_lt {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    0 < itemNumerator geom subclass label W ∧
      itemNumerator geom subclass label W < (sizeDenominator n geom : ℤ) := by
  have hd : (0 : ℚ) < sizeDenominator n geom := by
    exact_mod_cast sizeDenominator_pos n geom hgeom
  have hs := encodedSize_mem_interval subclass label ((W : ℚ) / geom) hW
  rw [← itemNumerator_ratio geom hgeom subclass label W] at hs
  have hpos : (0 : ℚ) < (itemNumerator geom subclass label W : ℚ) := by
    have hdiv : (0 : ℚ) < (itemNumerator geom subclass label W : ℚ) /
        (sizeDenominator n geom : ℚ) := lt_trans (by norm_num) hs.1
    rcases div_pos_iff.mp hdiv with h | h
    · exact h.1
    · exact (not_lt_of_ge hd.le h.2).elim
  have hlt : (itemNumerator geom subclass label W : ℚ) < (sizeDenominator n geom : ℚ) := by
    have h := (div_lt_iff₀ hd).mp hs.2
    simpa only [one_mul] using h
  constructor
  · exact_mod_cast hpos
  · exact_mod_cast hlt

def rawItem {n : ℕ} (geom : ℕ) (subclass : Subclass)
    (label : Option (Fin n)) (W : ℤ) : ℕ × ℕ :=
  ((itemNumerator geom subclass label W).toNat, sizeDenominator n geom)

theorem rawItem_numerator_cast {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    ((rawItem geom subclass label W).1 : ℤ) = itemNumerator geom subclass label W := by
  exact Int.toNat_of_nonneg (itemNumerator_pos_lt geom hgeom subclass label W hW).1.le

theorem rawItem_valid {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    0 < (rawItem geom subclass label W).1 ∧
      (rawItem geom subclass label W).1 < (rawItem geom subclass label W).2 := by
  have hs := itemNumerator_pos_lt geom hgeom subclass label W hW
  rw [← rawItem_numerator_cast geom hgeom subclass label W hW] at hs
  exact_mod_cast hs

theorem rawItem_ratio {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    ((rawItem geom subclass label W).1 : ℚ) / (rawItem geom subclass label W).2 =
      encodedSize subclass label ((W : ℚ) / geom) := by
  have hc : ((rawItem geom subclass label W).1 : ℚ) =
      (itemNumerator geom subclass label W : ℚ) := by
    exact_mod_cast rawItem_numerator_cast geom hgeom subclass label W hW
  rw [hc]
  exact itemNumerator_ratio geom hgeom subclass label W

def localNumerator (D L ell : ℕ) : ℕ := 10 * widthRadix D ^ (L - ell)

theorem geomDenominator_mul_gap (m R D L : ℕ) :
    (geomDenominator m R D L : ℚ) * Geometry.gap m R =
      10 * (widthRadix D : ℚ) ^ L := by
  have hp : ((R : ℚ) + 1) ^ m ≠ 0 :=
    pow_ne_zero m (by positivity)
  unfold geomDenominator Geometry.gap
  push_cast
  field_simp [hp]
  ring

theorem geomDenominator_mul_lambda (m R D L ell : ℕ) (hell : ell ≤ L) :
    (geomDenominator m R D L : ℚ) * Geometry.lambda m R D ell =
      (localNumerator D L ell : ℚ) := by
  have hc : (widthRadix D : ℚ) ≠ 0 := by
    exact_mod_cast (widthRadix_pos D).ne'
  have hpow : (widthRadix D : ℚ) ^ L =
      (widthRadix D : ℚ) ^ ell * (widthRadix D : ℚ) ^ (L - ell) := by
    rw [← pow_add, Nat.add_sub_of_le hell]
  have hrad : (100 * ((D : ℚ) + 1)) = (widthRadix D : ℚ) := by
    simp [widthRadix]
  rw [Geometry.lambda, ← mul_div_assoc, geomDenominator_mul_gap, hrad, hpow]
  simp only [localNumerator, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  field_simp [hc]

theorem geomDenominator_mul_delta (m R D L : ℕ) :
    (geomDenominator m R D L : ℚ) * Geometry.delta m R D L = 1 := by
  rw [Geometry.delta, ← mul_div_assoc, geomDenominator_mul_lambda m R D L L le_rfl]
  norm_num [localNumerator]

def baselineNumerator (m R D L : ℕ) (r : Geometry.Position m R) : ℤ :=
  80 * (R + 1 : ℤ) ^ m * (widthRadix D : ℤ) ^ L +
    10 * (widthRadix D : ℤ) ^ L *
      (((r.2.val : ℤ) + 1) * (R + 1 : ℤ) ^ r.1.val - 1)

def betaNumerator (m R D L : ℕ) (e : Fin m) : ℤ :=
  10 * (widthRadix D : ℤ) ^ L * ((R + 1 : ℤ) ^ e.val - 1)

theorem geomDenominator_mul_baseline (m R D L : ℕ) (r : Geometry.Position m R) :
    (geomDenominator m R D L : ℚ) * Geometry.baseline m R r =
      (baselineNumerator m R D L r : ℚ) := by
  rw [Geometry.baseline, mul_add, ← mul_assoc, geomDenominator_mul_gap]
  simp only [baselineNumerator, Geometry.heightCode, geomDenominator]
  push_cast
  ring

theorem geomDenominator_mul_beta (m R D L : ℕ) (e : Fin m) :
    (geomDenominator m R D L : ℚ) * Geometry.beta m R e =
      (betaNumerator m R D L e : ℚ) := by
  rw [Geometry.beta, ← mul_assoc, geomDenominator_mul_gap]
  simp only [betaNumerator, Geometry.theta]
  push_cast
  ring

end BinPackingGap.IntegerPackingArithmetic

end OAI
