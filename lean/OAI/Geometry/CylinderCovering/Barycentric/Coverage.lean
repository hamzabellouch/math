import OAI.Geometry.CylinderCovering.Radial.Coordinates
import OAI.Geometry.CylinderCovering.Barycentric.SweepsDefinitions

namespace OAI

namespace CylinderCovering.BarycentricRadial

private theorem abs_mul_le_abs_left {x y : ℝ} (hy : |y| ≤ 1) :
    |x * y| ≤ |x| := by
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg x) hy

private theorem quadratic_bounds {w : ℝ} (hw : |w| ≤ 1) :
    0 ≤ (1 + w ^ 2) / 2 ∧ (1 + w ^ 2) / 2 ≤ 1 := by
  have hw2 : w ^ 2 ≤ 1 := by nlinarith [abs_le.mp hw, sq_abs w]
  constructor <;> nlinarith [sq_nonneg w]

theorem joint_excess_bound {k p q w z S T : ℝ}
    (hk : 0 ≤ k) (hkhalf : k ≤ 1 / 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hw : |w| ≤ 1) (hz : |z| ≤ 1)
    (hS : 1 / 2 ≤ S) (hT : 1 / 2 ≤ T)
    (hsum : 1 = S + T + k * p * w - k * q * z)
    (hfirst : q = S * w + k * p * ((1 + w ^ 2) / 2))
    (hsecond : p = T * z - k * q * ((1 + z ^ 2) / 2)) :
    S + T - 1 ≤
      k ^ 2 * ((w ^ 2 + w ^ 4) / 4 + (z ^ 2 + z ^ 4) / 4) + 10 * k ^ 3 := by
  let E := S + T - 1
  let gw := (1 + w ^ 2) / 2
  let gz := (1 + z ^ 2) / 2
  have hE0 : 0 ≤ E := by dsimp [E]; linarith
  have hST : |S - T| ≤ E := by rw [abs_le]; dsimp [E]; constructor <;> linarith
  have hgw := quadratic_bounds hw
  have hgz := quadratic_bounds hz
  have hgwabs : |gw| ≤ 1 := by dsimp [gw]; rw [abs_of_nonneg hgw.1]; exact hgw.2
  have hgzabs : |gz| ≤ 1 := by dsimp [gz]; rw [abs_of_nonneg hgz.1]; exact hgz.2
  have hpzg : |p * z * gw| ≤ 1 :=
    (abs_mul_le_abs_left hgwabs).trans ((abs_mul_le_abs_left hz).trans hp)
  have hqwg : |q * w * gz| ≤ 1 :=
    (abs_mul_le_abs_left hgzabs).trans ((abs_mul_le_abs_left hw).trans hq)
  have hSTwz : (S - T) * w * z ≤ E :=
    (le_abs_self _).trans ((abs_mul_le_abs_left hz).trans
      ((abs_mul_le_abs_left hw).trans hST))
  have hcross : q * z - p * w = (S - T) * w * z + k * (p * z * gw + q * w * gz) := by
    dsimp [gw, gz]
    linear_combination z * hfirst - w * hsecond
  have hidentity : E = k * ((S - T) * w * z) + k ^ 2 * (p * z * gw + q * w * gz) := by
    calc
      E = k * (q * z - p * w) := by dsimp [E]; linarith [hsum]
      _ = _ := by rw [hcross]; ring
  have hinner : p * z * gw + q * w * gz ≤ 2 := by
    linarith [(le_abs_self (p * z * gw)).trans hpzg,
      (le_abs_self (q * w * gz)).trans hqwg]
  have hpre : E ≤ k * E + 2 * k ^ 2 := by
    have := add_le_add (mul_le_mul_of_nonneg_left hSTwz hk)
      (mul_le_mul_of_nonneg_left hinner (sq_nonneg k))
    nlinarith only [this, hidentity]
  have hE : E ≤ 4 * k ^ 2 := by
    have := mul_le_mul_of_nonneg_right hkhalf hE0
    nlinarith only [this, hpre]
  have hk2 : 4 * k ^ 2 ≤ 2 * k := by
    nlinarith only [mul_nonneg hk (sub_nonneg.mpr hkhalf)]
  have hTpart : |(T - 1 / 2) * z| ≤ E := by
    apply (abs_mul_le_abs_left hz).trans
    rw [abs_of_nonneg (by linarith : 0 ≤ T - 1 / 2)]
    dsimp [E]
    linarith
  have hSpart : |(S - 1 / 2) * w| ≤ E := by
    apply (abs_mul_le_abs_left hw).trans
    rw [abs_of_nonneg (by linarith : 0 ≤ S - 1 / 2)]
    dsimp [E]
    linarith
  have hkqg : |k * q * gz| ≤ k := by
    apply (abs_mul_le_abs_left hgzabs).trans
    apply (abs_mul_le_abs_left hq).trans
    rw [abs_of_nonneg hk]
  have hkpg : |k * p * gw| ≤ k := by
    apply (abs_mul_le_abs_left hgwabs).trans
    apply (abs_mul_le_abs_left hp).trans
    rw [abs_of_nonneg hk]
  have hperr : |p - z / 2| ≤ 3 * k := by
    have heq : p - z / 2 = (T - 1 / 2) * z - k * q * gz := by
      dsimp [gz]; linarith [hsecond]
    rw [heq]
    have htri := (abs_sub ((T - 1 / 2) * z) (k * q * gz)).trans
      (add_le_add hTpart hkqg)
    linarith only [htri, hE, hk2]
  have hqerr : |q - w / 2| ≤ 3 * k := by
    have heq : q - w / 2 = (S - 1 / 2) * w + k * p * gw := by
      dsimp [gw]; linarith [hfirst]
    rw [heq]
    have htri := (abs_add_le ((S - 1 / 2) * w) (k * p * gw)).trans
      (add_le_add hSpart hkpg)
    linarith only [htri, hE, hk2]
  have hperr' : (p - z / 2) * z * gw ≤ 3 * k :=
    (le_abs_self _).trans ((abs_mul_le_abs_left hgwabs).trans
      ((abs_mul_le_abs_left hz).trans hperr))
  have hqerr' : (q - w / 2) * w * gz ≤ 3 * k :=
    (le_abs_self _).trans ((abs_mul_le_abs_left hgzabs).trans
      ((abs_mul_le_abs_left hw).trans hqerr))
  have hbase : p * z * gw + q * w * gz =
      (w ^ 2 + z ^ 2 + 2 * w ^ 2 * z ^ 2) / 4 +
      (p - z / 2) * z * gw + (q - w / 2) * w * gz := by
    dsimp [gw, gz]; ring
  have hinner' : p * z * gw + q * w * gz ≤
      (w ^ 2 + w ^ 4) / 4 + (z ^ 2 + z ^ 4) / 4 + 6 * k := by
    rw [hbase]
    nlinarith only [hperr', hqerr', sq_nonneg (w ^ 2 - z ^ 2)]
  have hfinal := add_le_add (mul_le_mul_of_nonneg_left hSTwz hk)
    (mul_le_mul_of_nonneg_left hinner' (sq_nonneg k))
  have hkE := mul_le_mul_of_nonneg_left hE hk
  rw [← hidentity] at hfinal
  change E ≤ _
  nlinarith only [hfinal, hkE]

theorem capped_alternative {k p q w z S T : ℝ}
    (hk : 0 < k) (hkbound : k ≤ 1 / 5000)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hw : |w| ≤ 1) (hz : |z| ≤ 1)
    (hsum : 1 = S + T + k * p * w - k * q * z)
    (hfirst : q = S * w + k * p * ((1 + w ^ 2) / 2))
    (hsecond : p = T * z - k * q * ((1 + z ^ 2) / 2)) :
    S ≤ 1 / 2 + k ^ 2 * ((w ^ 2 + w ^ 4) / 4 + 1 / 1000) ∨
    T ≤ 1 / 2 + k ^ 2 * ((z ^ 2 + z ^ 4) / 4 + 1 / 1000) := by
  by_contra h
  push Not at h
  have hw0 : 0 ≤ (w ^ 2 + w ^ 4) / 4 + (1 : ℝ) / 1000 := by positivity
  have hz0 : 0 ≤ (z ^ 2 + z ^ 4) / 4 + (1 : ℝ) / 1000 := by positivity
  have hS : 1 / 2 ≤ S := by nlinarith [mul_nonneg (sq_nonneg k) hw0]
  have hT : 1 / 2 ≤ T := by nlinarith [mul_nonneg (sq_nonneg k) hz0]
  have hupper := joint_excess_bound (le_of_lt hk) (by linarith) hp hq hw hz hS hT
    hsum hfirst hsecond
  have hsmall := mul_le_mul_of_nonneg_right hkbound (sq_nonneg k)
  nlinarith only [hupper, h.1, h.2, hsmall]

end CylinderCovering.BarycentricRadial

namespace RadialCoordinates

open Set

theorem nonnegative_complementary_representations {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsum : a + b + c + d = 1) (k : ℝ) :
    ∃ t r S T : ℝ,
      t ∈ Icc 0 1 ∧ r ∈ Icc 0 1 ∧ 0 ≤ S ∧ 0 ≤ T ∧
      a = S * t + k * (c - d) * t ^ 2 ∧
      b = S * (1 - t) - k * (c - d) * (1 - t) ^ 2 ∧
      c = T * r - k * (a - b) * r ^ 2 ∧
      d = T * (1 - r) + k * (a - b) * (1 - r) ^ 2 ∧
      1 = S + T + k * (c - d) * angular t - k * (a - b) * angular r ∧
      a - b = S * angular t + k * (c - d) * ((1 + angular t ^ 2) / 2) ∧
      c - d = T * angular r - k * (a - b) * ((1 + angular r ^ 2) / 2) := by
  obtain ⟨t, S, ht, hS, hat, hbt⟩ :=
    CylinderCovering.BarycentricRadial.exists_nonnegative_radial_representation ha hb (k * (c-d))
  obtain ⟨r, T, hr, hT, hcr, hdr⟩ :=
    CylinderCovering.BarycentricRadial.exists_nonnegative_radial_representation hc hd ((-k) * (a-b))
  have heq1 := radial_representation_sum_difference hat hbt
  have heq2 := radial_representation_sum_difference hcr hdr
  refine ⟨t, r, S, T, ht, hr, hS, hT, hat, hbt, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hcr]
  · nlinarith only [hdr]
  · nlinarith only [heq1.1, heq2.1, hsum]
  · nlinarith only [heq1.2]
  · nlinarith only [heq2.2]

theorem cap_eq_angular_polynomial (k t : ℝ) :
    cap k t = 1 / 2 + k ^ 2 *
      ((angular t ^ 2 + angular t ^ 4) / 4 + 1 / 1000) := by
  unfold cap capPolynomial
  ring

theorem barycentric_simplex_covered {k : ℝ} (hk : 0 < k) (hkbound : k ≤ 1 / 5000) :
    barycentricSimplex ⊆ firstSweep k ∪ secondSweep k := by
  intro v hv
  obtain ⟨hnonneg, hsum⟩ := hv
  have hsum' : v 0 + v 1 + v 2 + v 3 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  obtain ⟨t, r, S, T, ht, hr, hS, hT, hat, hbt, hcr, hdr, heq, heq1, heq2⟩ :=
    nonnegative_complementary_representations (hnonneg 0) (hnonneg 1)
      (hnonneg 2) (hnonneg 3) hsum' k
  have hp : |v 2 - v 3| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hnonneg 0, hnonneg 1, hnonneg 2, hnonneg 3]
  have hq : |v 0 - v 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hnonneg 0, hnonneg 1, hnonneg 2, hnonneg 3]
  have hw : |angular t| ≤ 1 := by
    rw [abs_le]; unfold angular
    constructor <;> linarith [ht.1, ht.2]
  have hz : |angular r| ≤ 1 := by
    rw [abs_le]; unfold angular
    constructor <;> linarith [hr.1, hr.2]
  have hcap := CylinderCovering.BarycentricRadial.capped_alternative hk hkbound
    hp hq hw hz heq heq1 heq2
  rw [← cap_eq_angular_polynomial, ← cap_eq_angular_polynomial] at hcap
  rcases hcap with hcap | hcap
  · exact Or.inl ⟨hsum, t, S, ht, hS, hcap, hp, hat, hbt⟩
  · exact Or.inr ⟨hsum, r, T, hr, hT, hcap, hq, hcr, hdr⟩

end RadialCoordinates

end OAI
