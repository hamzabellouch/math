import OAI.Analysis.LipschitzHilbert.Fourier.PositiveLineKernel
import OAI.Analysis.LipschitzHilbert.Estimates.TileLatticeEnvelope

namespace OAI

/-! The two-point decay estimate behind the positive error convolution.
Only fixed exponents six and three are needed. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem envelope_triangle_base (s l x y : ℝ) :
    1 + ((x-y)/l)^2 ≤ 2 * (1+((x-s)/l)^2) * (1+((y-s)/l)^2) := by
  have heq : (x-y)/l = (x-s)/l - (y-s)/l := by ring
  rw [heq]
  nlinarith [sq_nonneg ((x-s)/l + (y-s)/l),
    sq_nonneg (((x-s)/l)*((y-s)/l))]

theorem envelope_three_product (s l x y : ℝ) :
    lineEnvelope s l 3 x * lineEnvelope s l 3 y ≤ 8 * lineEnvelope y l 3 x := by
  let A := 1+((x-s)/l)^2
  let B := 1+((y-s)/l)^2
  let D := 1+((x-y)/l)^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have h := pow_le_pow_left₀ hD.le (envelope_triangle_base s l x y) 3
  change (A^3)⁻¹ * (B^3)⁻¹ ≤ 8 * (D^3)⁻¹
  rw [← mul_inv, ← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hA 3) (pow_pos hB 3)) (pow_pos hD 3)).mpr
  simpa only [mul_pow, show (2:ℝ)^3=8 by norm_num, one_mul, mul_assoc] using h

theorem envelope_six_product (s l x y : ℝ) :
    lineEnvelope s l 6 x * lineEnvelope s l 6 y ≤
      8 * lineEnvelope y l 3 x * lineEnvelope s l 3 x := by
  have hsmall : lineEnvelope s l 3 y ≤ 1 := by
    simpa only [lineEnvelope, pow_zero, inv_one] using
      lineEnvelope_antitone s l y (by decide : 0 ≤ 3)
  have hpow (z : ℝ) : lineEnvelope s l 6 z = lineEnvelope s l 3 z ^ 2 := by
    unfold lineEnvelope
    rw [show (6:ℕ) = 3*2 from rfl, pow_mul, inv_pow]
  have heq : lineEnvelope s l 6 x * lineEnvelope s l 6 y =
      (lineEnvelope s l 3 x * lineEnvelope s l 3 y) *
        (lineEnvelope s l 3 x * lineEnvelope s l 3 y) := by
    rw [hpow x, hpow y]
    ring
  rw [heq]
  have h1 := envelope_three_product s l x y
  have h2 : lineEnvelope s l 3 x * lineEnvelope s l 3 y ≤ lineEnvelope s l 3 x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall (lineEnvelope_nonneg _ _ _ _)
  calc
    _ ≤ (8 * lineEnvelope y l 3 x) * lineEnvelope s l 3 x :=
      mul_le_mul h1 h2 (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
        (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))
    _ = _ := by ring

theorem two_point_tile_envelope {ι : Type*} [Fintype ι]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site)
    (a b l W x y x' y' : ℝ) (hl : 0 < l) (hW : 0 < W) :
    (∑ i, (lineEnvelope (a+l*(site i).1) l 6 x * lineEnvelope (b+W*(site i).2) W 6 y) *
      (lineEnvelope (a+l*(site i).1) l 6 x' * lineEnvelope (b+W*(site i).2) W 6 y')) ≤
    (64 * (4 * Real.pi)^2) * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y := by
  have hterm (i : ι) :
      (lineEnvelope (a+l*(site i).1) l 6 x * lineEnvelope (b+W*(site i).2) W 6 y) *
      (lineEnvelope (a+l*(site i).1) l 6 x' * lineEnvelope (b+W*(site i).2) W 6 y') ≤
      (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
      (lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y) := by
    have hx := envelope_six_product (a+l*(site i).1) l x x'
    have hy := envelope_six_product (b+W*(site i).2) W y y'
    have h := mul_le_mul hx hy
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
      (mul_nonneg (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _)) (lineEnvelope_nonneg _ _ _ _))
    convert h using 1 <;> ring
  calc
    _ ≤ ∑ i, (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
        (lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) *
        ∑ i, lineEnvelope (a+l*(site i).1) l 3 x * lineEnvelope (b+W*(site i).2) W 3 y :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (64 * lineEnvelope x' l 3 x * lineEnvelope y' W 3 y) * (4*Real.pi)^2 :=
      mul_le_mul_of_nonneg_left (injective_tile_lattice_overlap site hinj a b l W x y
        hl.ne' hW.ne' (by decide : 1 ≤ 3) (by decide : 1 ≤ 3))
        (mul_nonneg (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))
          (lineEnvelope_nonneg _ _ _ _))
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
