import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope

namespace OAI

/-! Put translated sheared packet lattices on a common reference lattice.
The site map is injective and moves each center by at most one mesh in
both coordinates. No equality of the physical and reference lattices is
assumed. -/

noncomputable section
namespace LipschitzHilbert

/-- Quantize a translated, sheared lattice without identifying distinct
sites of that lattice. The shear is measured in the reference coordinates. -/
def snappedLatticeSite (a b l W delta : ℝ) (q : ℤ × ℤ) : ℤ × ℤ :=
  (⌊a/l⌋+q.1,⌊(b+delta*l*q.1)/W⌋+q.2)

theorem snappedLatticeSite_injective (a b l W delta : ℝ) :
    Function.Injective (snappedLatticeSite a b l W delta) := by
  intro q q' h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  change ⌊a/l⌋+q.1 = ⌊a/l⌋+q'.1 at hx
  have hx' : q.1 = q'.1 := add_left_cancel hx
  change ⌊(b+delta*l*q.1)/W⌋+q.2 = ⌊(b+delta*l*q'.1)/W⌋+q'.2 at hy
  rw [hx'] at hy
  exact Prod.ext hx' (add_left_cancel hy)

theorem floor_mesh_error (x l : ℝ) (hl : 0 < l) :
    |x-l*(⌊x/l⌋:ℤ)| ≤ l := by
  have hlo := Int.floor_le (x/l)
  have hhi := Int.lt_floor_add_one (x/l)
  have hlo' := (le_div_iff₀ hl).mp hlo
  have hhi' := (div_lt_iff₀ hl).mp hhi
  apply abs_le.mpr
  constructor <;> nlinarith

theorem snappedLatticeSite_horizontal (a b l W delta : ℝ) (hl : 0 < l) (q : ℤ × ℤ) :
    |(a+l*q.1)-l*(snappedLatticeSite a b l W delta q).1| ≤ l := by
  have h := floor_mesh_error a l hl
  convert h using 1
  congr 1
  simp only [snappedLatticeSite,Int.cast_add]
  ring

theorem snappedLatticeSite_vertical (a b l W delta : ℝ) (hW : 0 < W) (q : ℤ × ℤ) :
    |(b+delta*l*q.1+W*q.2)-W*(snappedLatticeSite a b l W delta q).2| ≤ W := by
  have h := floor_mesh_error (b+delta*l*q.1) W hW
  convert h using 1
  congr 1
  simp only [snappedLatticeSite,Int.cast_add]
  ring

/-- Moving a center by at most one mesh preserves any fixed decay order. -/
theorem lineEnvelope_near_center (a b l x : ℝ) (n : ℕ) (hl : 0 < l)
    (hab : |a-b| ≤ l) :
    lineEnvelope a l n x ≤ 3^n*lineEnvelope b l n x := by
  let u := (x-a)/l
  let d := (a-b)/l
  have hd : |d| ≤ 1 := by
    dsimp [d]
    rw [abs_div,abs_of_pos hl]
    exact (div_le_one hl).mpr hab
  have hd2 : d^2 ≤ 1 := by nlinarith [abs_le.mp hd,sq_abs d]
  have hv : (x-b)/l = u+d := by dsimp [u,d]; ring
  have hbase : 1+((x-b)/l)^2 ≤ 3*(1+((x-a)/l)^2) := by
    rw [hv]
    change 1+(u+d)^2 ≤ 3*(1+u^2)
    nlinarith [sq_nonneg (u-d)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+((x-b)/l)^2) hbase n
  have ha : 0 < (1+((x-a)/l)^2)^n := by positivity
  have hb : 0 < (1+((x-b)/l)^2)^n := by positivity
  unfold lineEnvelope
  rw [← one_div,← div_eq_mul_inv]
  apply (div_le_div_iff₀ ha hb).mpr
  simpa only [one_mul,mul_pow] using hp

/-- Product decay survives the actual center quantization with fixed cost. -/
theorem snappedLatticeSite_envelope (a b l W delta x y : ℝ)
    (hl : 0 < l) (hW : 0 < W) (q : ℤ × ℤ) (nx ny : ℕ) :
    lineEnvelope (a+l*q.1) l nx x *
        lineEnvelope (b+delta*l*q.1+W*q.2) W ny y ≤
      (3^nx*3^ny) *
        (lineEnvelope (l*(snappedLatticeSite a b l W delta q).1) l nx x *
          lineEnvelope (W*(snappedLatticeSite a b l W delta q).2) W ny y) := by
  have hx := lineEnvelope_near_center (a+l*q.1)
    (l*(snappedLatticeSite a b l W delta q).1) l x nx hl
    (snappedLatticeSite_horizontal a b l W delta hl q)
  have hy := lineEnvelope_near_center (b+delta*l*q.1+W*q.2)
    (W*(snappedLatticeSite a b l W delta q).2) W y ny hW
    (snappedLatticeSite_vertical a b l W delta hW q)
  have h := mul_le_mul hx hy (lineEnvelope_nonneg _ _ _ _)
    (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
  convert h using 1
  ring

end LipschitzHilbert

end

end OAI
