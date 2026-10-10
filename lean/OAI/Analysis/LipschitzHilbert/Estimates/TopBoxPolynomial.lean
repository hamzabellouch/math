import OAI.Analysis.LipschitzHilbert.Estimates.WeightedExceptionalArea
import OAI.Analysis.LipschitzHilbert.Packets.TopWeightedPacket
import OAI.Analysis.LipschitzHilbert.Packets.PacketBoxes

namespace OAI

/-! Fixed polynomial top weights dominate the reciprocal lattice decay
uniformly on a whole box and all its allowed vertical shifts. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem box_polynomial_base_two (a r k x : ℝ) (hr : 0 < r)
    (hx : |x-(a+r*k)| ≤ 2*r) :
    (1+k^2)/16 ≤ 1+((x-a)/r)^2 := by
  let t := (x-a)/r
  have hd : |t-k| ≤ 2 := by
    have heq : t-k = (x-(a+r*k))/r := by dsimp [t]; field_simp; ring
    rw [heq, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    exact hx
  have hs : (t-k)^2 ≤ 4 := by nlinarith [abs_le.mp hd, sq_abs (t-k)]
  dsimp only [t] at *
  nlinarith [sq_nonneg (k-2*((x-a)/r)), sq_nonneg ((x-a)/r)]

theorem topWeight_box_lower (a b r R x z v : ℝ) (p : ℤ × ℤ) (q : ℕ)
    (hr : 0 < r) (hR : 0 < R)
    (hx : |x-(a+r*p.1)| ≤ r) (hz : |z-(b+R*p.2)| ≤ R) (hv : |v| ≤ R) :
    ((boxVariationWeight p)⁻¹/256)^q ≤
      polynomialWeight a r q x * polynomialWeight b R q (z+v) := by
  have hx2 : |x-(a+r*p.1)| ≤ 2*r := hx.trans (by linarith)
  have hz2 : |(z+v)-(b+R*p.2)| ≤ 2*R := by
    calc
      _ = |(z-(b+R*p.2))+v| := by congr 1; ring
      _ ≤ |z-(b+R*p.2)|+|v| := abs_add_le _ _
      _ ≤ 2*R := by linarith
  have h1 := box_polynomial_base_two a r p.1 x hr hx2
  have h2 := box_polynomial_base_two b R p.2 (z+v) hR hz2
  have hprod := mul_le_mul h1 h2 (by positivity : 0 ≤ (1+(p.2:ℝ)^2)/16)
    (by positivity : 0 ≤ 1+((x-a)/r)^2)
  have hinv : (boxVariationWeight p)⁻¹ = (1+(p.1:ℝ)^2)*(1+(p.2:ℝ)^2) := by
    simp only [boxVariationWeight, lineEnvelope, sub_zero, div_one, pow_one, mul_inv_rev, inv_inv]
    ring
  rw [hinv]
  have hbase : ((1+(p.1:ℝ)^2)*(1+(p.2:ℝ)^2))/256 ≤
      (1+((x-a)/r)^2)*(1+((z+v-b)/R)^2) := by nlinarith [hprod]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤
    ((1+(p.1:ℝ)^2)*(1+(p.2:ℝ)^2))/256) hbase q
  simpa only [polynomialWeight, ← div_pow, mul_pow] using hp

end LipschitzHilbert

end

end OAI
