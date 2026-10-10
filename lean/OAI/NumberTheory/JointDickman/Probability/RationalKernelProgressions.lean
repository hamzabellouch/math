import OAI.NumberTheory.JointDickman.Probability.RationalGeometricKernel

namespace OAI

/-! # Rational geometric kernels along a progression -/
namespace JointDickman
open Finset

theorem rational_geometric_progression_bound (q : ℕ) (hq : 0 < q)
    (a : ℕ) (ha : a.Coprime q) (d N L : ℕ) :
    (∑ k ∈ Icc 1 L, geometricSquareKernel N ((a:ℝ)/q*d*k)) ≤
      (N:ℝ)^2*(L:ℝ)*(Nat.gcd d q:ℝ)/q +
      (N:ℝ)*((L:ℝ)+2*((q/Nat.gcd d q:ℕ):ℝ)) := by
  let g := Nat.gcd d q
  let q' := q/g
  let d' := d/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right d hq
  have hgd : g ∣ d := Nat.gcd_dvd_left d q
  have hgq : g ∣ q := Nat.gcd_dvd_right d q
  have hq' : 0 < q' := Nat.div_pos (Nat.le_of_dvd hq hgq) hg
  let : NeZero q' := ⟨hq'.ne'⟩
  have hd' : d'.Coprime q' := Nat.coprime_div_gcd_div_gcd hg
  have ha' : a.Coprime q' := ha.of_dvd_right (Nat.div_dvd_of_dvd hgq)
  have hc : (a*d').Coprime q' := ha'.mul_left hd'
  have hqr : (q:ℝ) = (g:ℝ)*(q':ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgq).symm
  have hdr : (d:ℝ) = (g:ℝ)*(d':ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgd).symm
  have hgR : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hqR : (q':ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
  have hphase : (a:ℝ)/(q:ℝ)*d = ((a*d':ℕ):ℝ)/(q':ℝ) := by
    rw [hqr,hdr,Nat.cast_mul]
    field_simp
  have hbound := rational_geometric_kernel_sum_coprime N L (a*d') hc
  simp_rw [hphase]
  apply hbound.trans_eq
  change (N:ℝ)^2*(L:ℝ)/(q':ℝ) + (N:ℝ)*((L:ℝ)+2*(q':ℝ)) =
    (N:ℝ)^2*(L:ℝ)*(g:ℝ)/(q:ℝ) + (N:ℝ)*((L:ℝ)+2*(q':ℝ))
  congr 1
  rw [hqr]
  field_simp

end JointDickman

end OAI
