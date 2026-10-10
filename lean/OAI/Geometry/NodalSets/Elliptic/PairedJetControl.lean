import OAI.Geometry.NodalSets.Elliptic.Logarithm

namespace OAI

namespace Yau.Geometry
noncomputable section

lemma paired_products_control (b v Rp Rm h c F : ℝ)
    (hv : 0 ≤ v) (hh : 0 < h) (hh1 : h ≤ 1) (hc : 0 < c) (hF : 0 ≤ F)
    (hd : c*h*v ≤ Rp-Rm) (hb : |b| ≤ |Rp|+F*v) :
    (c^2/(2*(c+F+1)^2))*h^2*(b^2+v^2) ≤ Rp^2+Rm^2 := by
  let q := |Rp|+|Rm|
  have hq : 0 ≤ q := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hdiff : Rp-Rm ≤ q := by dsimp [q]; linarith [le_abs_self Rp,neg_le_abs Rm]
  have hcv : c*h*v ≤ q := hd.trans hdiff
  have hcb : c*h*|b| ≤ (c+F)*q := by
    have h1 := mul_le_mul_of_nonneg_left hb (mul_nonneg hc.le hh.le)
    have h2 := mul_le_mul_of_nonneg_left hcv hF
    have h3 : h*|Rp| ≤ q := (mul_le_mul_of_nonneg_right hh1 (abs_nonneg Rp)).trans
      (by dsimp [q]; linarith [abs_nonneg Rm])
    have h4 := mul_le_mul_of_nonneg_left h3 hc.le
    nlinarith
  have hs : c*h*(|b|+v) ≤ (c+F+1)*q := by nlinarith
  have hs0 : 0 ≤ c*h*(|b|+v) := by positivity
  have hs2 := pow_le_pow_left₀ hs0 hs 2
  have hb2 : b^2+v^2 ≤ (|b|+v)^2 := by nlinarith [sq_abs b,mul_nonneg (abs_nonneg b) hv]
  have hq2 : q^2 ≤ 2*(Rp^2+Rm^2) := by
    dsimp [q]
    nlinarith [sq_abs Rp,sq_abs Rm,sq_nonneg (|Rp|-|Rm|)]
  have hp : 0 < 2*(c+F+1)^2 := by positivity
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).mpr
  have hleft := mul_le_mul_of_nonneg_left hb2 (by positivity : 0 ≤ c^2*h^2)
  have hright := mul_le_mul_of_nonneg_left hq2 (sq_nonneg (c+F+1))
  nlinarith

lemma opposite_real_products (B Rp Rm ep em pp pm h v a E : ℝ)
    (hh : 0 ≤ h) (hv : 0 ≤ v) (ha : 0 ≤ a)
    (hep : a ≤ ep) (hem : a ≤ em)
    (hpp : pp ≤ -h*v) (hpm : h*v ≤ pm)
    (hRp : |Rp-(B-ep*pp)| ≤ E*h^2*v)
    (hRm : |Rm-(B-em*pm)| ≤ E*h^2*v)
    (hsmall : 2*E*h ≤ a) : a*h*v ≤ Rp-Rm := by
  have hp0 : pp ≤ 0 := hpp.trans (by nlinarith)
  have hm0 : 0 ≤ pm := (mul_nonneg hh hv).trans hpm
  have hpp' : ep*pp ≤ -a*h*v := by
    have h1 := mul_le_mul_of_nonpos_right hep hp0
    have h2 := mul_le_mul_of_nonneg_left hpp ha
    nlinarith
  have hpm' : a*h*v ≤ em*pm := by
    have h1 := mul_le_mul_of_nonneg_right hem hm0
    have h2 := mul_le_mul_of_nonneg_left hpm ha
    nlinarith
  obtain ⟨hpl,hpu⟩ := abs_le.mp hRp
  obtain ⟨hml,hmu⟩ := abs_le.mp hRm
  have he := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hh hv)
  nlinarith

end
end Yau.Geometry

end OAI
