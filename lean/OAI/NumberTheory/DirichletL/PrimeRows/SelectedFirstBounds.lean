import OAI.NumberTheory.DirichletL.PrimeRows.SelectedFirst

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion

lemma compensatedReplacement_crude (V W D M B q : ℂ) (A E : ℝ)
    (hA : 0≤A) (hE : 0≤E) (hV : ‖V‖≤1) (hW : ‖W‖≤A)
    (hD : ‖D‖≤1/2) (hM : ‖M‖≤388) (hB : ‖B‖≤E) (hq : ‖q‖≤A) :
    ‖ProbeLocal.compensatedReplacement V W D M B q‖≤
      2*((E+A)*2*(1+A)*388+A*(1+A)) := by
  have h1V : ‖1-V‖≤2 := by have h := norm_sub_le (1:ℂ) V;rw [norm_one] at h;linarith
  have h1W : ‖1-W‖≤1+A := by have h := norm_sub_le (1:ℂ) W;rw [norm_one] at h;linarith
  have h1VW : ‖1-V*W‖≤1+A := by
    apply (norm_sub_le (1:ℂ) (V*W)).trans
    rw [norm_one,norm_mul]
    have hm := (mul_le_mul hV hW (norm_nonneg _) (by norm_num)).trans_eq (one_mul A)
    linarith
  have hi := ProbeLocal.inv_one_sub_norm_le_two D hD
  unfold ProbeLocal.compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ ((‖B-q‖*‖1-V‖*‖1-W‖*‖M‖)+‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*M) (q*(1-V*W))
    _ ≤ ((E+A)*2*(1+A)*388+A*(1+A))*2 := by
      have hbq : ‖B-q‖≤E+A := (norm_sub_le B q).trans (add_le_add hB hq)
      gcongr
    _ = _ := by ring

def selectedFirstBound (Q R : ℝ) : ℝ :=
  2*((Q^R+Q^(1/100:ℝ))*2*(1+Q^(1/100:ℝ))*388+Q^(1/100:ℝ)*(1+Q^(1/100:ℝ)))

lemma selectedFirstBound_nonneg (Q R : ℝ) (hQ : 0≤Q) : 0≤selectedFirstBound Q R := by
  unfold selectedFirstBound
  positivity

theorem continuedCompensatedLocal_first_bound (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (R : ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hxR : x.re≤R) (hw : -(1/100:ℝ)≤w.re)
    (hz : (17/50:ℝ)≤z.re) (hxw : 1≤x.re+w.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        selectedFirstBound P.val.absNorm R := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤P.val.absNorm := by linarith
  have hV := first_region_V_half _ hQ z hz
  have hD : ‖coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x‖≤1/2 :=
    (coordD_norm_le _ hQ0 _ _ x (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _)).trans
      (rpow_le_half _ _ hQ (by linarith))
  have hM : ‖continuedMarkedLocal η u P hs x w z‖≤388 := by
    rw [continuedMarkedLocal_eq_quotient η u P hs x w z
      (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV),div_eq_mul_inv,norm_mul]
    have hH := ramifiedCorrection_first_bound η u P hs hQ x w z hx hw hz hxw
    have hn : ‖ramifiedCorrection η u P hs x w z-1‖≤194 := by
      have h := norm_sub_le (ramifiedCorrection η u P hs x w z) (1:ℂ)
      rw [norm_one] at h
      linarith
    exact (mul_le_mul hn (ProbeLocal.inv_one_sub_norm_le_two _ hV) (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have hW : ‖coordW P.val.absNorm (idealRowHom u.val P.val) w‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) :=
    (coordW_norm_le _ hQ0 _ w (idealRowHom_norm u.val _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hq : ‖(P.val.absNorm:ℂ)^(-w)‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) := by
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hB : ‖star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x‖≤(P.val.absNorm:ℝ)^R := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)).trans
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 hxR
  exact compensatedReplacement_crude _ _ _ _ _ _ _ _ (by positivity) (by positivity)
    (hV.trans (by norm_num)) hW hD hM hB hq

end SevenEighths.ProbeHighRowFamily

end

end OAI
