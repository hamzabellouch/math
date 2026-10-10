import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralCancellation
import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma central_unramified_error_weights (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    let L := Q^(6*e)
    let E := unramifiedMarked Q A eta v x w z+coordD Q eta v x
    L^2*‖coordV Q z‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖coordD Q eta v x‖≤Q^(-(51/100:ℝ)) ∧
    L^2*‖E‖≤28*Q^(-(51/100:ℝ)) ∧
    L*‖star eta*(Q:ℂ)^x‖*‖E‖≤28*Q^(-(51/100:ℝ)) := by
  dsimp only
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:ℂ)^x
  let L : ℝ := Q^(6*e)
  have hL : 1≤L := Real.one_le_rpow hQ1 (by positivity)
  have hL0 : 0≤L := by positivity
  have hR := coordR_norm_le Q hQ0 A x z hA
  have hV := coordV_norm Q hQ0 z
  have hD := coordD_norm_le Q hQ0 eta v x heta hv
  have hK := coordK_norm_le Q hQ1 eta x w heta
  have hW : ‖W‖≤L := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hB : ‖B‖≤Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by rw [hx,hz];linarith))
  have hVh : ‖V‖≤1/2 := hV.le.trans (rpow_le_half Q _ hQ (by rw [hz];norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hE : ‖unramifiedMarked Q A eta v x w z+D‖≤24*L*‖R‖+4*‖K‖*‖V‖ := by
    have hh := unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    apply hh.trans
    nlinarith [mul_le_mul_of_nonneg_left (show 1+‖W‖≤2*L by linarith) (norm_nonneg R)]
  have weighted (k r : ℝ) (N : ℝ) (hN : N≤Q^r) (hexp : k+r≤-(51/100:ℝ)) :
      Q^k*N≤Q^(-(51/100:ℝ)) := by
    calc
      _ ≤ Q^k*Q^r := mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hQ0.le _)
      _ = Q^(k+r) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ1 hexp
  have hLR : L^3*‖R‖≤Q^(-(51/100:ℝ)) := by
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hR (by rw [hx,hz];linarith)
  have hLKV : L^2*(‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hkv : ‖K‖*‖V‖≤Q^(1-x.re-w.re-6*z.re) := by
      calc
        _ ≤ Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hkv (by rw [hx,hw,hz];linarith)
  have hLBR : L^2*(‖B‖*‖R‖)≤Q^(-(51/100:ℝ)) := by
    have hbr : ‖B‖*‖R‖≤Q^(4-5*x.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(4-6*x.re-6*z.re) := mul_le_mul hB hR (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hbr (by rw [hx,hz];linarith)
  have hLBKV : L*(‖B‖*‖K‖*‖V‖)≤Q^(-(51/100:ℝ)) := by
    have hbkv : ‖B‖*‖K‖*‖V‖≤Q^(1-w.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(1-x.re-w.re)*Q^(-6*z.re) := by
          gcongr
          exact hV.le
        _ = _ := by rw [←Real.rpow_add hQ0,←Real.rpow_add hQ0];congr 1;ring
    exact weighted _ _ _ hbkv (by rw [hw,hz];linarith)
  refine ⟨?_,?_,?_,?_⟩
  · change L^2*‖V‖≤_
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hV.le (by rw [hz];linarith)
  · change L^2*‖D‖≤_
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hD (by rw [hx];linarith)
  · have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg L)
    change L^2*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLR,hLKV]
  · have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hL0 (norm_nonneg B))
    change L*‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤_
    nlinarith [hLBR,hLBKV]

end SevenEighths.ProbeEuler
end

end OAI
