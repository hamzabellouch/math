import OAI.NumberTheory.TwoPoint.Halasz.HalaszQuantitativeMeanValue

namespace OAI

/-! Numerical margins for the degree and shift-length choices in the
logarithmic exponential-sum application. -/
namespace TwoPointCorrelations

lemma halasz_low_height_degree_margin {lam : ℝ}
    (hlo : 49/100≤lam) (hhi : lam≤9/10) :
    (1:ℝ)/16+(6:ℝ)^2/1024≤min (1/3:ℝ) (min (1-lam) (lam-1/3)) := by
  apply le_min
  · norm_num
  · apply le_min <;> linarith

lemma halasz_medium_degree_margin {lam : ℝ} (hlo : 9/10≤lam) (hhi : lam≤48) :
    (1:ℝ)/32≤lam/2-1/3-(3*lam+6)^2/1024 := by
  have hprod : 0≤(lam-9/10)*(48-lam) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma halasz_small_degree_margin {lam : ℝ} (hlo : 19/20≤lam) (hhi : lam≤48) :
    (1:ℝ)/16≤lam/2-1/3-(3*lam+6)^2/1024 := by
  have hprod : 0≤(lam-19/20)*(48-lam) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma halasz_small_degree_saving {lam k j : ℝ}
    (hlo : 19/20≤lam) (hhi : lam≤48) (hk0 : 0≤k) (hk : k≤3*lam+6)
    (hjlo : 3*lam/2≤j) (hjhi : j≤3*lam/2+1) :
    (1:ℝ)/16+k^2/1024≤min (j/3) (min (j-lam) (lam-j/3)) := by
  have hm := halasz_small_degree_margin hlo hhi
  have hk2 : k^2≤(3*lam+6)^2 := by nlinarith
  apply le_min
  · nlinarith
  · apply le_min <;> nlinarith

lemma halasz_large_degree_margin {m : ℝ} (hm : 8≤m) :
    m^2/4≤(2*m+1)*(m-6)-(12*m)^2/1024 := by
  have hh : 0≤m*(m-8) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma halasz_large_degree_saving {m lam j : ℝ} (hm : 8≤m)
    (hlamlo : 6*m-6≤lam) (hlamhi : lam≤6*m)
    (hjlo : 8*m≤j) (hjhi : j≤10*m) :
    m-6≤min (j/4) (min (j-lam) (lam-j/2)) := by
  apply le_min
  · linarith
  · apply le_min <;> linarith

lemma halasz_small_taylor_exponent {lam k : ℝ} (hk : 3*lam+3≤k) :
    lam-(k+1)/3≤-(4/3:ℝ) := by linarith

lemma halasz_large_taylor_exponent {lam m : ℝ} (hlam : lam≤6*m) :
    lam-(12*m+1)/2≤-(1/2:ℝ) := by linarith

end TwoPointCorrelations

end OAI
