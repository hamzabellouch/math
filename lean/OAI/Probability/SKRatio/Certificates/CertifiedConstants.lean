import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedInterpolation

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma sqrt_densityFactor_bound {j z t : ℝ} (hj : 0 < j) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (hexp : (z^2-j^2)/2 < 1)
    (harith : z/j/(1-(z^2-j^2)/2) ≤ t^2) : sqrt (densityFactor j z) ≤ t := by
  have hpos : 0 < 1-(z^2-j^2)/2 := by linarith only [hexp]
  have he : exp ((z^2-j^2)/2) ≤ 1/(1-(z^2-j^2)/2) := by
    have hh := one_div_le_one_div_of_le hpos (show 1-(z^2-j^2)/2 ≤ exp (-((z^2-j^2)/2)) by
      linarith only [add_one_le_exp (-((z^2-j^2)/2))])
    simpa only [exp_neg,one_div,inv_inv] using hh
  apply (sqrt_le_iff).mpr
  refine ⟨ht,?_⟩
  have hm := mul_le_mul_of_nonneg_left he (div_nonneg hz hj.le)
  unfold densityFactor
  exact hm.trans (by simpa only [mul_one_div] using harith)

def X0 : Enclosures where
  av := ⟨2777/3125,22291/25000⟩
  gv := ⟨110463/200000,111063/200000⟩
  mv := ⟨9979/125000,5177/62500⟩
  rv := ⟨0,33/2000⟩
  vs := ⟨0,13/100⟩
  gs := ⟨0,43/500⟩
  ms := ⟨0,239/1000⟩
  fs := ⟨0,333/500⟩

def X1 : Enclosures where
  av := ⟨214787/250000,215537/250000⟩
  gv := ⟨544267/1000000,547267/1000000⟩
  mv := ⟨94251/1000000,97251/1000000⟩
  rv := ⟨0,1/50⟩
  vs := ⟨0,157/1000⟩
  gs := ⟨0,19/200⟩
  ms := ⟨0,249/1000⟩
  fs := ⟨0,737/1000⟩

def X2 : Enclosures where
  av := ⟨207709/250000,208459/250000⟩
  gv := ⟨26771/50000,26921/50000⟩
  mv := ⟨21177/200000,21777/200000⟩
  rv := ⟨0,47/2000⟩
  vs := ⟨0,181/1000⟩
  gs := ⟨0,103/1000⟩
  ms := ⟨0,127/500⟩
  fs := ⟨0,397/500⟩

def X3 : Enclosures where
  av := ⟨405599/500000,407099/500000⟩
  gv := ⟨132171/250000,132921/250000⟩
  mv := ⟨7051/62500,14477/125000⟩
  rv := ⟨0,13/500⟩
  vs := ⟨0,49/250⟩
  gs := ⟨0,109/1000⟩
  ms := ⟨0,32/125⟩
  fs := ⟨0,207/250⟩

def X4 : Enclosures where
  av := ⟨397223/500000,398723/500000⟩
  gv := ⟨522571/1000000,525571/1000000⟩
  mv := ⟨118053/1000000,121053/1000000⟩
  rv := ⟨0,7/250⟩
  vs := ⟨0,209/1000⟩
  gs := ⟨0,23/200⟩
  ms := ⟨0,257/1000⟩
  fs := ⟨0,171/200⟩

lemma density0 : sqrt (densityFactor (7/20) (2/5)) ≤ 27/25 := by
  apply sqrt_densityFactor_bound <;> norm_num
lemma check0 : interpolationCheck (7/20) (2/5) (27/25) X0 X1 = true := by decide +kernel

lemma density1 : sqrt (densityFactor (2/5) (89/200)) ≤ 1067/1000 := by
  apply sqrt_densityFactor_bound <;> norm_num
lemma check1 : interpolationCheck (2/5) (89/200) (1067/1000) X1 X2 = true := by decide +kernel

lemma density2 : sqrt (densityFactor (89/200) (19/40)) ≤ 521/500 := by
  apply sqrt_densityFactor_bound <;> norm_num
lemma check2 : interpolationCheck (89/200) (19/40) (521/500) X2 X3 = true := by decide +kernel

lemma density3 : sqrt (densityFactor (19/40) (1/2)) ≤ 517/500 := by
  apply sqrt_densityFactor_bound <;> norm_num
lemma check3 : interpolationCheck (19/40) (1/2) (517/500) X3 X4 = true := by decide +kernel

end SKRatio.Certificate

end

end OAI
