import OAI.Analysis.Triangular.Schwartz.SpectralCLM
import OAI.Analysis.Triangular.Envelope.EnvelopeSumsBase
import OAI.Analysis.Triangular.Envelope.EnvelopeNorms

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def varFreqBox (j : Fin 31) : RI := (RI.point (frequencyDistance j)).divNat 18
lemma varFreqBox_mem (j : Fin 31) : (varFreqBox j).Mem |frequency j| := by
  have hx := RI.mem_divNat (RI.mem_point (frequencyDistance j)) (by norm_num : 0<(18:ℕ))
  change ((RI.point (frequencyDistance j)).divNat 18).Mem _
  convert hx using 1
  fin_cases j <;> norm_num [frequencyDistance, frequency]
def cVariationBox : RI := ((RI.sum (fun j : Fin 31 => (columnNorm22 j).mul ((varFreqBox j).pow 2))).mul (piBox.pow 2)).divNat 2

lemma cVariationBox_mem : cVariationBox.Mem cVariation := by
  have hx := RI.mem_mul (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (fourierNorm_mem j) (RI.mem_pow (varFreqBox_mem j) 2))) (RI.mem_pow piBox_mem 2)
  have hy := RI.mem_divNat hx (by norm_num : 0<2)
  simpa only [cVariationBox,cVariation,coeffAbs,sq_abs,Nat.cast_ofNat] using hy
lemma cVariation_lt : cVariation < 119 := by
  have hx := ri_mem_lt cVariationBox_mem 119 1 (by norm_num) (by decide +kernel)
  simpa using hx
def dVariationBox : RI := (RI.sum (fun j : Fin 31 => (columnNorm22 j).mul ((varFreqBox j).pow 1))).mul (piBox.pow 1)

lemma dVariationBox_mem : dVariationBox.Mem dVariation := by
  have hx := RI.mem_mul (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (fourierNorm_mem j) (RI.mem_pow (varFreqBox_mem j) 1))) (RI.mem_pow piBox_mem 1)
  simpa only [dVariationBox,dVariation,coeffAbs,pow_one] using hx
lemma dVariation_lt : dVariation < 119 := by
  have hx := ri_mem_lt dVariationBox_mem 119 1 (by norm_num) (by decide +kernel)
  simpa using hx
end AtomicTriangular.FiniteCertificate
end

end OAI
