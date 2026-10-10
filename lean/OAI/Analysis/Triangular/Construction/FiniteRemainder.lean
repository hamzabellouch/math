import OAI.Analysis.Triangular.Construction.CurvatureAnalytic
import OAI.Analysis.Triangular.Taylor.CoefficientSpectral
import OAI.Analysis.Triangular.Signs.RemainderPre
import OAI.Analysis.Triangular.Signs.DeletedJets

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

def complexError (F : ℕ → ℝ → ℂ) (m v : ℝ) : ℂ := complexDeleted F m v-complexTaylor F m v
lemma complexError_add (F G : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexError (fun k s => F k s+G k s) m v=complexError F m v+complexError G m v := by
  simp only [complexError,complexDeleted_add,complexTaylor_add]
  ring
lemma complexError_mul (a : ℂ) (F : ℕ → ℝ → ℂ) (m v : ℝ) :
    complexError (fun k s => a*F k s) m v=a*complexError F m v := by
  simp only [complexError,complexDeleted_mul,complexTaylor_mul]
  ring
lemma complexError_sum {ι : Type*} (S : Finset ι) (F : ι → ℕ → ℝ → ℂ) (m v : ℝ) :
    complexError (fun k s => ∑ i∈S,F i k s) m v=∑ i∈S,complexError (F i) m v := by
  simp only [complexError,complexDeleted_sum,complexTaylor_sum,Finset.sum_sub_distrib]
lemma finiteWave_error (q br : Fin 2) (n : Fin 7) (j : Fin 31) {v : ℝ} (hv : |v|≤nearRadius n) :
    ‖complexError (fun k s => finiteWaveJet q br (frequency j) k s) (nearNode n) v‖≤
      remainderWave q br (nearNode n) (nearRadius n) (frequency j) := by
  have he : (fun (k : ℕ) (s : ℝ) => finiteWaveJet q br (frequency j) k s)=
      (fun (k : ℕ) (s : ℝ) => taylorAmplitude q br (frequency j)*(Complex.exp (taylorPhase q br (frequency j)*(s:ℂ))*(taylorPhase q br (frequency j))^k)) := by
    funext k s; simp only [finiteWaveJet,mul_assoc]
  rw [he,complexError_mul,complexError,complexDeleted_exp,complexTaylor_exp,norm_mul]
  have hb := Envelope.expDeleted_error (taylorPhase q br (frequency j)) (nearNode n) v (nearRadius n)
    (nearRadius_nonneg n) hv (remainder_ratio_lt_one q br n j)
  have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg (taylorAmplitude q br (frequency j)))
  convert hh using 1
  first | rfl | (simp only [remainderWave,curvatureWave,Complex.norm_exp,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]; ring)
lemma remainderWave_nonneg (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    0≤remainderWave q br (nearNode n) (nearRadius n) (frequency j) := by
  unfold remainderWave
  have hp := sub_pos.mpr (remainder_ratio_lt_one q br n j)
  have hy := nearRadius_nonneg n
  have hc := curvatureWave_nonneg q br (nearNode n) (frequency j)
  positivity
lemma rawRemainderColumn_nonneg (br : Fin 2) (n : Fin 7) (c : Fin 22) :
    0≤rawRemainderColumn br n c := Finset.sum_nonneg fun j _ => mul_nonneg (remainderWave_nonneg 1 br n j) (norm_nonneg _)
lemma rawRemainderConstant_nonneg (br : Fin 2) (n : Fin 7) :
    0≤rawRemainderConstant br n := Finset.sum_nonneg fun j _ => mul_nonneg (remainderWave_nonneg 0 br n j) (norm_nonneg _)
lemma inputJJet_zero_tail (C : ℝ) (a : TrigonometricCoefficients) (br : Fin 2) (k : ℕ) (s : ℂ) :
    inputJJet (coefficientInput C a 0) br k s=
      (C:ℂ)*(∑ j : Fin 31,fourierCoeff j*finiteWaveJet 0 br (frequency j) k s)+
      ∑ c : Fin 22,(a c:ℂ)*(∑ j : Fin 31,finiteColumn ⟨c.val,by omega⟩ j*finiteWaveJet 1 br (frequency j) k s) := by
  rw [inputJJet,tailSpectral_zero_coeff,finiteSpectral_coefficient_apply]
  simp only [_root_.smul_apply,smul_eq_mul,spectralPCLM_apply,spectralP,waveFunctionJet_apply]
lemma atom_remainder_bound (S : Fin 31 → ℂ) (q br : Fin 2) (n : Fin 7) {v : ℝ} (hv : |v|≤nearRadius n) :
    ‖complexError (fun k s => ∑ j : Fin 31,S j*finiteWaveJet q br (frequency j) k s) (nearNode n) v‖≤
      ∑ j : Fin 31,remainderWave q br (nearNode n) (nearRadius n) (frequency j)*‖S j‖ := by
  rw [complexError_sum]
  simp only [complexError_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (finiteWave_error q br n j hv) (norm_nonneg _)
lemma finite_input_error (C : ℝ) (a : TrigonometricCoefficients) (br : Fin 2) (n : Fin 7) {v M : ℝ}
    (hv : |v|≤nearRadius n) (hM : ∀ c : Fin 22,rawRemainderColumn br n c≤M) :
    ‖complexError (fun k s => inputJJet (coefficientInput C a 0) br k s) (nearNode n) v‖≤
      |C| *rawRemainderConstant br n+‖a‖*M := by
  simp only [inputJJet_zero_tail]
  rw [complexError_add,complexError_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (atom_remainder_bound fourierCoeff 0 br n hv) (abs_nonneg _)
  · rw [complexError_sum]
    simp only [complexError_mul]
    calc
      _ ≤ ∑ c : Fin 22,‖(a c:ℂ)*complexError (fun k s => ∑ j : Fin 31,finiteColumn ⟨c.val,by omega⟩ j*finiteWaveJet 1 br (frequency j) k s) (nearNode n) v‖ := norm_sum_le _ _
      _ ≤ ∑ c : Fin 22,|a c| *M := by
        apply Finset.sum_le_sum
        intro c _
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((atom_remainder_bound _ 1 br n hv).trans (hM c)) (abs_nonneg _)
      _ = ‖a‖*M := by rw [←Finset.sum_mul,AtomicTriangular.L1Kernel.l1_norm,tsum_fintype]
end AtomicTriangular.Construction
end

end OAI
