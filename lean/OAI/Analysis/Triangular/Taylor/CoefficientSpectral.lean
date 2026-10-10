import OAI.Analysis.Triangular.Construction.ActualInput
import OAI.Analysis.Triangular.Taylor.WaveFunction
import OAI.Analysis.Triangular.Taylor.VariationBound

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma finiteColumn_even (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val,by omega⟩ l=cCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val<22 by omega,↓reduceDIte,
    show 2*j.val%2=0 by omega,↓reduceIte]
  congr 2
  omega
lemma finiteColumn_odd (j : Fin 11) (l : Fin 31) :
    finiteColumn ⟨2*j.val+1,by omega⟩ l=dCoefficient ⟨j.val,by omega⟩ l := by
  simp only [finiteColumn,show 2*j.val+1<22 by omega,↓reduceDIte,
    show ¬((2*j.val+1)%2=0) by omega,↓reduceIte]
  congr 2
  omega
lemma sum_fin22_pairs {M : Type*} [AddCommMonoid M] (g : Fin 22 → M) :
    (∑ c : Fin 22, g c)=∑ j : Fin 11, (g ⟨2*j.val,by omega⟩+g ⟨2*j.val+1,by omega⟩) := by
  have hh := (finProdFinEquiv (m:=11) (n:=2)).sum_comp g
  rw [Fintype.sum_prod_type] at hh
  simp only [Fin.sum_univ_two] at hh
  convert hh.symm using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2 <;> apply Fin.ext <;> simp [finProdFinEquiv, mul_comm, add_comm]
lemma finiteSpectral_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    finiteSpectral (coefficientInput C a w)=∑ c : Fin 22,
      (a c:ℂ) • atomSpectral (finiteColumn ⟨c.val,by omega⟩) := by
  rw [sum_fin22_pairs]
  simp only [finiteSpectral,coefficientInput]
  apply Finset.sum_congr rfl
  intro j _
  congr 2 <;> congr 1 <;> funext l
  · exact (finiteColumn_even j l).symm
  · exact (finiteColumn_odd j l).symm
lemma finiteSpectral_coefficient_apply (C : ℝ) (a : TrigonometricCoefficients)
    (w : TailCoefficients) (f : C(Spectrum,ℂ)) :
    finiteSpectral (coefficientInput C a w) f=∑ c : Fin 22,
      (a c:ℂ)*(∑ j : Fin 31, finiteColumn ⟨c.val,by omega⟩ j*f ⟨frequency j,frequency_mem j⟩) := by
  rw [finiteSpectral_coefficient]
  simp only [sum_apply,smul_apply,smul_eq_mul,atomSpectral_apply]
lemma tailSpectral_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput C a w)= (C:ℂ) • spectralPCLM+
      ∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val) := rfl
lemma tailSpectral_zero_coeff (C : ℝ) (a : TrigonometricCoefficients) :
    tailSpectral (coefficientInput C a 0)=(C:ℂ) • spectralPCLM := by
  ext f
  simp [tailSpectral_apply,coefficientInput,spectralPCLM_apply]
lemma complex_smul_clm_bound (r : ℝ) (T : C(Spectrum,ℂ) →L[ℂ] ℂ) :
    ‖(r:ℂ) • T‖ ≤ |r| * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg r) (norm_nonneg T))
  intro f
  change ‖(r:ℂ) * T f‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
  exact mul_le_mul_of_nonneg_left (T.le_opNorm f) (abs_nonneg r)
lemma tail_pair_norm119 (n : Node) (u v : ℝ) :
    ‖(u:ℂ) • spectralCCLM n+(v:ℂ) • spectralDCLM n‖ ≤ 119*(|u|+|v|) := by
  have h0 := (spectralCCLM_norm n).trans cVariation_lt.le
  have h1 := (spectralDCLM_norm n).trans dVariation_lt.le
  have hsum := norm_add_le ((u:ℂ) • spectralCCLM n) ((v:ℂ) • spectralDCLM n)
  have hsm := add_le_add (complex_smul_clm_bound u (spectralCCLM n))
    (complex_smul_clm_bound v (spectralDCLM n))
  have hh : ‖(u:ℂ) • spectralCCLM n+(v:ℂ) • spectralDCLM n‖ ≤
      |u| * ‖spectralCCLM n‖+|v| * ‖spectralDCLM n‖ := by
    exact hsum.trans hsm
  nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg u),mul_le_mul_of_nonneg_left h1 (abs_nonneg v)]
lemma norm_series_bound {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (g : ι → E) (v : ι → ℝ) (hv : Summable v) (M : ℝ)
    (hb : ∀ i, ‖g i‖≤M*v i) : ‖∑' i, g i‖≤M*∑' i,v i := by
  have hs : Summable (fun i => ‖g i‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hv.mul_left M)
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hb (hv.mul_left M)).trans_eq (tsum_mul_left))
lemma tailSeries_norm (w : TailCoefficients) :
    ‖∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val)‖ ≤ 119*‖w‖ := by
  have hh := norm_series_bound (fun n : TailNode => (w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val)
    (fun n => |w (n,0)|+|w (n,1)|) (tail_pairs_summable w) 119
    (fun n => tail_pair_norm119 n.val (w (n,0)) (w (n,1)))
  rw [tail_pairs_norm] at hh
  exact hh
lemma tailSpectral_zero_constant (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput 0 a w)=
      ∑' n : TailNode, ((w (n,0):ℂ) • spectralCCLM n.val+(w (n,1):ℂ) • spectralDCLM n.val) := by
  have hz : (0:ℂ) • spectralPCLM=(0:C(Spectrum,ℂ) →L[ℂ] ℂ) := by
    ext f
    change (0:ℂ)*_=0
    exact zero_mul _
  change (0:ℂ) • spectralPCLM+_= _
  rw [hz,zero_add]
  rfl
lemma tailSpectral_zero_constant_norm (a : TrigonometricCoefficients) (w : TailCoefficients) :
    ‖tailSpectral (coefficientInput 0 a w)‖ ≤ 119*‖w‖ := by
  rw [tailSpectral_zero_constant]
  exact tailSeries_norm w
lemma finiteSpectral_wave_bound (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (s : ℝ) {M : ℝ} (hb : ∀ c : Fin 22, rawCurvatureColumn br s c ≤ M) :
    ‖finiteSpectral (coefficientInput C a w) (waveFunctionJet 1 br 2 s)‖ ≤ ‖a‖*M := by
  rw [finiteSpectral_coefficient_apply]
  calc
    _ ≤ ∑ c : Fin 22, ‖(a c:ℂ)*(∑ j : Fin 31, finiteColumn ⟨c.val,by omega⟩ j * waveFunctionJet 1 br 2 s ⟨frequency j,frequency_mem j⟩)‖ := norm_sum_le _ _
    _ ≤ ∑ c : Fin 22, |a c| * rawCurvatureColumn br s c := by
      apply Finset.sum_le_sum
      intro c _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,waveFunctionJet_apply,norm_finiteWaveJet_two]
      exact le_of_eq (mul_comm _ _)
    _ ≤ ∑ c : Fin 22, |a c| * M := Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hb c) (abs_nonneg _)
    _ = _ := by rw [←Finset.sum_mul,l1_norm,tsum_fintype]
end AtomicTriangular.Construction
end

end OAI
