import OAI.Analysis.Triangular.Construction.SpectralJetBridge

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

def tailColumnSpectral (p : TailNode × Fin 2) : C(Spectrum,ℂ) →L[ℂ] ℂ :=
  if p.2.val=0 then spectralCCLM p.1.val else spectralDCLM p.1.val
lemma tailColumnSpectral_norm (p : TailNode × Fin 2) : ‖tailColumnSpectral p‖≤119 := by
  unfold tailColumnSpectral
  split_ifs
  · exact (spectralCCLM_norm _).trans cVariation_lt.le
  · exact (spectralDCLM_norm _).trans dVariation_lt.le
lemma summable_l1_complex_smul {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedSpace ℂ E] (w : ℓ¹(ι,ℝ)) (T : ι → E) (M : ℝ) (hM : ∀ i, ‖T i‖≤M) :
    Summable (fun i => (w i:ℂ) • T i) := by
  apply Summable.of_norm_bounded ((l1_summable w).mul_right M)
  intro i
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hM i) (abs_nonneg _)
lemma summable_tail_columns (w : TailCoefficients) :
    Summable (fun p => (w p:ℂ) • tailColumnSpectral p) := by
  exact summable_l1_complex_smul w tailColumnSpectral 119 tailColumnSpectral_norm
lemma tsum_prod_fin_two {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (g : ι × Fin 2 → E) (hg : Summable g) :
    (∑' p, g p)=∑' i, (g (i,0)+g (i,1)) := by
  rw [hg.tsum_prod]
  simp only [tsum_fintype,Fin.sum_univ_two]
lemma tailSpectral_product (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients) :
    tailSpectral (coefficientInput C a w)= (C:ℂ) • spectralPCLM+
      ∑' p : TailNode × Fin 2,(w p:ℂ) • tailColumnSpectral p := by
  have he := tsum_prod_fin_two (fun p => (w p:ℂ) • tailColumnSpectral p) (summable_tail_columns w)
  rw [he,tailSpectral_coefficient]
  rfl
lemma summable_tail_columns_apply (w : TailCoefficients) (f : C(Spectrum,ℂ)) :
    Summable (fun p => (w p:ℂ)*tailColumnSpectral p f) := by
  simpa only [ContinuousLinearMap.apply_apply,smul_apply,smul_eq_mul] using
    ((ContinuousLinearMap.apply ℂ ℂ f).summable (summable_tail_columns w))
lemma tailSpectral_product_apply (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (f : C(Spectrum,ℂ)) :
    tailSpectral (coefficientInput C a w) f=(C:ℂ)*spectralP f+
      ∑' p : TailNode × Fin 2,(w p:ℂ)*tailColumnSpectral p f := by
  rw [tailSpectral_product,add_apply,smul_apply,smul_eq_mul,spectralPCLM_apply]
  congr 1
  exact (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_tail_columns w)
lemma tailColumnSpectral_jet (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) (p : TailNode × Fin 2) :
    (tailColumnSpectral p (jetFunction q v m d)).re=tailJet (damping q) v m p.1.val.val p.2 d := by
  unfold tailColumnSpectral tailJet tailJetVector
  split_ifs with hc
  · rw [spectralCCLM_apply,spectralC_jetFunction]
    rfl
  · rw [spectralDCLM_apply,spectralD_jetFunction]
    rfl
lemma tailSpectral_jet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (q : Fin 2) (v : ℝ) (m : ℤ) (d : Fin 2) :
    (tailSpectral (coefficientInput C a w) (jetFunction q v m d)).re=
      C*jet (damping q) v m d (finiteColumn 22)+
      ∑' p : TailNode × Fin 2,w p*tailJet (damping q) v m p.1.val.val p.2 d := by
  rw [tailSpectral_product_apply,add_re,re_tsum (summable_tail_columns_apply _ _)]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,spectralP_jet,tailColumnSpectral_jet]
lemma negativeJet_add (v : ℝ) (n : ℤ) (d : Fin 2) (a b c e : ℂ) :
    negativeJet v n d (a+c) (b+e)=negativeJet v n d a b+negativeJet v n d c e := by
  unfold negativeJet
  split_ifs <;> ring
lemma inputJJet_negative (a : InputCoefficients) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (inputJJet a 1 0 n) (inputJJet a 1 1 n)=
      tailSpectral a (jetFunction 0 v n d)+finiteSpectral a (jetFunction 1 v n d) := by
  unfold inputJJet
  rw [negativeJet_add,negativeJet_linear,negativeJet_linear]
lemma inputJJet_negative_coefficient (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (inputJJet (coefficientInput C a w) 1 0 n)
      (inputJJet (coefficientInput C a w) 1 1 n)).re=
      C*jet h v n d (finiteColumn 22)+
      (∑' p : TailNode × Fin 2,w p*tailJet h v n p.1.val.val p.2 d)+
      ∑ c : Fin 22,a c*jet H v n d (finiteColumn ⟨c.val,by omega⟩) := by
  rw [inputJJet_negative,add_re,tailSpectral_jet,finiteSpectral_jet]
  rfl
end AtomicTriangular.Construction
end

end OAI
