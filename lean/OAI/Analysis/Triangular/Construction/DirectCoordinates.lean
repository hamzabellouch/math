import OAI.Analysis.Triangular.Construction.NormalizedJets
import OAI.Analysis.Triangular.Construction.DirectWaveJets

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
lemma negativeJet_re (v : ℝ) (n : ℤ) (d : Fin 2) (a b : ℂ) :
    (negativeJet v n d a b).re=
      Real.exp (Real.pi*(v-h)*n)/(Q n)*
        (if d.val=0 then -a.re else (D n-Real.pi*(v-h))*a.re-b.re) := by
  have he : exp (Real.pi*(v-h)*(n:ℂ))=(Real.exp (Real.pi*(v-h)*n):ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; rfl
  unfold negativeJet
  rw [he,←ofReal_inv]
  split_ifs <;> simp only [mul_re,mul_im,ofReal_re,ofReal_im,neg_re,sub_re,sub_im,
    zero_mul,mul_zero,sub_zero,add_zero]
  all_goals ring
lemma damped_wave_re (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (n : ℤ) :
    (T (waveFunctionJet q 0 0 n)).re=Real.exp (-Real.pi*(damping q-h)*n)*(T (waveFunctionJet 0 0 0 n)).re ∧
    (T (waveFunctionJet q 0 1 n)).re=Real.exp (-Real.pi*(damping q-h)*n)*
      ((T (waveFunctionJet 0 0 1 n)).re-Real.pi*(damping q-h)*(T (waveFunctionJet 0 0 0 n)).re) := by
  have he : exp (-(Real.pi:ℂ)*(damping q-h)*(n:ℂ))=(Real.exp (-Real.pi*(damping q-h)*n):ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; rfl
  constructor
  · rw [waveFunctionJet_direct_zero,map_smul,←waveFunctionJet_zero_phase,he]
    simp only [smul_eq_mul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  · rw [waveFunctionJet_direct_one,map_smul,map_sub,map_smul,←waveFunctionJet_zero_phase,he]
    simp only [smul_eq_mul,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,sub_re,mul_im,sub_im,mul_zero,add_zero]
lemma negativeJet_direct_re (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (T (waveFunctionJet q 0 0 n)) (T (waveFunctionJet q 0 1 n))).re=
      Real.exp (Real.pi*(v-damping q)*n)/(Q n)*
        (if d.val=0 then -(T (waveFunctionJet 0 0 0 n)).re else
          (D n-Real.pi*(v-damping q))*(T (waveFunctionJet 0 0 0 n)).re-(T (waveFunctionJet 0 0 1 n)).re) := by
  rw [negativeJet_re,(damped_wave_re T q n).1,(damped_wave_re T q n).2]
  have he : Real.exp (Real.pi*(v-h)*n)*Real.exp (-Real.pi*(damping q-h)*n)=
      Real.exp (Real.pi*(v-damping q)*n) := by rw [←Real.exp_add]; congr 1; ring
  split_ifs
  · linear_combination (-(T (waveFunctionJet 0 0 0 n)).re/(Q n))*he
  · linear_combination (((D n-Real.pi*(v-damping q))*(T (waveFunctionJet 0 0 0 n)).re-(T (waveFunctionJet 0 0 1 n)).re)/(Q n))*he

def directJetFunction (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) : C(Spectrum,ℂ) :=
  (exp (Real.pi*(v-h)*(n:ℂ))*(Q n:ℂ)⁻¹) •
    (if d.val=0 then -waveFunctionJet q 0 0 n else
      ((D n:ℂ)-Real.pi*(v-h)) • waveFunctionJet q 0 0 n-waveFunctionJet q 0 1 n)
lemma negativeJet_direct_linear (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (T (waveFunctionJet q 0 0 n)) (T (waveFunctionJet q 0 1 n))=
      T (directJetFunction q v n d) := by
  unfold directJetFunction negativeJet
  split_ifs <;> simp only [map_smul,map_neg,map_sub,smul_eq_mul]
lemma Q_node_ne (n : Node) : Q n.val≠0 :=
  (lt_trans (by norm_num) (FiniteCertificate.Q_node_bounds n.val n.property.2).1).ne'
lemma spectralP_directJet (q : Fin 2) (v : ℝ) (n : Node) (d : Fin 2) :
    (spectralPCLM (directJetFunction q v n.val d)).re=0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralP_direct _).1,(spectralP_direct _).2,P_node,deriv_P_node]
  split_ifs <;> simp
lemma spectralC_directJet (n m : Node) (d : Fin 2) :
    (spectralCCLM m (directJetFunction 0 h n.val d)).re=
      if n.val=m.val ∧ d.val=0 then -1 else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralC_direct m _).1,(spectralC_direct m _).2]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,Real.exp_zero,sub_zero]
  by_cases hm : n=m
  · subst m
    rw [cBasis_at_node,cBasis_deriv_re]
    by_cases hd : d.val=0
    · simp only [hd,↓reduceIte,and_self]
      field_simp [Q_node_ne n]
    · simp only [hd,↓reduceIte,and_false]
      ring
  · have hmn : n.val≠m.val := fun he => hm (Subtype.ext he)
    rw [cBasis_other_node hmn,deriv_cBasis_other_node hmn]
    simp [hmn]
lemma spectralD_directJet (n m : Node) (d : Fin 2) :
    (spectralDCLM m (directJetFunction 0 h n.val d)).re=
      if n.val=m.val ∧ d.val=1 then -1 else 0 := by
  rw [←negativeJet_direct_linear,negativeJet_direct_re,(spectralD_direct m _).1,(spectralD_direct m _).2]
  simp only [damping,Fin.val_zero,↓reduceIte,sub_self,mul_zero,zero_mul,Real.exp_zero,sub_zero]
  by_cases hm : n=m
  · subst m
    have hd0 : dBasis n n.val=0 := by rw [dBasis_cBasis]; simp
    rw [hd0,deriv_dBasis_at_node,cBasis_at_node]
    fin_cases d <;> simp only [Nat.one_ne_zero,↓reduceIte,zero_re,mul_zero,zero_sub,neg_zero,mul_zero,and_true]
    · norm_num
    · field_simp [Q_node_ne n]
  · have hmn : n.val≠m.val := fun he => hm (Subtype.ext he)
    rw [dBasis_other_node hmn,deriv_dBasis_other_node hmn]
    simp [hmn]
end AtomicTriangular.Construction
end

end OAI
