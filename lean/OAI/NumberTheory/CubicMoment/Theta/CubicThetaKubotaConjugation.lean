import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaReal

namespace OAI

/-! Invariance of the cubic multiplier under the two integral modular
generators, as needed to extend it to the group of DR v3 Section 5.1. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicSymbol_primary_lower_add {a c : Eisenstein}
    (ha : primary a) (hac : primary (a+c)) :
    cubicSymbol (a+c) c = cubicSymbol a c := by
  have hc : a+c ∣ c-(-a) := ⟨1,by ring⟩
  have he : a ∣ a+c-c := ⟨1,by ring⟩
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub hc),cubicSymbol_neg hac,
    cubic_reciprocity hac ha,cubicSymbol_congr (residue_eq_of_dvd_sub he)]

def cubicThetaKubotaConjugate (u : SL(2,Eisenstein)) (g : cubicThetaPrincipalGroup) :
    cubicThetaPrincipalGroup :=
  ⟨u*g.val*u⁻¹,by
    have hg : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein))) g.val = 1 :=
      g.property
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein)))
      (u*g.val*u⁻¹) = 1
    rw [map_mul,map_mul,map_inv,hg,mul_one,mul_inv_cancel]⟩

def cubicThetaModularS : SL(2,Eisenstein) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

def cubicThetaModularT : SL(2,Eisenstein) :=
  ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩

lemma cubicThetaKubotaConjugate_S_entries (g : cubicThetaPrincipalGroup) :
    (cubicThetaKubotaConjugate cubicThetaModularS g).val 0 0 = g.val 1 1 ∧
      (cubicThetaKubotaConjugate cubicThetaModularS g).val 1 0 = -g.val 0 1 := by
  change ((!![0,-1;1,0] * (g.val:Matrix (Fin 2) (Fin 2) Eisenstein)) *
      Matrix.adjugate !![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein) 0 0 = g.val 1 1 ∧
    ((!![0,-1;1,0] * (g.val:Matrix (Fin 2) (Fin 2) Eisenstein)) *
      Matrix.adjugate !![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein) 1 0 = -g.val 0 1
  constructor <;> simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma cubicThetaKubotaConjugate_T_entries (g : cubicThetaPrincipalGroup) :
    (cubicThetaKubotaConjugate cubicThetaModularT g).val 0 0 = g.val 0 0+g.val 1 0 ∧
      (cubicThetaKubotaConjugate cubicThetaModularT g).val 1 0 = g.val 1 0 := by
  change ((!![1,1;0,1] * (g.val:Matrix (Fin 2) (Fin 2) Eisenstein)) *
      Matrix.adjugate !![1,1;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein) 0 0 = g.val 0 0+g.val 1 0 ∧
    ((!![1,1;0,1] * (g.val:Matrix (Fin 2) (Fin 2) Eisenstein)) *
      Matrix.adjugate !![1,1;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein) 1 0 = g.val 1 0
  constructor <;> simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem cubicThetaKubotaValue_conjugate_S (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (cubicThetaKubotaConjugate cubicThetaModularS g) =
      cubicThetaKubotaValue g := by
  obtain ⟨ha,hc⟩ := cubicThetaKubotaConjugate_S_entries g
  rw [cubicThetaKubotaValue_eq_symbol,ha,hc,
    cubicSymbol_neg (cubicThetaPrincipalGroup_diagonal_primary g).2,
    ←cubicThetaKubota_column_switch,cubicThetaKubotaValue_eq_symbol]

theorem cubicThetaKubotaValue_conjugate_T (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (cubicThetaKubotaConjugate cubicThetaModularT g) =
      cubicThetaKubotaValue g := by
  obtain ⟨ha,hc⟩ := cubicThetaKubotaConjugate_T_entries g
  have ha' := (cubicThetaPrincipalGroup_diagonal_primary
    (cubicThetaKubotaConjugate cubicThetaModularT g)).1
  rw [ha] at ha'
  rw [cubicThetaKubotaValue_eq_symbol,ha,hc,cubicThetaKubotaValue_eq_symbol]
  exact cubicSymbol_primary_lower_add (cubicThetaPrincipalGroup_diagonal_primary g).1 ha'

end CubicFirstMoment

end

end OAI
