import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaSupplement

namespace OAI

/-! The alternative (b/d) expression for the actual cubic Kubota
multiplier on the principal congruence group. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrincipalGroup_offDiagonal (g : cubicThetaPrincipalGroup) :
    (3:Eisenstein) ∣ g.val 0 1 ∧ (3:Eisenstein) ∣ g.val 1 0 := by
  have hm : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein))) g.val = 1 :=
    g.property
  constructor
  · have he := congrArg (fun h : SL(2,Residues (3:Eisenstein)) => h 0 1) hm
    change Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 0 1) = 0 at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)
  · have he := congrArg (fun h : SL(2,Residues (3:Eisenstein)) => h 1 0) hm
    change Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 1 0) = 0 at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)

lemma cubicThetaPrincipalGroup_det (g : cubicThetaPrincipalGroup) :
    g.val 0 0*g.val 1 1-g.val 0 1*g.val 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using g.val.property

lemma cubicThetaKubota_column_switch (g : cubicThetaPrincipalGroup) :
    cubicSymbol (g.val 0 0) (g.val 1 0) = cubicSymbol (g.val 1 1) (g.val 0 1) := by
  obtain ⟨ha,hd⟩ := cubicThetaPrincipalGroup_diagonal_primary g
  have hdet := cubicThetaPrincipalGroup_det g
  have hdiv : g.val 1 0 ∣ g.val 0 0*g.val 1 1-1 := by
    refine ⟨g.val 0 1,?_⟩
    linear_combination hdet
  have h9 : (9:Eisenstein) ∣ g.val 0 0*g.val 1 1-1 := by
    obtain ⟨x,hx⟩ := (cubicThetaPrincipalGroup_offDiagonal g).1
    obtain ⟨y,hy⟩ := (cubicThetaPrincipalGroup_offDiagonal g).2
    refine ⟨x*y,?_⟩
    calc
      _ = g.val 0 1*g.val 1 0 := by linear_combination hdet
      _ = _ := by rw [hx,hy]; ring
  have hprod := cubicThetaKubota_symbol_one (primary_mul ha hd) h9 hdiv
  rw [cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero hd)] at hprod
  have hquot : g.val 1 1 ∣ (g.val 0 1*g.val 1 0)-(-1) := by
    refine ⟨g.val 0 0,?_⟩
    linear_combination -hdet
  have hpair : cubicSymbol (g.val 1 1) (g.val 0 1)*cubicSymbol (g.val 1 1) (g.val 1 0) = 1 := by
    rw [←cubicSymbol_mul_upper hd,cubicSymbol_congr (residue_eq_of_dvd_sub hquot),
      cubicSymbol_neg hd,cubic_reciprocity hd primary_one,cubicSymbol_one_lower]
  have hn : cubicSymbol (g.val 1 1) (g.val 1 0) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hprod
    exact zero_ne_one hprod
  exact mul_right_cancel₀ hn (hprod.trans hpair.symm)

/-- DR v3 (5.5), derived from the supplementary laws and determinant. -/
theorem cubicThetaKubotaValue_alternative (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue g =
      if g.val 1 0 = 0 then 1 else cubicSymbol (g.val 1 1) (g.val 0 1) := by
  unfold cubicThetaKubotaValue
  split_ifs
  · rfl
  · exact cubicThetaKubota_column_switch g

end CubicFirstMoment

end

end OAI
