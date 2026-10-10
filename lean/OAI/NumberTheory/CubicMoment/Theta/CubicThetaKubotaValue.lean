import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmetic

namespace OAI

/-! The actual principal congruence group and pointwise cubic Kubota
multiplier of DR v3 (5.4). Multiplicativity and theta automorphy are not
assumed by these arithmetic definitions. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrincipalGroup : Subgroup SL(2,Eisenstein) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein)))).ker

lemma cubicThetaPrincipalGroup_diagonal_primary (g : cubicThetaPrincipalGroup) :
    primary (g.val 0 0) ∧ primary (g.val 1 1) := by
  have hm : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein))) g.val = 1 :=
    g.property
  constructor
  · have he := congrArg (fun h : SL(2,Residues (3:Eisenstein)) => h 0 0) hm
    change Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 0 0) = 1 at he
    have hz : Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 0 0-1) = 0 := by
      rw [map_sub,map_one,he,sub_self]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  · have he := congrArg (fun h : SL(2,Residues (3:Eisenstein)) => h 1 1) hm
    change Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 1 1) = 1 at he
    have hz : Ideal.Quotient.mk (modulus (3:Eisenstein)) (g.val 1 1-1) = 0 := by
      rw [map_sub,map_one,he,sub_self]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)

lemma cubicThetaPrincipalGroup_column_coprime (g : cubicThetaPrincipalGroup) :
    IsCoprime (g.val 0 0) (g.val 1 0) := by
  have hd : g.val 0 0*g.val 1 1-g.val 0 1*g.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.val.property
  refine ⟨g.val 1 1,-g.val 0 1,?_⟩
  linear_combination hd

/-- The cubic residue value in the original Kubota convention. -/
def cubicThetaKubotaValue (g : cubicThetaPrincipalGroup) : ℂ :=
  if g.val 1 0 = 0 then 1 else cubicSymbol (g.val 0 0) (g.val 1 0)

lemma cubicThetaKubotaValue_norm (g : cubicThetaPrincipalGroup) :
    ‖cubicThetaKubotaValue g‖ = 1 := by
  unfold cubicThetaKubotaValue
  split_ifs
  · simp
  · exact norm_cubicSymbol_of_isCoprime (cubicThetaPrincipalGroup_diagonal_primary g).1
      (cubicThetaPrincipalGroup_column_coprime g)

end CubicFirstMoment

end

end OAI
