import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaMultiplication

namespace OAI

/-! The cubic Kubota character on the actual principal congruence group
Gamma_1(3) of DR v3 (5.4). Multiplicativity is derived from reciprocity,
including the noncoprime and zero-entry cases. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaKubotaValue_eq_symbol (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue g = cubicSymbol (g.val 0 0) (g.val 1 0) := by
  unfold cubicThetaKubotaValue
  split_ifs with hc
  · have hu := cubicThetaPrincipalGroup_column_coprime g
    rw [hc] at hu
    have ha := primary_unit_eq_one (isCoprime_zero_right.mp hu)
      (cubicThetaPrincipalGroup_diagonal_primary g).1
    rw [ha,cubicSymbol_one_lower]
  · rfl

theorem cubicThetaKubotaValue_mul (g h : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (g*h) = cubicThetaKubotaValue g*cubicThetaKubotaValue h := by
  have h9 : (9:Eisenstein) ∣ g.val 0 1*h.val 1 0 := by
    obtain ⟨x,hx⟩ := (cubicThetaPrincipalGroup_offDiagonal g).1
    obtain ⟨y,hy⟩ := (cubicThetaPrincipalGroup_offDiagonal h).2
    exact ⟨x*y,by rw [hx,hy]; ring⟩
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol,
    cubicThetaKubotaValue_eq_symbol]
  have hp := cubicThetaKubota_product (cubicThetaPrincipalGroup_diagonal_primary g).1
    (cubicThetaPrincipalGroup_diagonal_primary h).1 (cubicThetaPrincipalGroup_det g)
    h9 (cubicThetaPrincipalGroup_column_coprime h)
  simpa only [Subgroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two] using hp

/-- The published multiplier is a genuine multiplicative character. -/
def cubicThetaKubotaCharacter : cubicThetaPrincipalGroup →* ℂ where
  toFun := cubicThetaKubotaValue
  map_one' := by simp [cubicThetaKubotaValue]
  map_mul' := cubicThetaKubotaValue_mul

lemma cubicThetaKubotaCharacter_cube (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaCharacter g ^ 3 = 1 := by
  change cubicThetaKubotaValue g ^ 3 = 1
  rw [cubicThetaKubotaValue_eq_symbol]
  exact cubicSymbol_cube_of_isCoprime (cubicThetaPrincipalGroup_diagonal_primary g).1
    (g.val 1 0) (cubicThetaPrincipalGroup_column_coprime g)

end CubicFirstMoment

end

end OAI
