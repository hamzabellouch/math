import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCharacterAverage

namespace OAI

/-! The finite Gauss average equals the manuscript's actual raw completed
sum. Nonsquarefree terms vanish by the proved finite Gauss-sum identity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaPrimaryPairEquiv : CubicThetaPrimaryPair ≃
    {du : PrimaryArgument × PrimaryArgument // Squarefree (du.2:Eisenstein)} where
  toFun cd := ⟨(⟨cd.val.2,cd.property.2.1⟩,⟨cd.val.1,cd.property.1⟩),cd.property.2.2⟩
  invFun du := ⟨(du.val.2.val,du.val.1.val),du.val.2.property,du.val.1.property,du.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma metaplecticRawCompleted_primary_pairs (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (X : ℝ) :
    metaplecticRawCompleted r ℓ W X=
      ∑' cd : CubicThetaPrimaryPair,
        if IsCoprime r cd.val.2 then
          (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
            star (cubicSymbol r cd.val.1)*W (norm cd.val.1*norm cd.val.2^3/X)
        else 0 := by
  let f (du : PrimaryArgument × PrimaryArgument) : ℂ :=
    if IsCoprime (du.1:Eisenstein) r then
      (Real.sqrt (norm du.1):ℂ)*gauss du.2*theta ℓ (du.2*du.1^3)*
        star (cubicSymbol r du.2)*W (norm (du.2*du.1^3)/X)
    else 0
  have hs : Function.support f ⊆ {du | Squarefree (du.2:Eisenstein)} := by
    intro du hdu
    by_contra hns
    apply hdu
    dsimp only [f]
    rw [gauss_eq_zero_of_not_squarefree du.2.property hns]
    split_ifs <;> ring
  change (∑' du,f du)=_
  calc
    _ = ∑' du : {du : PrimaryArgument × PrimaryArgument // Squarefree (du.2:Eisenstein)},
        f du.val := (tsum_subtype_eq_of_support_subset hs).symm
    _ = ∑' cd : CubicThetaPrimaryPair,f (cubicThetaPrimaryPairEquiv cd).val :=
      (cubicThetaPrimaryPairEquiv.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro cd
      dsimp only [f,cubicThetaPrimaryPairEquiv,Equiv.coe_fn_mk]
      rw [isCoprime_comm,norm_mul_eq,eisenstein_norm_pow]

theorem cubicThetaPrimaryGaussSum_average_raw {r : Eisenstein}
    (hr : primary r) (hs : Squarefree r) [Fintype (Residues r)]
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) {X : ℝ} (hX : 0<X) :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      cubicThetaPrimaryGaussSum r (residueRepresentative r u) ℓ W X)=
    (Real.sqrt (norm r):ℂ)*gauss r*metaplecticRawCompleted r ℓ W X := by
  rw [cubicThetaPrimaryGaussSum_average hr hs ℓ W hW hX,metaplecticRawCompleted_primary_pairs]

/-- Exact finite additive detection of the raw completed cubic Gauss sum,
with the angular lambda factor and the scale 27 both retained. -/
theorem cubicThetaSelectedSmoothSum_average_raw {r : Eisenstein}
    (hr : primary r) (hs : Squarefree r) [Fintype (Residues r)]
    (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W) {X : ℝ} (hX : 0<X) :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      cubicThetaSelectedSmoothSum ℓ
        ((traceLambda^3*(residueRepresentative r u:ℂ))/(r:ℂ)) W (X/27))=
    (((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r)*metaplecticRawCompleted r ℓ W X := by
  simp_rw [cubicThetaSelectedSmoothSum_rational]
  calc
    _ = (((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE)*
        ∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
          cubicThetaPrimaryGaussSum r (residueRepresentative r u) ℓ W X := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := by rw [cubicThetaPrimaryGaussSum_average_raw hr hs ℓ W hW hX]; ring

end CubicFirstMoment

end

end OAI
