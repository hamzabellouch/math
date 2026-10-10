import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspPeriodicity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNineCusp
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueLocalCoefficient

namespace OAI

/-! The actual radial constant in the adapted primary cusp. The arithmetic
base scalar is retained, including after finite character averaging. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaActualCuspConstant_adapted (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0) (j : Fin 3) :
    cubicThetaActualCuspConstant (cubicThetaProjectedCuspType g j)=
      if j=0 then cubicThetaSeriesConstant else 0 := by
  have hcong := cubicThetaProjectedCuspType_congr g hc ha j
  have hj : (3:ℤ)∣cubicThetaProjectedCuspType g j ↔ j=0 := by
    constructor
    · intro hd
      have h := dvd_sub hd hcong
      have hdj : (3:ℤ)∣(j.val:ℤ) := by simpa only [sub_sub_cancel] using h
      apply Fin.ext
      have hjb := j.isLt
      obtain ⟨k,hk⟩ := hdj
      dsimp only [Fin.val_zero]
      omega
    · intro hj
      subst j
      simpa only [Fin.val_zero,Nat.cast_zero,sub_zero] using hcong
  simp only [cubicThetaActualCuspConstant,hj]

lemma cubicThetaNineGaussMatrix_constant (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaProjectedConstant (cubicThetaNineGaussMatrix r hr u hu)
      (cubicThetaNineGaussMatrix_primary r hr u hu)=
      star (cubicSymbol r u)*star cubicThetaSeriesConstant/3 := by
  have ha : (3:Eisenstein)∣cubicThetaNineGaussMatrix r hr u hu 0 0 := by
    rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1]
    refine ⟨-lambdaE*u,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  unfold cubicThetaProjectedConstant
  simp_rw [cubicThetaNineGaussMatrix_multiplier,
    cubicThetaActualCuspConstant_adapted _ (cubicThetaNineGaussMatrix_primary r hr u hu) ha]
  simp [Fin.sum_univ_three]

lemma cubicThetaResidueCuspMatrix_weighted_constant (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicSymbol r u*cubicThetaProjectedConstant (cubicThetaResidueCuspMatrix r hr u)
      (cubicThetaResidueCuspPrimary r hr u)=star cubicThetaSeriesConstant/3 := by
  have h := cubicThetaNineGaussMatrix_constant r hr u hu
  have hg := cubicThetaResidueCuspMatrix_of_coprime r hr u hu
  have hc : cubicThetaProjectedConstant (cubicThetaResidueCuspMatrix r hr u)
      (cubicThetaResidueCuspPrimary r hr u)=
      star (cubicSymbol r u)*star cubicThetaSeriesConstant/3 := by
    simpa only [hg] using h
  rw [hc]
  have hχ : cubicSymbol r u*star (cubicSymbol r u)=1 := by
    rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hr hu]
    norm_num
  calc
    _ = (cubicSymbol r u*star (cubicSymbol r u))*star cubicThetaSeriesConstant/3 := by ring
    _ = _ := by rw [hχ,one_mul]

def cubicThetaResidueConstant (r : Eisenstein) (hr : primary r) [Fintype (Residues r)] : ℂ :=
  ∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
    cubicThetaProjectedConstant (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))
      (cubicThetaResidueCuspPrimary r hr (residueRepresentative r u))

lemma cubicThetaResidueConstant_units (r : Eisenstein) (hr : primary r)
    [Fintype (Residues r)] :
    cubicThetaResidueConstant r hr=
      (Nat.card (Residues r)ˣ:ℂ)*(star cubicThetaSeriesConstant/3) := by
  classical
  let F : Residues r→ℂ := fun u => cubicSymbol r (residueRepresentative r u)*
    cubicThetaProjectedConstant (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))
      (cubicThetaResidueCuspPrimary r hr (residueRepresentative r u))
  have hz (u : Residues r) (hu : ¬IsUnit u) : F u=0 := by
    have hn : ¬IsCoprime r (residueRepresentative r u) := by
      intro h
      exact hu (by simpa only [residueRepresentative_spec] using residue_isUnit_of_isCoprime h)
    dsimp only [F]
    rw [cubicSymbol_eq_zero_of_not_isCoprime hr hn,zero_mul]
  change (∑ u : Residues r,F u)=_
  rw [cubicTheta_sum_eq_units F hz]
  have he (u : (Residues r)ˣ) : F u=star cubicThetaSeriesConstant/3 :=
    cubicThetaResidueCuspMatrix_weighted_constant r hr _ (cubicThetaUnitRepresentative_coprime r u)
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card]

end CubicFirstMoment

end

end OAI
