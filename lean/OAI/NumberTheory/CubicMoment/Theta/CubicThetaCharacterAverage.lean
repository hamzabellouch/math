import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSelectedGaussSum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothPairSupport
import OAI.NumberTheory.CubicGram.MixedPoisson
import OAI.NumberTheory.CubicGram.CubeExtraction

namespace OAI

/-! The finite cubic-character average of the actual selected Gauss sum.
The zero extension removes every cube factor sharing a prime with the level. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaPrimary_character_sum {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (c d : Eisenstein) :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      additivePhase r (c*d^3*residueRepresentative r u))=
    (Real.sqrt (norm r):ℂ)*gauss r*
      (if IsCoprime r d then star (cubicSymbol r c) else 0) := by
  have hN : (Real.sqrt (norm r):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hr))).ne'
  calc
    _ = (Real.sqrt (norm r):ℂ)*frequencyGauss r (c*d^3) := by
      rw [frequencyGauss,tsum_fintype,←mul_assoc,mul_inv_cancel₀ hN,one_mul]
    _ = _ := by
      rw [frequencyGauss_squarefree hr hs,cubicSymbol_mul_upper hr,cubicSymbol_pow_upper hr]
      by_cases hd : IsCoprime r d
      · rw [ite_eq_left hd,cubicSymbol_cube_of_isCoprime hr d hd,mul_one]
        ring
      · rw [ite_eq_right hd,cubicSymbol_eq_zero_of_not_isCoprime hr hd]
        simp

def cubicThetaPrimaryGaussSum (r u : Eisenstein) (ℓ : ℤ) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  ∑' cd : CubicThetaPrimaryPair,
    (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
      additivePhase r (cd.val.1*cd.val.2^3*u)*W (norm cd.val.1*norm cd.val.2^3/X)

lemma cubicThetaSelectedSmoothSum_rational (r u : Eisenstein) (ℓ : ℤ)
    (W : ℝ→ℂ) (X : ℝ) :
    cubicThetaSelectedSmoothSum ℓ ((traceLambda^3*(u:ℂ))/(r:ℂ)) W (X/27)=
      ((3^(5/2:ℝ):ℝ):ℂ)*theta ℓ lambdaE*cubicThetaPrimaryGaussSum r u ℓ W X := by
  rw [cubicThetaSelectedSmoothSum_pairs]
  have he : 27*(X/27)=X := by ring
  simp_rw [he,cubicThetaPrimary_additive_phase]
  rfl

theorem cubicThetaPrimaryGaussSum_average {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (ℓ : ℤ) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    {X : ℝ} (hX : 0<X) :
    (∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
      cubicThetaPrimaryGaussSum r (residueRepresentative r u) ℓ W X)=
    (Real.sqrt (norm r):ℂ)*gauss r*
      ∑' cd : CubicThetaPrimaryPair,
        if IsCoprime r cd.val.2 then
          (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
            star (cubicSymbol r cd.val.1)*W (norm cd.val.1*norm cd.val.2^3/X)
        else 0 := by
  let F (u : Residues r) (cd : CubicThetaPrimaryPair) : ℂ :=
    cubicSymbol r (residueRepresentative r u)*
      ((Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
        additivePhase r (cd.val.1*cd.val.2^3*residueRepresentative r u))*
          W (norm cd.val.1*norm cd.val.2^3/X)
  have hF (u : Residues r) : Summable (F u) := cubicThetaPrimary_smooth_summable _ W hW hX
  have hterm (cd : CubicThetaPrimaryPair) :
      (∑ u : Residues r,F u cd)=
      (Real.sqrt (norm r):ℂ)*gauss r*
        (if IsCoprime r cd.val.2 then
          (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
            star (cubicSymbol r cd.val.1)*W (norm cd.val.1*norm cd.val.2^3/X)
        else 0) := by
    let A := (Real.sqrt (norm cd.val.2):ℂ)*gauss cd.val.1*theta ℓ (cd.val.1*cd.val.2^3)*
      W (norm cd.val.1*norm cd.val.2^3/X)
    have ht : (∑ u : Residues r,F u cd)=A*
        ∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
          additivePhase r (cd.val.1*cd.val.2^3*residueRepresentative r u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [F,A]
      ring
    rw [ht,cubicThetaPrimary_character_sum hr hs]
    by_cases hd : IsCoprime r cd.val.2 <;> simp only [hd,ite_true,ite_false]
    · dsimp only [A]
      ring
    · ring
  calc
    _ = ∑ u : Residues r,∑' cd : CubicThetaPrimaryPair,F u cd := by
      apply Finset.sum_congr rfl
      intro u _
      rw [cubicThetaPrimaryGaussSum,←tsum_mul_left]
      apply tsum_congr
      intro cd
      dsimp only [F]
      ring
    _ = ∑' cd : CubicThetaPrimaryPair,∑ u : Residues r,F u cd :=
      (Summable.tsum_finsetSum (fun u _ => hF u)).symm
    _ = _ := by simp_rw [hterm]; rw [tsum_mul_left]

end CubicFirstMoment

end

end OAI
