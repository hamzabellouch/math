import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWindowWeak

namespace OAI

/-! The compact incoming window kills every spurious real residue of the
actual arithmetic family: only the theta parameter can contribute. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticResidueEnergy_eq_zero_of_orthogonal (σ : ℝ)
    (h : inner ℂ (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy σ))
      (cubicThetaForcingL2 σ)=0) : cubicThetaArithmeticResidueEnergy σ=0 := by
  let K := (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (σ:ℂ))).ker
  let f := cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 σ)
  let c := cubicThetaGlobalSpectralParameter (σ:ℂ)/((2*σ-2:ℝ):ℂ)
  let Q := K.starProjection f
  have hR : cubicThetaArithmeticResidueEnergy σ=c • Q := rfl
  by_cases hc : c=0
  · rw [hR,hc,zero_smul]
  have hP : K.starProjection Q=Q := K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem f)
  have hQ : inner ℂ Q f=inner ℂ Q Q := by
    have hi := K.inner_starProjection_left_eq_right Q f
    rw [hP] at hi
    exact hi
  have hi : inner ℂ (c • Q) f=0 := by
    rw [← hR,ContinuousLinearMap.adjoint_inner_right]
    exact h
  rw [inner_smul_left (𝕜:=ℂ) Q f c,hQ] at hi
  have hself : inner ℂ Q Q=0 := (mul_eq_zero.mp hi).resolve_left (by simpa using hc)
  have hzero : Q=0 := (inner_self_eq_zero (𝕜:=ℂ) (x:=Q)).mp hself
  rw [hR,hzero,smul_zero]

theorem cubicThetaArithmeticResidueEnergy_vanishes_closed {σ : ℝ}
    (hσ : 1<σ) (hσ2 : σ≤2) (hne : (σ:ℂ)≠4/3) :
    cubicThetaArithmeticResidueEnergy σ=0 :=
  cubicThetaArithmeticResidueEnergy_eq_zero_of_orthogonal σ
    (cubicThetaResidue_forcing_orthogonal_closed hσ hσ2 hne)

theorem cubicThetaArithmeticResidueEnergy_vanishes {σ : ℝ}
    (hσ : 1<σ) (hσ2 : σ<2) (hne : (σ:ℂ)≠4/3) :
    cubicThetaArithmeticResidueEnergy σ=0 :=
  cubicThetaArithmeticResidueEnergy_vanishes_closed hσ hσ2.le hne

end CubicFirstMoment

end

end OAI
