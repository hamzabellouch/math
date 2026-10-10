import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanWeight

namespace OAI

/-! The row phases recover the finite Gauss coefficient when the
incoming Fourier index is zero. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaHorizontalCharacter_zero_index (z : ℂ) :
    cubicThetaHorizontalCharacter 0 z=1 := by
  simp [cubicThetaHorizontalCharacter,cubicThetaRowFrequency,tracePair]

lemma cubicThetaHorizontalCharacter_quotient (h d c : Eisenstein) :
    cubicThetaHorizontalCharacter h ((d:ℂ)/(c:ℂ))=
      (Real.fourierChar (tracePair (d:ℂ) ((h:ℂ)/((3*c:Eisenstein)*traceLambda))):ℂ) := by
  unfold cubicThetaHorizontalCharacter cubicThetaRowFrequency tracePair
  congr 3
  push_cast
  rw [show ((3:Eisenstein):ℂ)=(3:ℂ) from rfl]
  ring_nf

lemma cubicThetaKloostermanWeight_zero_index (h c : Eisenstein)
    (hc : (3:Eisenstein)∣c) (d : Eisenstein) :
    cubicThetaKloostermanWeight h 0 c hc d=
      cubicThetaEisensteinWeight c d*cubicThetaHorizontalCharacter h ((d:ℂ)/(c:ℂ)) := by
  classical
  unfold cubicThetaKloostermanWeight cubicThetaEisensteinWeight
  split_ifs with hd
  · simp only [cubicThetaGramRowPhase,CubicThetaBottomRow.phase,star_star,
      cubicThetaHorizontalCharacter_zero_index,mul_one]
  · rw [zero_mul]

theorem cubicThetaKloostermanSum_zero_index (h c : Eisenstein)
    (hc : (3:Eisenstein)∣c) :
    cubicThetaKloostermanSum h 0 c hc=cubicThetaEisensteinGaussCoefficient c h := by
  unfold cubicThetaKloostermanSum cubicThetaEisensteinGaussCoefficient
  apply tsum_congr
  intro x
  rw [cubicThetaKloostermanWeight_zero_index,cubicThetaHorizontalCharacter_quotient]
  rfl

end CubicFirstMoment

end

end OAI
