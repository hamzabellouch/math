import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStep

namespace OAI

/-! Separate the ramified cusp character from the ordinary cubic row
weight, using the proved step law and elementary reciprocity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaShiftedRowWeight_of_three_dvd {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) (hu : (3:Eisenstein) ∣ u) :
    cubicThetaShiftedRowWeight b c u=cubicSymbol c (3*u) := by
  unfold cubicThetaShiftedRowWeight
  apply cubicSymbol_periodic_of_nine_and_numerator
    (cubicTheta_primary_add_three_mul hc ⟨u,rfl⟩ b) hc
  · obtain ⟨v,rfl⟩ := hu
    exact ⟨b*v,by ring⟩
  · exact ⟨b,by ring⟩

lemma cubicThetaShiftedRowWeight_factor {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) :
    cubicThetaShiftedRowWeight b c u=
      star (cubicThetaCuspStepValue b u)*cubicSymbol c (3*u) := by
  let v := (1-c)*u
  have hv : (3:Eisenstein) ∣ v := by
    obtain ⟨k,hk⟩ := hc
    exact ⟨-k*u,by dsimp only [v]; linear_combination -u*hk⟩
  have hs := cubicThetaShiftedRowWeight_step hc b v u
  have he : v+c*u=u := by dsimp only [v]; ring
  rw [he,cubicThetaShiftedRowWeight_of_three_dvd hc b v hv] at hs
  have hr : cubicSymbol c (3*v)=cubicSymbol c (3*u) := by
    apply cubicSymbol_congr
    apply residue_eq_of_dvd_sub
    exact ⟨-3*u,by dsimp only [v]; ring⟩
  rwa [hr] at hs

end CubicFirstMoment

end

end OAI
