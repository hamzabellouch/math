import OAI.MathematicalPhysics.Transonic.Profile.ODEGlueInfinite

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set SourceFamily ExteriorPolynomial PhysicalExterior

structure ExteriorTail {M : MatchedPair} (B : ExteriorBranch M) where
  v : ℝ → ℝ
  start : v B.beginning=M.velocity B.beginning
  range : ∀ y∈Ici B.beginning, |v y|<1
  below : ∀ y∈Ici B.beginning, v y<y ∧ y*v y<1
  den_ne : ∀ y∈Ici B.beginning, profileDenom ell y (v y)≠0
  derivative : ∀ y∈Ici B.beginning, HasDerivWithinAt v (field ell M.beta (y,v y)) (Ici B.beginning) y

lemma ExteriorBranch.exists_tail {M : MatchedPair} (B : ExteriorBranch M) : Nonempty (ExteriorTail B) := by
  have hbu := B.bounds 1 ⟨B.a_lt.le,le_rfl⟩
  obtain ⟨v,hv,hvr,hvd,hvs,hvb⟩ := window_global B.window hbu.1 hbu.2
  have hE : sonicRadius (ShootingParameters.beta M.parameter.val)*(1+B.d/256)=B.endpoint := B.endpoint_eq.symm
  rw [hE] at hv hvr hvd hvs hvb
  have hmatch : B.velocity B.endpoint=v B.endpoint := by rw [B.endpoint_value,hv]
  let w := ODEGlue.join B.endpoint B.velocity v
  have heq (y:ℝ) (hy:B.endpoint≤y) : w y=v y := ODEGlue.join_eq_right hy hmatch
  have hdf (y:ℝ) (hy:y∈Ici B.beginning) : HasDerivWithinAt w (field ell M.beta (y,w y)) (Ici B.beginning) y :=
    ODEGlue.hasDerivWithinAt_join_Ici (f:=fun y u => field ell M.beta (y,u)) B.beginning_bounds.2.2.le
      (fun _ hz => B.velocity_derivative hz) hvd hmatch y hy
  have hnear (y:ℝ) (hy:y≤B.endpoint) : w y=B.velocity y := ite_eq_left hy
  refine ⟨⟨w,?_,?_,?_,?_,hdf⟩⟩
  · rw [hnear B.beginning B.beginning_bounds.2.2.le]
    exact B.start_value
  · intro y hy
    by_cases he : y≤B.endpoint
    · rw [hnear y he]
      exact (B.physical_range ⟨hy,he⟩).1
    · have he' := (lt_of_not_ge he).le
      rw [heq y he']
      exact abs_lt.mpr ⟨(hvr y he').1,((hvr y he').2).trans_lt (abs_lt.mp B.barrier_abs).2⟩
  · intro y hy
    by_cases he : y≤B.endpoint
    · rw [hnear y he]
      exact (B.physical_range ⟨hy,he⟩).2
    · rw [heq y (lt_of_not_ge he).le]
      exact hvb y (lt_of_not_ge he).le
  · intro y hy
    by_cases he : y≤B.endpoint
    · rw [hnear y he]
      exact B.den_ne ⟨hy,he⟩
    · have hgt := (lt_of_not_ge he).le
      rw [heq y hgt]
      apply window_strip_den_ne B.window
      · rwa [hE]
      · rw [hE]
        exact ⟨(hvr y hgt).1.le,(hvr y hgt).2⟩

end SepticProfile.SonicShooting

end
end

end OAI
