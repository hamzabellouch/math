import OAI.Geometry.RCD.Coordinates.FrameVelocityError

namespace OAI

/-! # Locality of the spatial frame velocity error -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem frameVelocityError_congr_ae {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    {g w : SobolevSpace μ Q} {S : Set X}
    (hgw : SobolevSpace.toLp μ Q g =ᵐ[μ.restrict S] SobolevSpace.toLp μ Q w) :
    frameVelocityError μ Q u g =ᵐ[μ.restrict S] frameVelocityError μ Q u w := by
  have hm (i : Fin n) := localGamma_pair_congr_ae μ Q
    (show SobolevSpace.toLp μ Q (u i) =ᵐ[μ.restrict S] SobolevSpace.toLp μ Q (u i)
      from Eventually.of_forall (fun _ => rfl)) hgw
  filter_upwards [localGamma_pair_congr_ae μ Q hgw hgw,ae_all_iff.mpr hm] with x hgg hm
  have hv : gradientFrameCoefficients μ Q u g x=gradientFrameCoefficients μ Q u w x := by
    exact congrArg (WithLp.toLp 2) (funext hm)
  unfold frameVelocityError frameEnergyError
  rw [hgg,hv]
  have hs : (∑ i, (localGamma μ Q (u i) g x)^2)=∑ i, (localGamma μ Q (u i) w x)^2 :=
    Finset.sum_congr rfl (fun i _ => congrArg (fun z : ℝ => z^2) (hm i))
  rw [hs]

theorem frameVelocityError_frame_congr_ae {n : ℕ} {u U : Fin n → SobolevSpace μ Q}
    (g : SobolevSpace μ Q) {S : Set X}
    (hu : ∀ i, SobolevSpace.toLp μ Q (U i) =ᵐ[μ.restrict S] SobolevSpace.toLp μ Q (u i)) :
    frameVelocityError μ Q U g =ᵐ[μ.restrict S] frameVelocityError μ Q u g := by
  have hm (i : Fin n) := localGamma_pair_congr_ae μ Q (hu i)
    (show SobolevSpace.toLp μ Q g =ᵐ[μ.restrict S] SobolevSpace.toLp μ Q g
      from Eventually.of_forall (fun _ => rfl))
  have hG (i j : Fin n) := localGamma_pair_congr_ae μ Q (hu i) (hu j)
  filter_upwards [ae_all_iff.mpr hm,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hG i))]
    with x hm hG
  have hv : gradientFrameCoefficients μ Q U g x=gradientFrameCoefficients μ Q u g x :=
    congrArg (WithLp.toLp 2) (funext hm)
  have he : frameEnergyError μ Q U g x=frameEnergyError μ Q u g x := by
    unfold frameEnergyError
    rw [Finset.sum_congr rfl (fun i _ => congrArg (fun z : ℝ => z^2) (hm i))]
  have hd : gramDefect μ Q U x=gramDefect μ Q u x := by
    unfold gramDefect
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hG i j]))
  unfold frameVelocityError
  rw [hv,he,hd]

end RegularPointCoordinates

end

end OAI
