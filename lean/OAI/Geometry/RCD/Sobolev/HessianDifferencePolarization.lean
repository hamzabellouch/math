import OAI.Geometry.RCD.Sobolev.HessianVelocityPolarization

namespace OAI

/-! # A diagonal Hessian difference is one mixed Hessian action -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localHessianAction_diagonal_difference
    (f u v fu fv uu vv : SobolevSpace μ Q) :
    (fun x => localHessianAction μ Q f u u fu fu uu x-
      localHessianAction μ Q f v v fv fv vv x) =ᵐ[μ]
      localHessianAction μ Q f (u-v) (u+v) (fu-fv) (fu+fv) (uu-vv) := by
  filter_upwards [localGamma_sub_left μ Q u v (fu+fv),
    localGamma_add_right μ Q u fu fv,localGamma_add_right μ Q v fu fv,
    localGamma_add_left μ Q u v (fu-fv),
    localGamma_sub_right μ Q u fu fv,localGamma_sub_right μ Q v fu fv,
    localGamma_sub_right μ Q f uu vv] with x h1 h2 h3 h4 h5 h6 h7
  dsimp only [localHessianAction]
  rw [h1,h2,h3,h4,h5,h6,h7]
  ring

theorem localGamma_difference_sum_rep {Ω : Set X}
    (u v uu vv : SobolevSpace μ Q)
    (huu : SobolevSpace.toLp μ Q uu =ᵐ[μ.restrict Ω] localGamma μ Q u u)
    (hvv : SobolevSpace.toLp μ Q vv =ᵐ[μ.restrict Ω] localGamma μ Q v v) :
    SobolevSpace.toLp μ Q (uu-vv) =ᵐ[μ.restrict Ω] localGamma μ Q (u-v) (u+v) := by
  simp only [map_sub]
  filter_upwards [huu,hvv,
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q uu) (SobolevSpace.toLp μ Q vv)),
    ae_restrict_of_ae (localGamma_sub_left μ Q u v (u+v)),
    ae_restrict_of_ae (localGamma_add_right μ Q u u v),
    ae_restrict_of_ae (localGamma_add_right μ Q v u v),
    ae_restrict_of_ae (localGamma_comm μ Q u v)] with x hu hv hs h1 h2 h3 hc
  rw [hs,h1,h2,h3]
  simp only [Pi.sub_apply,hu,hv]
  rw [hc]
  ring

theorem localGamma_sum_difference_bound {Ω : Set X} (u v : SobolevSpace μ Q)
    {P : ℝ}
    (hu : ∀ᵐ x ∂μ.restrict Ω, localGamma μ Q u u x ≤ P)
    (hv : ∀ᵐ x ∂μ.restrict Ω, localGamma μ Q v v x ≤ P) :
    (∀ᵐ x ∂μ.restrict Ω, localGamma μ Q (u-v) (u-v) x ≤ 4*P) ∧
    (∀ᵐ x ∂μ.restrict Ω, localGamma μ Q (u+v) (u+v) x ≤ 4*P) := by
  have hb : ∀ᵐ x ∂μ.restrict Ω,
      localGamma μ Q (u-v) (u-v) x ≤ 4*P ∧
      localGamma μ Q (u+v) (u+v) x ≤ 4*P := by
    filter_upwards [hu,hv,
      ae_restrict_of_ae (localGamma_sub_left μ Q u v (u-v)),
      ae_restrict_of_ae (localGamma_sub_right μ Q u u v),
      ae_restrict_of_ae (localGamma_sub_right μ Q v u v),
      ae_restrict_of_ae (localGamma_add_left μ Q u v (u+v)),
      ae_restrict_of_ae (localGamma_add_right μ Q u u v),
      ae_restrict_of_ae (localGamma_add_right μ Q v u v),
      ae_restrict_of_ae (localGamma_self μ Q (u-v)),
      ae_restrict_of_ae (localGamma_self μ Q (u+v))]
      with x hu hv hs hs1 hs2 ha ha1 ha2 hns hna
    have hn1 : 0 ≤ localGamma μ Q (u-v) (u-v) x := by rw [hns]; positivity
    have hn2 : 0 ≤ localGamma μ Q (u+v) (u+v) x := by rw [hna]; positivity
    rw [hs,hs1,hs2] at hn1 ⊢
    rw [ha,ha1,ha2] at hn2 ⊢
    constructor <;> linarith
  exact ⟨hb.mono fun _ h => h.1,hb.mono fun _ h => h.2⟩

end RegularPointCoordinates

end

end OAI
