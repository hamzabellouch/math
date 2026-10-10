import OAI.Geometry.RCD.Sobolev.HessianScaledVelocity
import OAI.Geometry.RCD.Sobolev.HessianActionLocality
import OAI.Geometry.RCD.Metric.InwardLocality

namespace OAI

/-! # Forward-action expansion of the velocity Hessian

The physical velocity differs from the osmotic potential minus half the
forward potential by a spatial constant. These identities retain arbitrary
local Gram representatives and that additive gauge.
-/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localHessianAction_forward_osmotic
    (f η u fη fu ηη uu ηu : SobolevSpace μ Q) :
    (fun x => localHessianAction μ Q f (η-(1/2:ℝ) • u) (η-(1/2:ℝ) • u)
        (fη-(1/2:ℝ) • fu) (fη-(1/2:ℝ) • fu) (ηη-ηu+(1/4:ℝ) • uu) x -
      localHessianAction μ Q f η η fη fη ηη x) =ᵐ[μ]
      fun x => (1/4:ℝ)*localHessianAction μ Q f u u fu fu uu x-
        localHessianAction μ Q f η u fη fu ηu x := by
  filter_upwards [localGamma_sub_left μ Q η ((1/2:ℝ) • u) (fη-(1/2:ℝ) • fu),
    localGamma_smul_left μ Q (1/2:ℝ) u (fη-(1/2:ℝ) • fu),
    localGamma_sub_right μ Q η fη ((1/2:ℝ) • fu),
    localGamma_sub_right μ Q u fη ((1/2:ℝ) • fu),
    localGamma_smul_right μ Q (1/2:ℝ) η fu,
    localGamma_smul_right μ Q (1/2:ℝ) u fu,
    localGamma_add_right μ Q f (ηη-ηu) ((1/4:ℝ) • uu),
    localGamma_sub_right μ Q f ηη ηu,
    localGamma_smul_right μ Q (1/4:ℝ) f uu] with x h1 h2 h3 h4 h5 h6 h7 h8 h9
  dsimp only [localHessianAction]
  rw [h1,h2,h3,h4,h5,h6,h7,h8,h9]
  ring

theorem localGamma_forward_osmotic_reps {Ω : Set X}
    (f η u fη fu ηη uu ηu : SobolevSpace μ Q)
    (hfη : SobolevSpace.toLp μ Q fη =ᵐ[μ.restrict Ω] localGamma μ Q f η)
    (hfu : SobolevSpace.toLp μ Q fu =ᵐ[μ.restrict Ω] localGamma μ Q f u)
    (hηη : SobolevSpace.toLp μ Q ηη =ᵐ[μ.restrict Ω] localGamma μ Q η η)
    (huu : SobolevSpace.toLp μ Q uu =ᵐ[μ.restrict Ω] localGamma μ Q u u)
    (hηu : SobolevSpace.toLp μ Q ηu =ᵐ[μ.restrict Ω] localGamma μ Q η u) :
    (SobolevSpace.toLp μ Q (fη-(1/2:ℝ) • fu) =ᵐ[μ.restrict Ω]
      localGamma μ Q f (η-(1/2:ℝ) • u)) ∧
    (SobolevSpace.toLp μ Q (ηη-ηu+(1/4:ℝ) • uu) =ᵐ[μ.restrict Ω]
      localGamma μ Q (η-(1/2:ℝ) • u) (η-(1/2:ℝ) • u)) := by
  constructor
  · filter_upwards [hfη,hfu,
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q fη)
        (SobolevSpace.toLp μ Q ((1/2:ℝ) • fu))),
      ae_restrict_of_ae (Lp.coeFn_smul (1/2:ℝ) (SobolevSpace.toLp μ Q fu)),
      ae_restrict_of_ae (localGamma_sub_right μ Q f η ((1/2:ℝ) • u)),
      ae_restrict_of_ae (localGamma_smul_right μ Q (1/2:ℝ) f u)] with x h1 h2 h3 h4 h5 h6
    simp only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at h3 h4 ⊢
    rw [h3,h4,h1,h2,h5,h6]
  · filter_upwards [hηη,huu,hηu,
      ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.toLp μ Q (ηη-ηu))
        (SobolevSpace.toLp μ Q ((1/4:ℝ) • uu))),
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q ηη) (SobolevSpace.toLp μ Q ηu)),
      ae_restrict_of_ae (Lp.coeFn_smul (1/4:ℝ) (SobolevSpace.toLp μ Q uu)),
      ae_restrict_of_ae (localGamma_sub_left μ Q η ((1/2:ℝ) • u) (η-(1/2:ℝ) • u)),
      ae_restrict_of_ae (localGamma_sub_right μ Q η η ((1/2:ℝ) • u)),
      ae_restrict_of_ae (localGamma_sub_right μ Q u η ((1/2:ℝ) • u)),
      ae_restrict_of_ae (localGamma_smul_left μ Q (1/2:ℝ) u (η-(1/2:ℝ) • u)),
      ae_restrict_of_ae (localGamma_smul_right μ Q (1/2:ℝ) η u),
      ae_restrict_of_ae (localGamma_smul_right μ Q (1/2:ℝ) u u),
      ae_restrict_of_ae (localGamma_comm μ Q u η)] with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    simp only [map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at h4 h5 h6 ⊢
    rw [h4,h5,h6,h1,h2,h3,h7,h10,h8,h9,h11,h12,h13]
    ring

theorem localHessianAction_constant_directions {Ω : Set X}
    (f u u' v v' fu fu' fv fv' uv uv' : SobolevSpace μ Q) (c d : ℝ)
    (hu : SobolevSpace.toLp μ Q (u-u') =ᵐ[μ.restrict Ω] fun _ => c)
    (hv : SobolevSpace.toLp μ Q (v-v') =ᵐ[μ.restrict Ω] fun _ => d)
    (hfu : SobolevSpace.toLp μ Q fu =ᵐ[μ.restrict Ω] localGamma μ Q f u)
    (hfu' : SobolevSpace.toLp μ Q fu' =ᵐ[μ.restrict Ω] localGamma μ Q f u')
    (hfv : SobolevSpace.toLp μ Q fv =ᵐ[μ.restrict Ω] localGamma μ Q f v)
    (hfv' : SobolevSpace.toLp μ Q fv' =ᵐ[μ.restrict Ω] localGamma μ Q f v')
    (huv : SobolevSpace.toLp μ Q uv =ᵐ[μ.restrict Ω] localGamma μ Q u v)
    (huv' : SobolevSpace.toLp μ Q uv' =ᵐ[μ.restrict Ω] localGamma μ Q u' v') :
    localHessianAction μ Q f u v fu fv uv =ᵐ[μ.restrict Ω]
      localHessianAction μ Q f u' v' fu' fv' uv' := by
  have he (g : SobolevSpace μ Q) := localGamma_eq_of_constant_difference μ Q Ω u u' g c hu
  have he' (g : SobolevSpace μ Q) := localGamma_eq_of_constant_difference μ Q Ω v v' g d hv
  have hfu_eq : SobolevSpace.toLp μ Q fu =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q fu' := by
    filter_upwards [hfu,hfu',he f,ae_restrict_of_ae (localGamma_comm μ Q f u),
      ae_restrict_of_ae (localGamma_comm μ Q f u')] with x h1 h2 h3 h4 h5
    rw [h1,h2,h4,h5,h3]
  have hfv_eq : SobolevSpace.toLp μ Q fv =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q fv' := by
    filter_upwards [hfv,hfv',he' f,ae_restrict_of_ae (localGamma_comm μ Q f v),
      ae_restrict_of_ae (localGamma_comm μ Q f v')] with x h1 h2 h3 h4 h5
    rw [h1,h2,h4,h5,h3]
  have huv_eq : SobolevSpace.toLp μ Q uv =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q uv' := by
    filter_upwards [huv,huv',he v,he' u',ae_restrict_of_ae (localGamma_comm μ Q u' v),
      ae_restrict_of_ae (localGamma_comm μ Q v' u')] with x h1 h2 h3 h4 h5 h6
    rw [h1,h2,h3,h5,h4,h6]
  filter_upwards [he fv,he' fu,localGamma_pair_congr_ae μ Q (f := u') EventuallyEq.rfl hfv_eq,
    localGamma_pair_congr_ae μ Q (f := v') EventuallyEq.rfl hfu_eq,
    localGamma_pair_congr_ae μ Q (f := f) EventuallyEq.rfl huv_eq] with x h1 h2 h3 h4 h5
  dsimp only [localHessianAction]
  rw [h1,h2,h3,h4,h5]

end RegularPointCoordinates

end

end OAI
