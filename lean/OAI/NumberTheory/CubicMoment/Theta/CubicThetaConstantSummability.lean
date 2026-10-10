import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantDirichlet

namespace OAI

/-! Absolute convergence of the original scattering coefficient already
on Re(s)>4/3, obtained from its proved cube support. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaConstantTermWeight_norm_summable {s : ℂ} (hs : 4/3<s.re) :
    Summable (fun c : Eisenstein => ‖cubicThetaConstantTermWeight s c‖) := by
  have ht : 1<(3*s-3).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith
  let g (ν : EisensteinIdealExponent) := cubicThetaPrimeDensity cubicThetaRamifiedPrime ν*
    (idealExponentNorm ν:ℂ)^(-(3*s-3))
  have hg : Summable (fun ν => ‖g ν‖) :=
    idealDirichlet_norm_summable _ (cubicThetaPrimeDensity_norm cubicThetaRamifiedPrime) ht
  have hp : Summable (fun x : Bool × EisensteinIdealExponent => (3/2:ℂ)*g x.2) :=
    summable_mul_of_summable_norm (f:=fun _ : Bool => (3/2:ℂ)) (g:=g)
      (hasSum_fintype _).summable hg
  have hp' : Summable (fun x : Bool × EisensteinIdealExponent =>
      ‖cubicThetaConstantTermWeight s (cubicThetaCubeCoordinates x).val‖) := by
    apply hp.norm.congr
    intro x
    apply congrArg (fun z : ℂ => ‖z‖)
    change (3/2:ℂ)*g x.2 = cubicThetaConstantTermWeight s (cubicThetaSignedCube x.1 x.2)
    simpa only [g,mul_assoc] using (cubicThetaConstantTermWeight_cube s x.1 x.2).symm
  have hsub : Summable (fun x : CubicThetaNonzeroCube => ‖cubicThetaConstantTermWeight s x.val‖) :=
    cubicThetaCubeCoordinates.summable_iff.mp hp'
  apply (Subtype.val_injective.summable_iff (f:=fun c : Eisenstein => ‖cubicThetaConstantTermWeight s c‖) ?_).mp hsub
  intro c hc
  have hz : cubicThetaConstantTermWeight s c=0 := by
    by_contra h
    exact hc ⟨⟨c,cubicThetaConstantTermWeight_support s h⟩,rfl⟩
  simp only [hz,norm_zero]

end CubicFirstMoment

end

end OAI
