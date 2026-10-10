import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroFourier

namespace OAI

/-! The exact residue of the zero Fourier mode of the principal
level-three Eisenstein series. Nonzero Fourier modes remain separate. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaConstantModeContinuation (v : ℝ) (s : ℂ) : ℂ :=
  (v:ℂ)^s+((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s)*
    cubicThetaConstantContinuation s

lemma cubicThetaConstantModeContinuation_right {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 4/3<s.re) :
    cubicThetaEisensteinConstantMode v s=cubicThetaConstantModeContinuation v s := by
  rw [cubicThetaEisensteinConstantMode_eq hv (by linarith),cubicThetaConstantContinuation_right hs]
  rfl

lemma cubicTheta_principalZeta_residue_value :
    principalThetaConstant/(residueHeckeScale 1:ℂ)=(Real.pi:ℂ)/(3*Real.sqrt 3) := by
  unfold principalThetaConstant residueHeckeScale
  rw [eisenstein_units_card]
  have hnorm : norm (1:Eisenstein)=1 := by norm_num [norm]
  rw [hnorm,mul_one,Complex.ofReal_div,Complex.ofReal_mul]
  push_cast
  field_simp
  ring

theorem cubicThetaConstantModeContinuation_residue {v : ℝ} (hv : 0<v) :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaConstantModeContinuation v s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (((2*Real.pi/(3*Real.sqrt 3):ℂ)*
        ((principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2)))*
          (v:ℂ)^(2/3:ℂ))) := by
  let _ : NeZero (v:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hv.ne'⟩
  have hpow : ContinuousAt (fun s : ℂ => (v:ℂ)^s) (4/3:ℂ) :=
    (differentiable_const_cpow_of_neZero (v:ℂ)).continuous.continuousAt
  have hpow' : ContinuousAt (fun s : ℂ => (v:ℂ)^(2-s)) (4/3:ℂ) :=
    (differentiable_const_cpow_of_neZero (v:ℂ)).continuous.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  have hz := (continuousAt_id.sub (continuousAt_const (y:=(4/3:ℂ)))).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ))
  have hlead : Tendsto (fun s : ℂ => (s-4/3)*(v:ℂ)^s) (𝓝[≠] (4/3:ℂ)) (𝓝 0) := by
    simpa using hz.mul (hpow.tendsto.mono_left nhdsWithin_le_nhds)
  have hp : ContinuousAt (fun s : ℂ => ((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*
      (v:ℂ)^(2-s)) (4/3:ℂ) :=
    (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by norm_num)).mul hpow'
  have hr := hlead.add ((hp.tendsto.mono_left nhdsWithin_le_nhds).mul
    cubicThetaConstantContinuation_residue)
  have he : (fun s : ℂ => (s-4/3)*cubicThetaConstantModeContinuation v s)=
      (fun s : ℂ => (s-4/3)*(v:ℂ)^s+
        (((2*Real.pi/(9*Real.sqrt 3):ℂ)/(s-1))*(v:ℂ)^(2-s))*
          ((s-4/3)*cubicThetaConstantContinuation s)) := by
    funext s
    unfold cubicThetaConstantModeContinuation
    ring
  rw [he]
  convert hr using 1
  norm_num
  ring

end CubicFirstMoment

end

end OAI
