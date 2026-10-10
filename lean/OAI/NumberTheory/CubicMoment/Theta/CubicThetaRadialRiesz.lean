import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialForm

namespace OAI

/-! The weak inverse of the positive radial energy form, constructed by
Riesz representation on the closed graph space. This is not a postulated
spectral or automorphic continuation. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaRadialL2 := Lp ℂ 2 (volume : Measure ℝ)

def cubicThetaRadialProjection (i : Fin 3) :
    CubicThetaRadialJet →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 3 => ℂ) i

lemma cubicThetaRadialProjection_norm (i : Fin 3) : ‖cubicThetaRadialProjection i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (cubicThetaRadialProjection i) zero_le_one
  intro x
  simpa [cubicThetaRadialProjection] using PiLp.norm_apply_le x i

def cubicThetaRadialCoordinate (A : ℝ) (i : Fin 3) :
    cubicThetaRadialEnergySpace A →L[ℂ] CubicThetaRadialL2 :=
  ((cubicThetaRadialProjection i).compLpL 2 volume).comp
    (cubicThetaRadialEnergySpace A).subtypeL

abbrev cubicThetaRadialInclusion (A : ℝ) := cubicThetaRadialCoordinate A 0

lemma cubicThetaRadialCoordinate_bound (A : ℝ) (i : Fin 3)
    (u : cubicThetaRadialEnergySpace A) : ‖cubicThetaRadialCoordinate A i u‖ ≤ ‖u‖ := by
  calc
    _ ≤ ‖cubicThetaRadialProjection i‖*‖(u:CubicThetaRadialAmbient)‖ :=
      (cubicThetaRadialProjection i).norm_compLp_le _
    _ ≤ 1*‖u‖ := mul_le_mul_of_nonneg_right (cubicThetaRadialProjection_norm i) (_root_.norm_nonneg _)
    _ = _ := one_mul _

lemma cubicThetaRadialInclusion_norm (A : ℝ) : ‖cubicThetaRadialInclusion A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (cubicThetaRadialInclusion A) zero_le_one
  intro u
  simpa using cubicThetaRadialCoordinate_bound A 0 u

lemma cubicThetaRadialCoordinate_test (A : ℝ) (i : Fin 3) (f : cubicThetaRadialTests) :
    cubicThetaRadialCoordinate A i (cubicThetaRadialEnergyTest A f) =ᵐ[volume]
      (fun t => cubicThetaRadialJet A f t i) := by
  have hp := (cubicThetaRadialProjection i).coeFn_compLpL
    (cubicThetaRadialGraph A f)
  filter_upwards [hp,(cubicThetaRadialJet_memLp A f).coeFn_toLp] with t ht he
  change (cubicThetaRadialProjection i).compLpL 2 volume (cubicThetaRadialGraph A f) t=_
  rw [ht]
  change (cubicThetaRadialProjection i) (((cubicThetaRadialJet_memLp A f).toLp _) t)=_
  rw [he]
  rfl

lemma cubicThetaRadialInclusion_test (A : ℝ) (f : cubicThetaRadialTests) :
    cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f) =ᵐ[volume] f := by
  simpa [cubicThetaRadialJet] using cubicThetaRadialCoordinate_test A 0 f

def cubicThetaRadialWeakSolution (A : ℝ) (F : CubicThetaRadialL2) :
    cubicThetaRadialEnergySpace A :=
  (InnerProductSpace.toDual ℂ (cubicThetaRadialEnergySpace A)).symm
    ((innerSL ℂ F).comp (cubicThetaRadialInclusion A))

lemma cubicThetaRadialWeakSolution_equation (A : ℝ) (F : CubicThetaRadialL2)
    (v : cubicThetaRadialEnergySpace A) :
    inner ℂ (cubicThetaRadialWeakSolution A F) v=
      inner ℂ F (cubicThetaRadialInclusion A v) := by
  exact InnerProductSpace.toDual_symm_apply

lemma cubicThetaRadialWeakSolution_unique (A : ℝ) (F : CubicThetaRadialL2)
    {u : cubicThetaRadialEnergySpace A}
    (hu : ∀ v, inner ℂ u v=inner ℂ F (cubicThetaRadialInclusion A v)) :
    u=cubicThetaRadialWeakSolution A F := by
  apply (InnerProductSpace.toDual ℂ (cubicThetaRadialEnergySpace A)).injective
  ext v
  simpa [cubicThetaRadialWeakSolution] using hu v

lemma cubicThetaRadialWeakSolution_bound (A : ℝ) (F : CubicThetaRadialL2) :
    ‖cubicThetaRadialWeakSolution A F‖ ≤ ‖F‖ := by
  unfold cubicThetaRadialWeakSolution
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖innerSL ℂ F‖*‖cubicThetaRadialInclusion A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖F‖*1 := by
      rw [innerSL_apply_norm]
      exact mul_le_mul_of_nonneg_left (cubicThetaRadialInclusion_norm A) (_root_.norm_nonneg _)
    _ = _ := mul_one _

end CubicFirstMoment

end

end OAI
