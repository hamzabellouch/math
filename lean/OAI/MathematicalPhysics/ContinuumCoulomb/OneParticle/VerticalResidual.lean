import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalSliceProjection

namespace OAI

/-! Exact L2 mass splitting into the Gaussian transverse mode and its
orthogonal residual, for arbitrary product-space wavefunctions. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def verticalLift (freq : ℝ) (a : PlanarPosition → ℝ) (p : SplitPosition) : ℝ :=
  a p.1*verticalMode freq p.2

def verticalResidual (freq : ℝ) (f : SplitPosition → ℝ) (p : SplitPosition) : ℝ :=
  f p-verticalLift freq (verticalCoefficient freq f) p

theorem verticalLift_memLp {freq : ℝ} (hfreq : 0 < freq)
    (a : PlanarPosition → ℝ) (ha : MemLp a 2) : MemLp (verticalLift freq a) 2 := by
  have hm : AEStronglyMeasurable (verticalLift freq a)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) :=
    ha.aestronglyMeasurable.comp_fst.mul (verticalMode_memLp hfreq).aestronglyMeasurable.comp_snd
  have hi := ha.integrable_sq.mul_prod (verticalMode_square_integrable hfreq)
  have he : (fun p : SplitPosition => verticalLift freq a p^2) =
      fun p => (a p.1)^2*(verticalMode freq p.2)^2 := by
    funext p
    exact mul_pow _ _ _
  rw [← he] at hi
  apply (memLp_two_iff_integrable_sq (by simpa only [Measure.volume_eq_prod] using hm)).mpr
  simpa only [Measure.volume_eq_prod] using hi

theorem verticalLift_mass {freq : ℝ} (hfreq : 0 < freq) (a : PlanarPosition → ℝ) :
    (∫ p, (verticalLift freq a p)^2) = ∫ r, a r^2 := by
  simp_rw [verticalLift, mul_pow]
  rw [Measure.volume_eq_prod,
    integral_prod_mul (fun r => a r^2) (fun z => verticalMode freq z^2),
    verticalMode_normalized hfreq,mul_one]

theorem verticalCoefficient_lift {freq : ℝ} (hfreq : 0 < freq)
    (a : PlanarPosition → ℝ) (r : PlanarPosition) :
    verticalCoefficient freq (verticalLift freq a) r = a r := by
  unfold verticalCoefficient verticalLift
  rw [show (fun z => a r*verticalMode freq z*verticalMode freq z) =
    (fun z => a r*(verticalMode freq z)^2) from funext (fun z => by ring)]
  rw [integral_const_mul,verticalMode_normalized hfreq,mul_one]

theorem verticalCoefficient_pair_identity {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ p, f p*verticalLift freq (verticalCoefficient freq f) p) =
      ∫ r, (verticalCoefficient freq f r)^2 := by
  have ha := (verticalCoefficient_contraction hfreq f hf).1
  have hi := hf.integrable_mul (verticalLift_memLp hfreq _ ha)
  have hiprod : Integrable (fun p => f p*verticalLift freq (verticalCoefficient freq f) p)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hi
  rw [Measure.volume_eq_prod,integral_prod _ hiprod]
  apply integral_congr_ae
  filter_upwards [] with r
  change (∫ z, f (r,z)*(verticalCoefficient freq f r*verticalMode freq z)) = _
  rw [show (fun z => f (r,z)*(verticalCoefficient freq f r*verticalMode freq z)) =
    (fun z => verticalCoefficient freq f r*(f (r,z)*verticalMode freq z)) from
      funext (fun z => by ring),integral_const_mul]
  change verticalCoefficient freq f r*verticalCoefficient freq f r = _
  ring

/-- Exact Pythagoras identity for the actual transverse projection. -/
theorem verticalResidual_mass {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    MemLp (verticalResidual freq f) 2 ∧
      (∫ p, (verticalResidual freq f p)^2) =
        (∫ p, f p^2)-(∫ r, (verticalCoefficient freq f r)^2) := by
  let a := verticalCoefficient freq f
  let g := verticalLift freq a
  have ha : MemLp a 2 := (verticalCoefficient_contraction hfreq f hf).1
  have hg : MemLp g 2 := verticalLift_memLp hfreq a ha
  refine ⟨hf.sub hg,?_⟩
  have he : (fun p => (verticalResidual freq f p)^2) =
      (fun p => f p^2+(g p^2-2*(f p*g p))) := by
    funext p
    change (f p-g p)^2 = _
    ring
  rw [he,integral_add (f := fun p => f p^2) (g := fun p => g p^2-2*(f p*g p))
    hf.integrable_sq (hg.integrable_sq.sub ((hf.integrable_mul hg).const_mul 2)),
    integral_sub (f := fun p => g p^2) (g := fun p => 2*(f p*g p))
      hg.integrable_sq ((hf.integrable_mul hg).const_mul 2),integral_const_mul]
  have hm : (∫ p, g p^2) = ∫ r, a r^2 := verticalLift_mass hfreq a
  have hp : (∫ p, f p*g p) = ∫ r, a r^2 := verticalCoefficient_pair_identity hfreq f hf
  rw [hm,hp]
  dsimp [a]
  ring

theorem verticalResidual_coefficient_zero {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    verticalCoefficient freq (verticalResidual freq f) =ᵐ[volume] 0 := by
  have ha := (verticalCoefficient_contraction hfreq f hf).1
  have h := verticalCoefficient_sub_ae hfreq f
    (verticalLift freq (verticalCoefficient freq f)) hf (verticalLift_memLp hfreq _ ha)
  filter_upwards [h] with r hr
  change verticalCoefficient freq (fun p => f p-verticalLift freq (verticalCoefficient freq f) p) r = 0
  simpa only [verticalCoefficient_lift hfreq,sub_self] using hr

/-- The residual is orthogonal to every product with the transverse mode. -/
theorem verticalResidual_orthogonal {freq : ℝ} (hfreq : 0 < freq)
    (f : SplitPosition → ℝ) (hf : MemLp f 2)
    (a : PlanarPosition → ℝ) (ha : MemLp a 2) :
    (∫ p, verticalResidual freq f p*verticalLift freq a p) = 0 := by
  have hr := (verticalResidual_mass hfreq f hf).1
  have hi := hr.integrable_mul (verticalLift_memLp hfreq a ha)
  have hiprod : Integrable (fun p => verticalResidual freq f p*verticalLift freq a p)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hi
  rw [Measure.volume_eq_prod,integral_prod _ hiprod]
  apply integral_eq_zero_of_ae
  filter_upwards [verticalResidual_coefficient_zero hfreq f hf] with r hz
  change (∫ z, verticalResidual freq f (r,z)*(a r*verticalMode freq z)) = 0
  rw [show (fun z => verticalResidual freq f (r,z)*(a r*verticalMode freq z)) =
    (fun z => a r*(verticalResidual freq f (r,z)*verticalMode freq z)) from
      funext (fun z => by ring),integral_const_mul]
  change a r*verticalCoefficient freq (verticalResidual freq f) r = 0
  simp only [hz,Pi.zero_apply,mul_zero]

end ContinuumCoulomb

end

end OAI
