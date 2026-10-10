import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitTestFunctions

namespace OAI

/-! Integrability of the actual sliced forms. These lemmas justify applying
Fubini and integrating the published one-dimensional and planar estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem split_square_integrable {f : SplitPosition → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun p => f p^2) :=
  (hf.continuous.memLp_of_hasCompactSupport hc (p := 2)).integrable_sq

theorem split_potential_integrable {f V : SplitPosition → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hV : Continuous V) :
    Integrable (fun p => V p*f p^2) := by
  have hs : HasCompactSupport (fun p => f p^2) :=
    hc.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hp : HasCompactSupport (fun p => V p*f p^2) := hs.mul_left
  exact (hV.mul (hf.pow 2)).integrable_of_hasCompactSupport hp

theorem split_planar_slice_contDiff {f : SplitPosition → ℝ}
    (hf : ContDiff ℝ 1 f) (z : ℝ) : ContDiff ℝ 1 (fun r => f (r,z)) :=
  hf.comp (contDiff_id.prodMk contDiff_const)

theorem split_vertical_slice_contDiff {f : SplitPosition → ℝ}
    (hf : ContDiff ℝ 1 f) (r : PlanarPosition) : ContDiff ℝ 1 (fun z => f (r,z)) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

theorem split_planar_mass_integral {f : SplitPosition → ℝ}
    (hf : MemLp f 2) :
    (∫ z : ℝ, ∫ r : PlanarPosition, f (r,z)^2) = ∫ p, f p^2 := by
  have hi : Integrable (fun p : SplitPosition => f p^2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrable_sq
  simpa only [Measure.volume_eq_prod] using (integral_prod_symm _ hi).symm

theorem split_vertical_mass_integral {f : SplitPosition → ℝ}
    (hf : MemLp f 2) :
    (∫ r : PlanarPosition, ∫ z : ℝ, f (r,z)^2) = ∫ p, f p^2 := by
  have hi : Integrable (fun p : SplitPosition => f p^2) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrable_sq
  simpa only [Measure.volume_eq_prod] using (integral_prod _ hi).symm

theorem split_planar_form_integrable {m : ℕ} (u : Fin m → PlanarPosition)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun z => planarTestForm (planarWellSum u) (fun r => f (r,z))) := by
  have hk : ∀ a : Fin 2, Integrable (fun z : ℝ =>
      ∫ r : PlanarPosition, (splitPlanarPartial f a (r,z))^2) := by
    intro a
    have hi : Integrable (fun p => (splitPlanarPartial f a p)^2) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact splitPlanarPartial_square_integrable hf hc a
    exact hi.integral_prod_right
  have hi : Integrable (fun p : SplitPosition => planarWellSum u p.1*f p^2)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact split_potential_integrable hf.continuous hc
      ((planarWellSum_continuous u).comp continuous_fst)
  have he : (fun z => planarTestForm (planarWellSum u) (fun r => f (r,z))) =
      (fun z => (1/2:ℝ)*(∑ a : Fin 2, ∫ r : PlanarPosition,
        (splitPlanarPartial f a (r,z))^2) + ∫ r, planarWellSum u r*f (r,z)^2) := by
    funext z
    simp only [planarTestForm, splitPlanarPartial_eq hf]
  rw [he]
  exact ((integrable_finsetSum _ (fun a _ => hk a)).const_mul (1/2)).add
    hi.integral_prod_right

theorem split_vertical_form_integrable (freq S : ℝ)
    {f : SplitPosition → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun r : PlanarPosition => verticalCappedForm freq S (fun z => f (r,z))) := by
  have hk : Integrable (fun p : SplitPosition => (splitVerticalPartial f p)^2)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact splitVerticalPartial_square_integrable hf hc
  have hi : Integrable (fun p : SplitPosition => verticalCapPotential freq S p.2*f p^2)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    apply split_potential_integrable hf.continuous hc
    unfold verticalCapPotential
    fun_prop
  have he : (fun r : PlanarPosition => verticalCappedForm freq S (fun z => f (r,z))) =
      (fun r => (1/2:ℝ)*(∫ z : ℝ, (splitVerticalPartial f (r,z))^2) +
        ∫ z, verticalCapPotential freq S z*f (r,z)^2) := by
    funext r
    simp only [verticalCappedForm, splitVerticalPartial_eq hf]
  rw [he]
  exact (hk.integral_prod_left.const_mul (1/2)).add hi.integral_prod_left

end ContinuumCoulomb

end

end OAI
