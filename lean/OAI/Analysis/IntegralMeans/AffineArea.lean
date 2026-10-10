import OAI.Analysis.IntegralMeans.DomainArea
import OAI.Analysis.IntegralMeans.SharpModel

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Brennan.Sharp

lemma lintegral_affine_unit (a u : ℂ) (hu : ‖u‖ = 1) (f : ℂ → ℝ≥0∞) :
    (∫⁻ w, f (a + u * w)) = ∫⁻ z, f z := by
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  let F : ℂ → ℂ := fun w => a + u * w
  have hd (w : ℂ) : HasDerivAt F u w := by
    exact (hasDerivAt_const_mul (x := w) u).const_add a
  have hinj : InjOn F univ := by
    intro x _ y _ h
    change a + u * x = a + u * y at h
    exact mul_left_cancel₀ hu0 (add_left_cancel h)
  have himage : F '' univ = univ := by
    apply Set.eq_univ_of_forall
    intro z
    refine ⟨(z - a) / u, Set.mem_univ _, ?_⟩
    dsimp [F]
    field_simp [hu0]
    ring
  have he := conformal_lintegral_eq MeasurableSet.univ
    (fun z _ => (hd z).differentiableAt) hinj f
  rw [himage] at he
  have hder (z : ℂ) : deriv F z = u := (hd z).deriv
  simp only [setLIntegral_univ, hder, hu, one_pow, ENNReal.ofReal_one, one_mul] at he
  exact he.symm

lemma lintegral_left_disk_indicator (t : ℝ) :
    (∫⁻ w, disk.indicator (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ t)) (-1 + w)) =
      areaMoment koebeMap disk t := by
  have h := lintegral_affine_unit (-1) 1 (by simp)
    (disk.indicator (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ t)))
  have hdisk : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  rw [lintegral_indicator hdisk] at h
  simpa only [one_mul, areaMoment] using h

lemma lintegral_right_disk_indicator (t : ℝ) :
    (∫⁻ w, disk.indicator (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ t)) (1 - w)) =
      areaMoment koebeMap disk t := by
  have h := lintegral_affine_unit 1 (-1) (by simp)
    (disk.indicator (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ t)))
  have hdisk : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  rw [lintegral_indicator hdisk] at h
  simpa only [neg_one_mul, ← sub_eq_add_neg, areaMoment] using h

end Brennan.Sharp

end

end OAI
