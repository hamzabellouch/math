import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakFluxPrimitive

namespace OAI

/-! Extend a classical flux to the endpoints using its continuous source. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralClosedFlux_primitive (a b : ℝ) (hab : a < b) (F G : ℝ → ℂ)
    (hG : ContinuousOn G (Icc a b))
    (hF : ∀ x ∈ Ioo a b, HasDerivAt F (G x) x) :
    ∃ P : ℝ → ℂ, Continuous P ∧
      (∀ x ∈ Icc a b, HasDerivAt P (G x) x) ∧ EqOn F P (Ioo a b) := by
  let m := (a+b)/2
  have hm : m ∈ Ioo a b := by dsimp only [m]; constructor <;> linarith
  let clamp := fun x : ℝ => max a (min b x)
  have hc (x : ℝ) : clamp x ∈ Icc a b :=
    ⟨le_max_left _ _,max_le hab.le (min_le_left _ _)⟩
  have hfix (x : ℝ) (hx : x ∈ Icc a b) : clamp x=x := by
    dsimp only [clamp]
    rw [min_eq_right hx.2,max_eq_right hx.1]
  let G₀ := fun x => G (clamp x)
  have hG₀ : Continuous G₀ := hG.comp_continuous (by fun_prop) hc
  let P := fun x => F m+∫ t in m..x, G₀ t
  have hP (x : ℝ) : HasDerivAt P (G₀ x) x :=
    (intervalIntegral.integral_hasDerivAt_right (hG₀.intervalIntegrable m x)
      hG₀.aestronglyMeasurable.stronglyMeasurableAtFilter hG₀.continuousAt).const_add _
  refine ⟨P,continuous_iff_continuousAt.mpr (fun x => (hP x).continuousAt),?_,?_⟩
  · intro x hx
    simpa only [G₀,hfix x hx] using hP x
  · apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo a b).isPreconnected
      (fun x hx => (hF x hx).differentiableAt.differentiableWithinAt)
      (fun x _ => (hP x).differentiableAt.differentiableWithinAt) _ hm
    · simp only [P,intervalIntegral.integral_same,add_zero]
    · intro x hx
      rw [(hF x hx).deriv,(hP x).deriv]
      exact (congrArg G (hfix x ⟨hx.1.le,hx.2.le⟩)).symm

end DefocusingNLS

end OAI
