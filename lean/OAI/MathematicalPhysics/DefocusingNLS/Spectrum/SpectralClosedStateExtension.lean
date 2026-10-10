import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFiniteUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedFluxPrimitive

namespace OAI

/-! Endpoint extension and backward uniqueness for continuous four-component ODE states. -/

open Set MeasureTheory
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralClosedState_extension (a b : ℝ) (hab : a < b) (F G : ℝ → E₄)
    (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (G x) x) :
    ∃ U : ℝ → E₄, Continuous U ∧
      (∀ x ∈ Icc a b, HasDerivAt U (G x) x) ∧ EqOn U F (Icc a b) := by
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
  let U := fun x => F m+∫ t in m..x, G₀ t
  have hU (x : ℝ) : HasDerivAt U (G₀ x) x :=
    (intervalIntegral.integral_hasDerivAt_right (hG₀.intervalIntegrable m x)
      hG₀.aestronglyMeasurable.stronglyMeasurableAtFilter hG₀.continuousAt).const_add _
  have hUc : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hU x).continuousAt)
  have he : EqOn F U (Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo a b).isPreconnected
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x _ => (hU x).differentiableAt.differentiableWithinAt) _ hm
    · simp only [U,intervalIntegral.integral_same,add_zero]
    · intro x hx
      rw [(hd x hx).deriv,(hU x).deriv]
      exact (congrArg G (hfix x ⟨hx.1.le,hx.2.le⟩)).symm
  refine ⟨U,hUc,fun x hx => ?_,?_⟩
  · simpa only [G₀,hfix x hx] using hU x
  · apply he.symm.of_subset_closure hUc.continuousOn hF Ioo_subset_Icc_self
    rw [closure_Ioo hab.ne]

theorem spectral_zero_on_open_annulus (Z G : ℝ → E₄) (L R B : ℝ) (hLR : L < R)
    (hZ : ContinuousOn Z (Icc L R)) (hG : ContinuousOn G (Icc L R))
    (hD : ∀ r ∈ Ioo L R, HasDerivAt Z (G r) r)
    (hB : ∀ r ∈ Icc L R, ‖G r‖ ≤ B*‖Z r‖)
    (hz : Z R=0) (r : ℝ) (hr : r ∈ Icc L R) : Z r=0 := by
  obtain ⟨U,hU,hd,he⟩ := spectralClosedState_extension L R hLR Z G hZ hG hD
  have huR : U R=0 := (he ⟨hLR.le,le_rfl⟩).trans hz
  have hu := spectral_zero_on_annulus U G L R B hU.continuousOn hd
    (fun t ht => by rw [he ht]; exact hB t ht) huR r hr
  exact (he hr).symm.trans hu

end DefocusingNLS

end OAI
