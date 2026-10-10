import Mathlib
import OAI.Analysis.Conductivity.Sources.LocalPiola

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma localPiolaSource_support (X : OpenPartialHomeomorph E E) (r : E → ℝ) :
    Function.support (localPiolaSource X r)⊆X '' (Function.support r∩X.source) := by
  intro y hy
  by_cases hyt : y∈X.target
  · refine ⟨X.symm y,⟨?_,X.map_target hyt⟩,X.right_inv hyt⟩
    intro hz
    exact hy (by simp [localPiolaSource,hyt,hz])
  · exact False.elim (hy (by simp [localPiolaSource,hyt]))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma localPiolaSource_compact (X : OpenPartialHomeomorph E E)
    (r : E → ℝ) (hc : HasCompactSupport r) (hs : tsupport r⊆X.source) :
    HasCompactSupport (localPiolaSource X r) ∧ tsupport (localPiolaSource X r)⊆X.target := by
  have hci : IsCompact (X '' tsupport r) := hc.image_of_continuousOn (X.continuousOn.mono hs)
  have ht : tsupport (localPiolaSource X r)⊆X '' tsupport r :=
    closure_minimal ((localPiolaSource_support X r).trans
      (image_mono (fun _ hx => subset_closure hx.1))) hci.isClosed
  exact ⟨hci.of_isClosed_subset isClosed_closure ht,ht.trans (by
    rintro y ⟨x,hx,rfl⟩; exact X.map_source (hs hx))⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma localPiolaSource_smooth (X : OpenPartialHomeomorph E E)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (r : E → ℝ) (hr : ContDiff ℝ (↑(⊤ : ℕ∞)) r)
    (hc : HasCompactSupport r) (hs : tsupport r⊆X.source) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (localPiolaSource X r) := by
  apply contDiff_of_contDiffOn_tsupport X.open_target _ (localPiolaSource_compact X r hc hs).2
  apply X.open_target.contDiffOn_iff.mpr
  intro y hy
  have hxi := hXi.contDiffAt (X.open_target.mem_nhds hy)
  have hx := hX.contDiffAt (X.open_source.mem_nhds (X.map_target hy))
  have hd : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun z => fderiv ℝ X (X.symm z)) y :=
    (hx.fderiv_right (by simp)).comp y hxi
  have hd0 := local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
    (hXi.differentiableOn (by simp)) (X.map_target hy)
  have hdet := ((contDiff_clm_det (E:=E) (↑(⊤ : ℕ∞))).contDiffAt.comp y hd).abs hd0
  have hformula := (hdet.inv (abs_ne_zero.mpr hd0)).mul (hr.contDiffAt.comp y hxi)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [X.open_target.mem_nhds hy] with z hz
  simp only [localPiolaSource,ite_eq_left hz]
  rfl

lemma localPiolaSource_coordinate_pairing (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target)
    (r : E → ℝ) (hs : Function.support r⊆X.source) (φ : E → ℝ) :
    (∫ y,φ (X.symm y)*localPiolaSource X r y ∂μ)=(∫ x,φ x*r x ∂μ) := by
  rw [localPiolaSource_pairing μ X hX
    (fun _ hx => local_fderiv_det_ne_zero X hX hXi hx) r hs (fun y => φ (X.symm y))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x∈Function.support r
  · simp only [X.left_inv (hs hx)]
  · rw [Function.notMem_support.mp hx,mul_zero,mul_zero]

end ScalarConductivity

end

end OAI
