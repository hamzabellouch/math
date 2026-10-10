import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport
import OAI.Geometry.PrescribedPotential.AtlasLocalization
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Kahler Integration. -/

section

 

noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise Classical
namespace Anticanonical
namespace ComplexAtlas
variable {d : ℕ} {X : Type*} [TopologicalSpace X] (A : ComplexAtlas d X)

def transitionHomeomorph (i j : Fin A.count) :
    OpenPartialHomeomorph (Coordinates d) (Coordinates d) :=
  (A.chart i).symm.trans (A.chart j)

lemma transitionHomeomorph_source (i j : Fin A.count) :
    (A.transitionHomeomorph i j).source = coordinateOverlap (A.chart i) (A.chart j) := rfl

lemma transition_fderiv_det (i j : Fin A.count) {z : Coordinates d}
    (hz : z ∈ coordinateOverlap (A.chart i) (A.chart j)) :
    |(fderiv ℝ (A.transition i j) z).det| =
      ‖A.jacobian i j ((A.chart i).symm z)‖ ^ 2 := by
  have hd := (A.holomorphic i j).differentiableAt
    ((A.isOpen_coordinateOverlap i j).mem_nhds hz)
  change DifferentiableAt ℂ (A.transition i j) z at hd
  rw [hd.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, Algebra.norm_complex_eq, jacobian, (A.chart i).right_inv hz.1,
    LinearMap.det_toMatrix']
  change |Complex.normSq _| = _
  rw [Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

lemma transition_hasFDerivAt (i j : Fin A.count) {z : Coordinates d}
    (hz : z ∈ (A.transitionHomeomorph i j).source) :
    HasFDerivAt (A.transitionHomeomorph i j) (fderiv ℝ (A.transition i j) z) z :=
  ((A.real_smooth_transition i j).contDiffAt
    ((A.isOpen_coordinateOverlap i j).mem_nhds hz)).differentiableAt (by simp) |>.hasFDerivAt

end ComplexAtlas
namespace SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace SmoothRealFunction

def product (φ ψ : SmoothRealFunction A) : SmoothRealFunction A where
  value x := φ.value x * ψ.value x
  smooth i := (φ.smooth i).mul (ψ.smooth i)

 

def localized (φ : SmoothRealFunction A) (i : Fin A.count) (z : Coordinates d) : ℝ :=
  if z ∈ (A.chart i).target then φ.localExpression i z else 0

lemma localized_eq {φ : SmoothRealFunction A} {i : Fin A.count} {z : Coordinates d}
    (hz : z ∈ (A.chart i).target) : φ.localized i z = φ.localExpression i z := ite_eq_left hz

lemma localized_support (φ : SmoothRealFunction A) (i : Fin A.count) :
    Function.support (φ.localized i) ⊆ (A.chart i) '' tsupport φ.value := by
  intro z hz
  change φ.localized i z ≠ 0 at hz
  by_cases ht : z ∈ (A.chart i).target
  · have hh : φ.value ((A.chart i).symm z) ≠ 0 := by
      simpa only [localized_eq ht, localExpression, Function.comp_apply] using hz
    exact ⟨(A.chart i).symm z, subset_tsupport _ hh, (A.chart i).right_inv ht⟩
  · exact (hz (ite_eq_right ht)).elim

lemma localized_smooth_compact [T2Space X] [CompactSpace X]
    (φ : SmoothRealFunction A) (i : Fin A.count)
    (hφ : tsupport φ.value ⊆ (A.chart i).source) :
    ContDiff ℝ ∞ (φ.localized i) ∧ HasCompactSupport (φ.localized i) ∧
      tsupport (φ.localized i) ⊆ (A.chart i).target := by
  let e := A.chart i
  let K := e '' tsupport φ.value
  have hK : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
    (e.continuousOn.mono hφ)
  have hs : Function.support (φ.localized i) ⊆ K := φ.localized_support i
  have hts : tsupport (φ.localized i) ⊆ K := closure_minimal hs hK.isClosed
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK hs, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ e.target
    · apply ((φ.smooth i).contDiffAt (e.open_target.mem_nhds hz)).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hz] with y hy using φ.localized_eq hy
    · have hzK : z ∉ K := by
        rintro ⟨x, hx, rfl⟩
        exact hz (e.mapsTo (hφ hx))
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with y hy
      exact Function.notMem_support.mp (fun h => hy (hs h))
  · rintro z hz
    obtain ⟨x, hx, rfl⟩ := hts hz
    exact e.mapsTo (hφ hx)

end SmoothRealFunction
namespace KaehlerMetric

def chartIntegral (g : KaehlerMetric A) (i : Fin A.count) (f : X → ℝ) : ℝ :=
  ∫ z in (A.chart i).target, f ((A.chart i).symm z) * g.volumeCoefficient i z

 

theorem chartIntegral_eq (g : KaehlerMetric A) (i j : Fin A.count) (f : X → ℝ)
    (hi : Function.support f ⊆ (A.chart i).source)
    (hj : Function.support f ⊆ (A.chart j).source) :
    g.chartIntegral i f = g.chartIntegral j f := by
  let e := A.transitionHomeomorph i j
  have hs (a b : Fin A.count) (hb : Function.support f ⊆ (A.chart b).source) :
      (∫ z in (A.transitionHomeomorph a b).source,
        f ((A.chart a).symm z) * g.volumeCoefficient a z) = g.chartIntegral a f := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart a).open_target.measurableSet
      (fun _ h => h.1)
    intro z hz
    have hn : (A.chart a).symm z ∉ (A.chart b).source := by
      intro h
      exact hz.2 ⟨hz.1, h⟩
    have hf : f ((A.chart a).symm z) = 0 := Function.notMem_support.mp (fun h => hn (hb h))
    rw [hf, zero_mul]
  rw [← hs i j hj, ← hs j i hi]
  have heq := integral_target_eq_integral_abs_det_fderiv_smul (μ := (volume : Measure (Coordinates d)))
    (f := e) (f' := fun z => fderiv ℝ (A.transition i j) z)
    (fun z hz => A.transition_hasFDerivAt i j hz)
    (fun z => f ((A.chart j).symm z) * g.volumeCoefficient j z)
  have htarget : e.target = (A.transitionHomeomorph j i).source := by
    ext z
    rfl
  rw [htarget] at heq
  rw [heq]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro z hz
  have hzi : (A.chart i).symm z ∈ (A.chart i).source := (A.chart i).mapsTo_symm hz.1
  have hzj : (A.chart i).symm z ∈ (A.chart j).source := hz.2
  have hc := g.volumeCoefficient_compatibility i j hzi hzj
  rw [(A.chart i).right_inv hz.1] at hc
  change f ((A.chart i).symm z) * g.volumeCoefficient i z =
    |(fderiv ℝ (A.transition i j) z).det| *
      (f ((A.chart j).symm (A.chart j ((A.chart i).symm z))) *
        g.volumeCoefficient j (A.chart j ((A.chart i).symm z)))
  rw [A.transition_fderiv_det i j hz, (A.chart j).left_inv hzj, hc]
  ring

end KaehlerMetric
end SourceSmooth
end Anticanonical

end
end

end OAI
