import Mathlib
import OAI.Geometry.PrescribedPotential.CoordinateInnerCover
import OAI.Geometry.PrescribedPotential.CoordinateMinimumBound
import OAI.Geometry.PrescribedPotential.NormalizedPotentialL1
import OAI.Geometry.PrescribedPotential.PathCoordinateDensity
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Path Potential Bound. -/

section

 

noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped ContDiff
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

theorem volumePath_oscillation_bound
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t b : ℝ) (φ : SmoothRealFunction A),
      t ∈ Icc 0 1 → SolvesVolumePath g h t φ b →
      ∀ x y, |φ.value x-φ.value y| ≤ C := by
  classical
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨S,hS⟩ := CoordinateBall.finite_inner_cover (A := A)
  obtain ⟨B,hB⟩ := normalized_potential_L1 g S
    (by intro x; obtain ⟨p,hp,hx⟩ := hS x; exact ⟨p,hp,p.half_source_sub hx⟩)
  choose K hK hKb using (fun p : S => p.val.path_det_bound g h)
  choose C hC using (fun p : S => p.val.minimum_bound g B (hK p))
  let R : ℝ := ∑ p : S, max (C p) 0
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨R,hR,?_⟩
  intro t b φ ht hs x y
  obtain ⟨xm,_,hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty φ.continuous.continuousOn
  obtain ⟨xM,_,hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty φ.continuous.continuousOn
  let ψ := φ.normalizeAt xM
  have hψ : g.PositivePotential ψ := by
    intro i z hz
    simpa only [ψ, SmoothRealFunction.hessian_normalizeAt] using hs.choose i z hz
  have hψ0 : ∀ z, ψ.value z ≤ 0 := by
    intro z
    change φ.value z-φ.value xM ≤ 0
    exact sub_nonpos.mpr (hmax (mem_univ z))
  have hψz : ∃ z, ψ.value z = 0 := ⟨xM,φ.normalizeAt_value xM⟩
  obtain ⟨p,hp,hxm⟩ := hS xm
  have hlocal := hC ⟨p,hp⟩ ψ hψ0 (hB ψ hψ hψ0 hψz p hp)
    (by
      intro z hz
      simpa only [ψ, SmoothRealFunction.hessian_normalizeAt] using
        hKb ⟨p,hp⟩ t b φ ht hs z hz)
    xm hxm (by
      intro z
      change φ.value xm-φ.value xM ≤ φ.value z-φ.value xM
      exact sub_le_sub_right (hmin (mem_univ z)) _)
  have hCR : C ⟨p,hp⟩ ≤ R := (le_max_left _ _).trans
    (Finset.single_le_sum (fun q _ => le_max_right (C q) 0) (Finset.mem_univ (⟨p,hp⟩ : S)))
  have hosc : φ.value xM-φ.value xm ≤ R := by
    change -(φ.value xm-φ.value xM) ≤ C ⟨p,hp⟩ at hlocal
    linarith
  have hxM : φ.value x ≤ φ.value xM := hmax (mem_univ x)
  have hyM : φ.value y ≤ φ.value xM := hmax (mem_univ y)
  have hmx : φ.value xm ≤ φ.value x := hmin (mem_univ x)
  have hmy : φ.value xm ≤ φ.value y := hmin (mem_univ y)
  exact abs_le.mpr ⟨by linarith only [hosc,hyM,hmx], by linarith only [hosc,hxM,hmy]⟩

 

theorem volumePath_potential_bound
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) (x₀ : X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t b : ℝ) (φ : SmoothRealFunction A),
      t ∈ Icc 0 1 → φ.value x₀ = 0 → SolvesVolumePath g h t φ b →
      ∀ x, |φ.value x| ≤ C := by
  obtain ⟨C,hC,hb⟩ := volumePath_oscillation_bound g h
  refine ⟨C,hC,?_⟩
  intro t b φ ht hn hs x
  simpa only [hn,sub_zero] using hb t b φ ht hs x x₀
end Anticanonical.SourceSmooth

end
end

end OAI
