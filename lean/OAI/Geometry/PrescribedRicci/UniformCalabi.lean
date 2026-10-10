import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiLocalMaximum
import OAI.Geometry.PrescribedRicci.CalabiTensorMetric
import OAI.Geometry.PrescribedRicci.CompactPathBounds
import OAI.Geometry.PrescribedRicci.CompactPathRicci

namespace OAI

/-! Uniform Calabi. -/

section

 

noncomputable section
open Matrix Set Filter Topology Manifold IsManifold
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma exists_nested_coordinateCutoff {K U : Set (Coordinates d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : Coordinates d → ℝ) (L : Set (Coordinates d)), ContDiff ℝ ∞ χ ∧
      IsCompact L ∧ L ⊆ U ∧ tsupport χ ⊆ interior L ∧ K ⊆ L ∧ ∀ z ∈ K, χ z = 1 := by
  obtain ⟨K₁,hK₁,hK₁c,hKK₁,hK₁U⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨f,hf,hf0,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,Coordinates d)) hK.isClosed hKK₁ (n:=⊤)
  have hsm : ContDiff ℝ ∞ (fun z => f z) := contMDiff_iff_contDiff.mp f.contMDiff
  have hsup : tsupport (fun z => f z) ⊆ K₁ := by
    apply closure_minimal _ hK₁c
    intro z hz
    by_contra hn
    exact hz (hf0 z hn)
  obtain ⟨L,hL,_,hK₁L,hLU⟩ := exists_compact_closed_between hK₁ hU hK₁U
  refine ⟨f,L,hsm,hL,hLU,hsup.trans hK₁L,?_,?_⟩
  · exact (hKK₁.trans interior_subset).trans (hK₁L.trans interior_subset)
  · intro z hz
    exact hf.self_of_nhdsSet z hz

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

 

theorem volumePath_calabi_bound_on_compact (g : KaehlerMetric A)
    (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d) (q : Fin A.count)
    {K : Set (Coordinates d)} (hK : IsCompact K) (hKt : K ⊆ (A.chart q).target) :
    ∃ P : ℝ, 0 < P ∧ ∀ (φ : SmoothRealFunction A) (hp : g.PositivePotential φ),
      g.integral φ.value = 0 → ∀ (t b : ℝ), t ∈ Icc (0:ℝ) 1 →
      (∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g line).value x+b) →
      ∀ z ∈ K, (g.deform φ hp).calabiNorm q z ≤ P := by
  obtain ⟨χ,L,hχ,hL,hLt,hχL,hKL,hχK⟩ := exists_nested_coordinateCutoff hK (A.chart q).open_target hKt
  obtain ⟨M,hM,hmetric⟩ := g.volumePath_metric_bounds_on_compact line hd q hL hLt
  obtain ⟨R,hR,hRicci⟩ := g.volumePath_ricci_bounds_on_compact line q hL hLt
  obtain ⟨P,hP,hCalabi⟩ := calabi_bound_on_compact q hL hLt χ hχ hχL hM.le hR.le
  refine ⟨P,hP,?_⟩
  intro φ hp hm t b ht heq z hz
  apply hCalabi (g.deform φ hp) (fun y hy => ?_) z (hKL hz) (hχK z hz)
  have h1 := hmetric φ hp hm t b ht heq y hy
  have h2 := hRicci φ hp t b ht heq y hy
  exact ⟨h1.1,h1.2,h2.1,h2.2⟩

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
