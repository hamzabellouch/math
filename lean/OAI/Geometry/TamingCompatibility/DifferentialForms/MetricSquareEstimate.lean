import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.LinearUniform

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma metric_square_uniform_estimate
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 2 →L[ℝ] R m)) (b : 𝓢(V,R 2 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j) :
    ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ (n : ℕ)
      (χ : 𝓢(V,ℂ)), HasCompactSupport (χ : V → ℂ) → tsupport χ ⊆ W →
      ∃ T : localSolutionSpace U n (square e a b ρ) →L[ℂ] H V (C 2) ((n:ℝ)+2),
      ∀ u, toDistribution V (C 2) ((n:ℝ)+2) (T u) =
        smulLeftCLM (C 2) χ (toDistribution V (C 2) 1 u.val.1) := by
  obtain ⟨W,hW,hpW,hWU,hreg⟩ := metric_square_uniform_regular hU p hp metric frame hframe
    a b ρ g ha c hc hgp
  refine ⟨W,hW,hpW,hWU,fun n χ hχ hχW => ?_⟩
  exact local_regular_estimate U W n (square e a b ρ) (hreg n) χ hχ hχW

end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

structure SquareData (p : A.centers) (U : Set Space) (q : Space) where
  W : Set Space
  openW : IsOpen W
  qW : q ∈ W
  WU : W ⊆ U
  a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)
  b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)
  ρ : 𝓢(Space,ℝ)
  g : Fin 4 → Fin 4 → Space → ℝ
  agreeA : ∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p) i z
  agreeB : ∀ z ∈ W, b z = normalB J α ht p.val (D p) z
  agreeρ : ∀ z ∈ W, ρ z = chartDensity J α p.val z
  polarized : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
    (2*g i j x) • ContinuousLinearMap.id ℝ EuclideanEnergy.Pair
  center : ∀ i j, g i j q = chartDensity J α p.val q * ∑ t, (D p).frame t q i * (D p).frame t q j

include hs in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_geometric_square_data (p : A.centers)
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (q : Space) (hq : q ∈ U) : Nonempty (SquareData A J α ht D p U q) := by
  obtain ⟨φ,hφ,hφU,W,hW,hqW,hWU,hφone⟩ := SchwartzCutoff.exists_one_near hU hq
  have hφD := hφU.trans hUD
  let a := patchA J α ht p.val (D p) (φ.smooth ⊤) hφ hφD
  let b := patchB J α hs ht p.val (D p) (φ.smooth ⊤) hφ hφD
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset) (φ.smooth ⊤) hφ hφD
  have ha : ∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p) i z := by
    intro z hz i
    simp only [a,patchA,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hb : ∀ z ∈ W, b z = normalB J α ht p.val (D p) z := by
    intro z hz
    simp only [b,patchB,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hρ : ∀ z ∈ W, ρ z = chartDensity J α p.val z := by
    intro z hz
    simp only [ρ,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  let G := fun i j z => ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p.val (D p) i j z
  have hG : ∀ i j, G i j q = chartDensity J α p.val q * ∑ t, (D p).frame t q i * (D p).frame t q j := by
    intro i j
    simp only [G,hρ q hqW,hφone q hqW,one_mul,GeometricChart.normalMetric,
      LocalMatrixOperator.frameCovector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      star_trivial,mul_comm]
  refine ⟨{ W := W
            openW := hW
            qW := hqW
            WU := hWU
            a := a
            b := b
            ρ := ρ
            g := G
            agreeA := ha
            agreeB := hb
            agreeρ := hρ
            polarized := ?_
            center := hG }⟩
  exact patchA_polarized J α ht p.val (D p) (φ.smooth ⊤) hφ hφD ρ

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

include hs in
omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_geometric_square_estimate (p : A.centers)
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
        (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ)),
        (∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p) i z) ∧
        (∀ z ∈ W, b z = normalB J α ht p.val (D p) z) ∧
        (∀ z ∈ W, ρ z = chartDensity J α p.val z) ∧
        ∀ (n : ℕ) (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
          ∃ T : localSolutionSpace W n (square EuclideanEnergy.e a b ρ) →L[ℂ] H Space (C 2) ((n:ℝ)+2),
            ∀ u, toDistribution Space (C 2) ((n:ℝ)+2) (T u) =
              smulLeftCLM (C 2) χ (toDistribution Space (C 2) 1 u.val.1) := by
  obtain ⟨d⟩ := exists_geometric_square_data A J α hs ht D p hU hUD q hq
  obtain ⟨V,hV,hqV,hVW,hest⟩ := metric_square_uniform_estimate (m := 4) d.openW q d.qW
    (coordinateMetric J α ht p.val q) (fun i => (D p).frame i q)
    ((D p).frame_gram q (hUD hq)) d.a d.b d.ρ d.g
    d.polarized
    (chartDensity J α p.val q) (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq))) d.center
  refine ⟨d.W,V,d.openW,d.qW,d.WU,hV,hqV,hVW,?_⟩
  refine ⟨d.a,d.b,d.ρ,d.agreeA,d.agreeB,d.agreeρ,?_⟩
  simpa only [Space,EuclideanEnergy.V] using hest

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
