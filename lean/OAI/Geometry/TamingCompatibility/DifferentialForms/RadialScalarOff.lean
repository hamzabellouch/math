import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScaledOffData
import OAI.Geometry.TamingCompatibility.Charts.RadialCutoffGeometry

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem closedLift_scalar_off_source
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
    (hχ0 : ((χ 4 : Space → ℂ) =ᶠ[𝓝 0] fun _ => 1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,q),
      ∀ (_hr : 0 < t.1), t.1 ≤ 1 →
      ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
        (hφK : tsupport φ ⊆ K) (j : Fin 2) (b : Space) (R M : ℝ), 0 ≤ R → 0 ≤ M →
        tsupport φ ⊆ Metric.ball b R → (∀ z, |φ z| ≤ M) →
        R+c*t.1 ≤ dist b t.2 →
        let f := testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
        ‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
          (extChartAt Model p.val).symm t.2 -
          ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm t.2‖ ≤ C*M*R^3/t.1^3 := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,he⟩ :=
    closedLift_scaled_off_source A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ hχ0
  obtain ⟨c,hc,hcs⟩ := normalizedCutoffs_bounded_radius L χ hcχ
  have hshrink : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), ∀ n : Fin 4, ∀ hr : t.1 ≠ 0,
      tsupport (normalizedCutoff L t.2 t.1 hr (χ (n.val+1))) ⊆ W := by
    apply Filter.eventually_all.mpr
    intro n
    exact normalizedCutoff_eventually_support L q (χ (n.val+1)) (hcχ n.val (by omega)) hW hqW
  refine ⟨c,hc,C,hC,?_⟩
  filter_upwards [he,hshrink] with t htest hts
  intro hr hr1 φ hφc hφK j b R M hR hM hball hval hsep
  dsimp only
  apply htest hr hr1 φ hφc hφK j b R M hR hM hball hval
  intro n hn z hz
  refine ⟨hts ⟨n,by omega⟩ hr.ne' hz,?_⟩
  intro hφz
  exact Set.disjoint_left.mp (closedBall_ball_disjoint_of_radii hsep)
    (hcs n hn t.2 t.1 hr hz) (hball hφz)

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility
open Set
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def supportedSchwartz (K : Set E) : Submodule ℝ 𝓢(E,ℝ) where
  carrier := {f | tsupport f ⊆ K}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact (tsupport_add (f : E → ℝ) g).trans (union_subset hf hg)
  smul_mem' := by
    intro c f hf
    exact (tsupport_smul_subset_right (fun _ : E => c) (f : E → ℝ)).trans hf

lemma supportedSchwartz_compact {K : Set E} (hK : IsCompact K)
    (f : supportedSchwartz K) : HasCompactSupport (f.val : E → ℝ) :=
  hK.of_isClosed_subset (isClosed_tsupport _) f.property

end TamingCompatibility

end
end

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
omit [IsManifold Model ∞ X] in
lemma chartLift_smul {k : ℕ} (p : X) (c : ℝ) (f : Space → MetricForms.Form Space k) :
    chartLift p (c • f) = c • chartLift p f := by
  funext x
  simp only [chartLift,Pi.smul_apply]
  split_ifs
  · rfl
  · simp
end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
lemma coordinateTest_smul (c : ℝ) (q : Space → EuclideanEnergy.Pair) :
    coordinateTest J α ht p D (c • q) = c • coordinateTest J α ht p D q := by
  funext z
  simp only [coordinateTest,frameTest,Pi.smul_apply,PiLp.smul_apply,smul_eq_mul]
  module
lemma manifoldTest_smul (c : ℝ) (q : Space → EuclideanEnergy.Pair) :
    manifoldTest J α ht p D (c • q) = c • manifoldTest J α ht p D q := by
  rw [manifoldTest,coordinateTest_smul,chartLift_smul,antiInvariantPart_smul]
  rfl
end TamingCompatibility.GeometricChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

def scalarTestLM (p : A.centers) (K : Set Space) (hK : IsCompact K)
    (hKD : K ⊆ (D p).domain) (j : Fin 2) :
    supportedSchwartz K →ₗ[ℝ] antiPre A J α hs ht where
  toFun f := testAnti A J α hs ht D p (componentTest j f.val)
    (componentTest_compact j f.val (supportedSchwartz_compact hK f))
    ((componentTest_support j f.val).trans (f.property.trans hKD))
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    change manifoldTest J α ht p.val (D p) (componentTest j (f.val+g.val)) = _
    have he : (componentTest j (f.val+g.val) : Space → EuclideanEnergy.Pair) =
        componentTest j f.val + componentTest j g.val := by
      funext z
      simp only [componentTest_apply,add_apply,add_smul,Pi.add_apply]
    rw [he,manifoldTest_add]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    change manifoldTest J α ht p.val (D p) (componentTest j (c • f.val)) = _
    have he : (componentTest j (c • f.val) : Space → EuclideanEnergy.Pair) =
        c • (componentTest j f.val : Space → EuclideanEnergy.Pair) := by
      funext z
      simp only [componentTest_apply,smul_apply,Pi.smul_apply,smul_smul,smul_eq_mul]
    rw [he,manifoldTest_smul]
    rfl

def smoothPullbackLM (p : X) (z : Space) :
    smoothForms X 2 →ₗ[ℝ] MetricForms.Form Space 2 where
  toFun a := ManifoldForms.pullback a.val (extChartAt Model p).symm z
  map_add' a b := congrFun (ManifoldForms.pullback_add a.val b.val (extChartAt Model p).symm) z
  map_smul' c a := congrFun (ManifoldForms.pullback_smul c a.val (extChartAt Model p).symm) z

def scalarCorrectionLM (Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (p : A.centers) (K : Set Space) (hK : IsCompact K)
    (hKD : K ⊆ (D p).domain) (j : Fin 2) (z : Space) :
    supportedSchwartz K →ₗ[ℝ] MetricForms.Form Space 2 :=
  (smoothPullbackLM p.val z).comp ((d.comp (antiDelta A J α hs ht)).comp
    (Gs.comp (scalarTestLM A J α hs ht D p K hK hKD j)))

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma scalarCorrectionLM_eq (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (p : A.centers) (K : Set Space) (hK : IsCompact K)
    (hKD : K ⊆ (D p).domain) (j : Fin 2) (z : Space) (f : supportedSchwartz K) :
    scalarCorrectionLM A J α hs ht D Gs p K hK hKD j z f =
      ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs
        (scalarTestLM A J α hs ht D p K hK hKD j f)).val (extChartAt Model p.val).symm z -
      ManifoldForms.pullback (k := 2) (H (scalarTestLM A J α hs ht D p K hK hKD j f)).val.val
        (extChartAt Model p.val).symm z := by
  rw [closedLiftOfInverse_pullback_sub]
  rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
