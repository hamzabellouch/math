import Mathlib
import OAI.Geometry.TamingCompatibility.Currents.NormalDistribution
import OAI.Geometry.TamingCompatibility.DifferentialForms.TestEvaluation
import OAI.Geometry.TamingCompatibility.Currents.DistributionEvaluation
import OAI.Geometry.TamingCompatibility.DifferentialForms.RawTest

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def testAnti (p : A.centers) (q : 𝓢(Space,EuclideanEnergy.Pair))
    (hc : HasCompactSupport (q : Space → _)) (hqD : tsupport q ⊆ (D p).domain) :
    antiPre A J α hs ht :=
  ⟨⟨manifoldTest J α ht p.val (D p) q,manifoldTest_smooth J α hs ht p.val (D p) (q.smooth ⊤) hc hqD⟩,
    manifoldTest_anti J α ht p.val (D p) q⟩

lemma componentTest_support (j : Fin 2) (φ : 𝓢(Space,ℝ)) :
    tsupport (componentTest j φ) ⊆ tsupport φ := by
  exact tsupport_smul_subset_left (φ : Space → ℝ)
    (fun _ : Space => EuclideanSpace.single j (1:ℝ))

lemma componentTest_compact (j : Fin 2) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) : HasCompactSupport (componentTest j φ : Space → _) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (componentTest_support j φ)

omit [T2Space X] in
lemma smooth_delta_pair (u v : antiPre A J α hs ht) :
    ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht u),
      weakDelta A J α hs ht (antiToEnergy A J α hs ht v)⟫ =
      ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht u.val.val)
        (codifferential J α ht v.val.val) x ∂geometricVolume A J α := by
  change ⟪smoothL2 A J α hs ht false (antiDelta A J α hs ht u),
    smoothL2 A J α hs ht false (antiDelta A J α hs ht v)⟫ = _
  rw [(smoothL2 A J α hs ht false).inner_map_map,preL2_inner]
  rfl

lemma raw_square_energy (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p) i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p) z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 2) (u : antiEnergy A J α hs ht) :
    (ComplexMatrix.square EuclideanEnergy.e a b ρ (rawDistribution A J α hs ht D hD p τ u)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      (⟪weakDelta A J α hs ht u,weakDelta A J α hs ht
        (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  let q := componentTest j φ
  let v := testAnti A J α hs ht D p q (componentTest_compact j φ hc)
    ((componentTest_support j φ).trans (hφU.trans hUD))
  have hLc : Continuous (fun w => (ComplexMatrix.square EuclideanEnergy.e a b ρ
      (rawDistribution A J α hs ht D hD p τ w)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j) :=
    by
      generalize rawDistribution A J α hs ht D hD p τ = L
      generalize ComplexMatrix.square EuclideanEnergy.e a b ρ = P
      exact continuous_system_eval L P (SchwartzMap.postcompCLM Complex.ofRealCLM φ) j
  have hRc : Continuous (fun w => (⟪weakDelta A J α hs ht w,
      weakDelta A J α hs ht (antiToEnergy A J α hs ht v)⟫ : ℂ)) :=
    Complex.continuous_ofReal.comp ((weakDelta A J α hs ht).continuous.inner continuous_const)
  have hclosed : _root_.IsClosed {w : antiEnergy A J α hs ht |
      (ComplexMatrix.square EuclideanEnergy.e a b ρ (rawDistribution A J α hs ht D hD p τ w)
        (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      (⟪weakDelta A J α hs ht w, weakDelta A J α hs ht (antiToEnergy A J α hs ht v)⟫ : ℂ)} :=
    isClosed_eq hLc hRc
  refine (antiToEnergy_dense A J α hs ht).induction_on u hclosed ?_
  intro w
  rw [rawDistribution_smooth,square_component_apply,smooth_delta_pair]
  congr 1
  apply chart_energy_local J α hs ht p.val (D p) A w.val.property w.property hU hUD
    a b ρ ha hb hρ
    (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p w.val))
    q ?_ (componentTest_compact j φ hc) ((componentTest_support j φ).trans hφU)
  intro z hz
  exact cutoff_realPair_raw A J α ht D hD p w.val τ (hUD hz) (hτ z hz)

end TamingCompatibility.GeometricHilbert

end

end OAI
