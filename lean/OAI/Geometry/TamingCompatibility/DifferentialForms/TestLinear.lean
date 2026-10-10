import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.WeakNormalEquation

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set
open scoped Manifold
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] {k : ℕ}
lemma chartLift_add (p : X) (a b : Space → Space [⋀^Fin k]→L[ℝ] ℝ) :
    chartLift p (a+b) = chartLift p a + chartLift p b := by
  classical
  funext x
  simp only [chartLift,Pi.add_apply]
  split_ifs
  · rfl
  · simp
end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)
lemma coordinateTest_add (q r : Space → EuclideanEnergy.Pair) :
    coordinateTest J α ht p D (q+r) = coordinateTest J α ht p D q + coordinateTest J α ht p D r := by
  funext z
  simp only [coordinateTest,frameTest,Pi.add_apply,PiLp.add_apply,add_smul]
  module
lemma manifoldTest_add (q r : Space → EuclideanEnergy.Pair) :
    manifoldTest J α ht p D (q+r) = manifoldTest J α ht p D q + manifoldTest J α ht p D r := by
  rw [manifoldTest,coordinateTest_add,chartLift_add,antiInvariantPart_add]
  rfl
end TamingCompatibility.GeometricChart

namespace TamingCompatibility.ComplexMatrix
open Set
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def realComponent {n : ℕ} (q : 𝓢(E,R n)) (j : Fin n) : 𝓢(E,ℝ) :=
  SchwartzMap.postcompCLM (EuclideanSpace.proj j) q
@[simp] lemma realComponent_apply {n : ℕ} (q : 𝓢(E,R n)) (j : Fin n) (x : E) :
    realComponent q j x = q x j := rfl
lemma realComponent_support {n : ℕ} (q : 𝓢(E,R n)) (j : Fin n) :
    tsupport (realComponent q j) ⊆ tsupport q :=
  tsupport_comp_subset (map_zero (EuclideanSpace.proj (𝕜 := ℝ) j)) q
lemma pair_decompose (q : 𝓢(E,R 2)) :
    (q : E → R 2) = componentTest (0 : Fin 2) (realComponent q 0) + componentTest (1 : Fin 2) (realComponent q 1) := by
  ext x j
  fin_cases j <;> simp [componentTest_apply,EuclideanSpace.single]
end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)

lemma pair_all_tests_eq (p : A.centers) {U : Set Space} (hUD : U ⊆ (D p).domain)
    (u v : L2 A J α hs ht true)
    (h : ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
      (hφU : tsupport φ ⊆ U) (j : Fin 2),
      ⟪u,smoothL2 A J α hs ht true
        (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
          ((componentTest_support j φ).trans (hφU.trans hUD))).val⟫ =
      ⟪v,smoothL2 A J α hs ht true
        (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
          ((componentTest_support j φ).trans (hφU.trans hUD))).val⟫)
    (q : 𝓢(Space,EuclideanEnergy.Pair)) (hc : HasCompactSupport (q : Space → EuclideanEnergy.Pair))
    (hqU : tsupport q ⊆ U) :
    ⟪u,smoothL2 A J α hs ht true (testAnti A J α hs ht D p q hc (hqU.trans hUD)).val⟫ =
    ⟪v,smoothL2 A J α hs ht true (testAnti A J α hs ht D p q hc (hqU.trans hUD)).val⟫ := by
  let φ (j : Fin 2) := realComponent q j
  have hφc (j : Fin 2) : HasCompactSupport (φ j : Space → ℝ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (realComponent_support q j)
  have hφU (j : Fin 2) : tsupport (φ j) ⊆ U := (realComponent_support q j).trans hqU
  let w (j : Fin 2) := testAnti A J α hs ht D p (componentTest j (φ j))
    (componentTest_compact j (φ j) (hφc j)) ((componentTest_support j (φ j)).trans ((hφU j).trans hUD))
  have he : testAnti A J α hs ht D p q hc (hqU.trans hUD) = w 0 + w 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change manifoldTest J α ht p.val (D p) q =
      manifoldTest J α ht p.val (D p) (componentTest 0 (φ 0)) +
      manifoldTest J α ht p.val (D p) (componentTest 1 (φ 1))
    rw [← manifoldTest_add]
    exact congrArg (manifoldTest J α ht p.val (D p)) (pair_decompose q)
  rw [he]
  change ⟪u,smoothL2 A J α hs ht true ((w 0).val + (w 1).val)⟫ =
    ⟪v,smoothL2 A J α hs ht true ((w 0).val + (w 1).val)⟫
  rw [map_add,inner_add_right,inner_add_right]
  exact congrArg₂ (·+·) (h (φ 0) (hφc 0) (hφU 0) 0) (h (φ 1) (hφc 1) (hφU 1) 1)

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
