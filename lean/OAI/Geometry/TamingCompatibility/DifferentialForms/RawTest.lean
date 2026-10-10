import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.ScalarRegularityBase
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexReal
import OAI.Geometry.TamingCompatibility.Functional.RawNormal

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)

lemma rawPair_manifoldTest {q : Space → EuclideanEnergy.Pair} (hqD : tsupport q ⊆ D.domain)
    {z : Space} (hz : z ∈ D.domain) :
    rawPair J α ht p D (manifoldTest J α ht p D q) z = q z := by
  have he : TamingCompatibility.pullback (manifoldTest J α ht p D q)
      (extChartAt Model p).symm z = coordinateTest J α ht p D q z :=
    pullback_manifoldTest J α ht p D hqD (D.domain_subset hz)
  unfold rawPair rawScalar
  rw [he]
  ext i
  fin_cases i <;>
    simp [EuclideanEnergy.pair,coordinateTest,frameTest,realPart_apply,imagPart_apply,
      D.frame_gram z hz]

lemma rawPair_manifoldTest_eventually {q : Space → EuclideanEnergy.Pair}
    (hqD : tsupport q ⊆ D.domain) {z : Space} (hz : z ∈ D.domain) :
    rawPair J α ht p D (manifoldTest J α ht p D q) =ᶠ[𝓝 z] q := by
  filter_upwards [D.domain_open.mem_nhds hz] with y hy
  exact rawPair_manifoldTest J α ht p D hqD hy

lemma normalOperator_test {q : Space → EuclideanEnergy.Pair}
    (hqD : tsupport q ⊆ D.domain) {z : Space} (hz : z ∈ D.domain) :
    normalOperator J α ht p D (rawPair J α ht p D (manifoldTest J α ht p D q)) z =
      normalOperator J α ht p D q z := by
  unfold normalOperator
  rw [(rawPair_manifoldTest_eventually J α ht p D hqD hz).fderiv_eq,
    rawPair_manifoldTest J α ht p D hqD hz]
end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def coordinateWeight (p : A.centers) (z : Space) : ℝ :=
  A.partition p ((extChartAt Model p.val).symm z)

omit [CompactSpace X] in
lemma coordinateWeight_smooth (p : A.centers) :
    ContDiffOn ℝ ∞ (coordinateWeight A p) (extChartAt Model p.val).target :=
  (A.partition p).contMDiff.comp_contMDiffOn
    (contMDiffOn_extChartAt_symm p.val) |>.contDiffOn

omit [CompactSpace X] in
lemma scalar_eq_weight (p : A.centers) (a : TwoForm X) (j : Fin 4)
    {z : Space} (hz : z ∈ (D p).domain) :
    scalar A J α ht D p a j z = coordinateWeight A p z * rawScalar J α ht p.val (D p) a j z := by
  unfold scalar localizedFunction
  rw [indicator_of_mem hz,indicator_of_mem ((D p).domain_subset hz)]
  rfl

def realPairSchwartz (p : A.centers) (a : smoothForms X 2) : 𝓢(Space,EuclideanEnergy.Pair) :=
  SchwartzMap.postcompCLM (retract 2) (pairLinear A J α ht D hD p a)

lemma realPairSchwartz_apply (p : A.centers) (a : smoothForms X 2) (z : Space) :
    realPairSchwartz A J α ht D hD p a z =
      EuclideanEnergy.pair (scalar A J α ht D p a.val 2 z) (scalar A J α ht D p a.val 3 z) := by
  ext i
  fin_cases i <;> simp [realPairSchwartz,pairLinear_eq_make,ScalarPair.make_apply,EuclideanEnergy.pair] <;> rfl

lemma realPairSchwartz_embed (p : A.centers) (a : smoothForms X 2) :
    SchwartzMap.postcompCLM (embed 2) (realPairSchwartz A J α ht D hD p a) =
      pairLinear A J α ht D hD p a := by
  ext z i
  fin_cases i <;> simp [realPairSchwartz_apply,pairLinear_eq_make,ScalarPair.make_apply,EuclideanEnergy.pair] <;> rfl

lemma realPairSchwartz_raw (p : A.centers) (a : smoothForms X 2)
    {z : Space} (hz : z ∈ (D p).domain) :
    realPairSchwartz A J α ht D hD p a z =
      coordinateWeight A p z • rawPair J α ht p.val (D p) a.val z := by
  rw [realPairSchwartz_apply,scalar_eq_weight A J α ht D p a.val 2 hz,
    scalar_eq_weight A J α ht D p a.val 3 hz]
  ext i
  fin_cases i <;> rfl

lemma cutoff_realPair_raw (p : A.centers) (a : smoothForms X 2) (τ : 𝓢(Space,ℝ))
    {z : Space} (hz : z ∈ (D p).domain) (hτ : τ z * coordinateWeight A p z = 1) :
    SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a) z =
      rawPair J α ht p.val (D p) a.val z := by
  rw [SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth]
  rw [realPairSchwartz_raw A J α ht D hD p a hz,smul_smul,hτ,one_smul]
end TamingCompatibility.GeometricChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart MeasureTheory ComplexMatrix
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma scalarDistribution_smooth (p : A.centers) (a : antiPre A J α hs ht) :
    scalarDistribution A J α hs ht D hD p (antiToEnergy A J α hs ht a) =
      (pairLinear A J α ht D hD p a.val : 𝓢'(Space,ScalarPair.F)) := by
  change ScalarPair.jetDistribution none
    (energyToScalarJet A J α hs ht D hD p (antiToEnergy A J α hs ht a)) = _
  rw [energyToScalarJet_smooth]
  exact ScalarPair.jetDistribution_jet _ none

def rawDistribution (p : A.centers) (τ : 𝓢(Space,ℝ)) :
    antiEnergy A J α hs ht →L[ℝ] 𝓢'(Space,ScalarPair.F) :=
  (smulLeftCLM ScalarPair.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)).restrictScalars ℝ ∘L
    scalarDistribution A J α hs ht D hD p

lemma rawDistribution_H1 (p : A.centers) (τ : 𝓢(Space,ℝ)) (u : antiEnergy A J α hs ht) :
    MemSobolev 1 2 (rawDistribution A J α hs ht D hD p τ u) := by
  change MemSobolev 1 2 (smulLeftCLM ScalarPair.F
    (SchwartzMap.postcompCLM Complex.ofRealCLM τ) (scalarDistribution A J α hs ht D hD p u))
  have hu := scalarDistribution_H1 A J α hs ht D hD p u
  simpa only [Nat.cast_one] using
    (EuclideanSobolevOperators.memSobolev_nat_product (E := Space) (F := ScalarPair.F) 1
      (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
      (u := scalarDistribution A J α hs ht D hD p u) (by simpa only [Nat.cast_one] using hu))

lemma rawDistribution_smooth (p : A.centers) (τ : 𝓢(Space,ℝ)) (a : antiPre A J α hs ht) :
    rawDistribution A J α hs ht D hD p τ (antiToEnergy A J α hs ht a) =
      (SchwartzMap.postcompCLM (embed 2)
        (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a.val)) :
          𝓢'(Space,ScalarPair.F)) := by
  change smulLeftCLM ScalarPair.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
    (scalarDistribution A J α hs ht D hD p (antiToEnergy A J α hs ht a)) = _
  rw [scalarDistribution_smooth,product_schwartz]
  congr 1
  rw [← realPairSchwartz_embed A J α ht D hD p a.val]
  ext z i
  simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM τ).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply τ.hasTemperateGrowth,SchwartzMap.postcompCLM_apply,embed_apply,
    PiLp.smul_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
