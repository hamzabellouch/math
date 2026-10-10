import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeScalarJet

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ComplexMatrix Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
omit [CompactSpace X] in
lemma scalar_eq_weight (p : A.centers) (a : TwoForm X) (j : Fin 6)
    {z : Space} (hz : z ∈ (D p).domain) :
    scalar A J α ht D p a j z = coordinateWeight A p z * rawVector J α ht p.val (D p) a z j := by
  unfold scalar localizedFunction
  rw [indicator_of_mem hz,indicator_of_mem ((D p).domain_subset hz)]
  rfl

def realVectorSchwartz (p : A.centers) (a : smoothForms X 2) : 𝓢(Space,HodgeNormalSymbol.W) :=
  SchwartzMap.postcompCLM (retract 6) (scalarVectorLinear A J α ht D hD p a)
lemma realVectorSchwartz_apply (p : A.centers) (a : smoothForms X 2) (z : Space) (i : Fin 6) :
    realVectorSchwartz A J α ht D hD p a z i = scalar A J α ht D p a.val i z := by
  simp only [realVectorSchwartz,SchwartzMap.postcompCLM_apply,scalarVectorLinear_eq_make,
    retract_apply,HodgeScalar.make_apply,Complex.ofReal_re]
  rfl
lemma realVectorSchwartz_embed (p : A.centers) (a : smoothForms X 2) :
    SchwartzMap.postcompCLM (embed 6) (realVectorSchwartz A J α ht D hD p a) =
      scalarVectorLinear A J α ht D hD p a := by
  ext z i
  simp only [SchwartzMap.postcompCLM_apply,embed_apply,realVectorSchwartz_apply,
    scalarVectorLinear_eq_make,HodgeScalar.make_apply]
  rfl
lemma realVectorSchwartz_raw (p : A.centers) (a : smoothForms X 2)
    {z : Space} (hz : z ∈ (D p).domain) :
    realVectorSchwartz A J α ht D hD p a z = coordinateWeight A p z • rawVector J α ht p.val (D p) a.val z := by
  ext i
  rw [realVectorSchwartz_apply,scalar_eq_weight A J α ht D p a.val i hz]
  rfl
lemma cutoff_realVector_raw (p : A.centers) (a : smoothForms X 2) (τ : 𝓢(Space,ℝ))
    {z : Space} (hz : z ∈ (D p).domain) (hτ : τ z * coordinateWeight A p z = 1) :
    SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ (realVectorSchwartz A J α ht D hD p a) z =
      rawVector J α ht p.val (D p) a.val z := by
  rw [SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,
    realVectorSchwartz_raw A J α ht D hD p a hz,smul_smul,hτ,one_smul]
end TamingCompatibility.HodgeChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart MeasureTheory ComplexMatrix
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
lemma hodgeRawDistribution_smooth (p : A.centers) (τ : 𝓢(Space,ℝ)) (a : PreL2 A J α hs ht true) :
    hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht a) =
      (SchwartzMap.postcompCLM (embed 6)
        (SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ
          (realVectorSchwartz A J α ht (fun q => (D q).toData) hD p a)) : 𝓢'(Space,HodgeScalar.F)) := by
  change smulLeftCLM HodgeScalar.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
    (hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht a)) = _
  rw [hodgeScalarDistribution_smooth,product_schwartz]
  congr 1
  rw [← realVectorSchwartz_embed A J α ht (fun q => (D q).toData) hD p a]
  ext z i
  simp only [SchwartzMap.smulLeftCLM_apply (SchwartzMap.postcompCLM Complex.ofRealCLM τ).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply τ.hasTemperateGrowth,SchwartzMap.postcompCLM_apply,embed_apply,
    PiLp.smul_apply,Complex.ofRealCLM_apply,smul_eq_mul,Complex.ofReal_mul]
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
def hodgeTest (p : A.centers) (q : 𝓢(Space,HodgeNormalSymbol.W))
    (hc : HasCompactSupport (q : Space → _)) (hqD : tsupport q ⊆ (D p).domain) : PreL2 A J α hs ht true :=
  ⟨manifoldTest J α ht p.val (D p).toData q,
    manifoldTest_smooth J α hs ht p.val (D p).toData (q.smooth ⊤) hc hqD⟩
lemma full_componentTest_support (j : Fin 6) (φ : 𝓢(Space,ℝ)) :
    tsupport (componentTest j φ) ⊆ tsupport φ :=
  tsupport_smul_subset_left (φ : Space → ℝ) (fun _ : Space => EuclideanSpace.single j (1:ℝ))
lemma full_componentTest_compact (j : Fin 6) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) : HasCompactSupport (componentTest j φ : Space → _) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (full_componentTest_support j φ)
omit [T2Space X] in
lemma hodge_smooth_energy_pair (u v : PreL2 A J α hs ht true) :
    ⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht u),
      hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht v)⟫ =
      ∫ x, energyPairing J α ht u.val v.val x ∂geometricVolume A J α := by
  let := geometricVolume_finite A J α hs ht
  change ⟪WithLp.toLp 2 (smoothL2 A J α hs ht false (hodgeDelta A J α hs ht u),
      smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht u))),
    WithLp.toLp 2 (smoothL2 A J α hs ht false (hodgeDelta A J α hs ht v),
      smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht v)))⟫ = _
  rw [WithLp.prod_inner_apply,(smoothL2 A J α hs ht false).inner_map_map,
    (smoothL2 A J α hs ht false).inner_map_map,preL2_inner,preL2_inner]
  symm
  apply integral_add
  · exact (GeometricAdjoint.pairing_one_smooth J α hs ht
      (GeometricAdjoint.codifferential_smooth J α hs ht u.property)
      (GeometricAdjoint.codifferential_smooth J α hs ht v.property)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · exact (GeometricAdjoint.pairing_one_smooth J α hs ht
      (GeometricAdjoint.codifferential_smooth J α hs ht (starTwo_smooth J α hs ht u.property))
      (GeometricAdjoint.codifferential_smooth J α hs ht (starTwo_smooth J α hs ht v.property))).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

lemma hodge_raw_square_energy_smooth (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) (w : PreL2 A J α hs ht true) :
    (ComplexMatrix.square EuclideanEnergy.e a b ρ (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht w))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      (⟪hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht w),hodgeWeakDerivative A J α hs ht
        (hodgeSmooth A J α hs ht (hodgeTest A J α hs ht D p (componentTest j φ)
          (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  rw [hodgeRawDistribution_smooth,square_component_apply,hodge_smooth_energy_pair]
  congr 1
  apply chart_energy_local J α hs ht p.val (D p).toData A w.property hU hUD
    a b ρ ha hb hρ
    (SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ
      (realVectorSchwartz A J α ht (fun q => (D q).toData) hD p w))
    (componentTest j φ) ?_ (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans hφU)
  intro z hz
  exact cutoff_realVector_raw A J α ht (fun q => (D q).toData) hD p w τ (hUD hz) (hτ z hz)

lemma hodge_raw_square_energy (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
    (j : Fin 6) (u : hodgeEnergy A J α hs ht) :
    (ComplexMatrix.square EuclideanEnergy.e a b ρ (hodgeRawDistribution A J α hs ht D hD p τ u)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      (⟪hodgeWeakDerivative A J α hs ht u,hodgeWeakDerivative A J α hs ht
        (hodgeSmooth A J α hs ht (hodgeTest A J α hs ht D p (componentTest j φ)
          (full_componentTest_compact j φ hc) ((full_componentTest_support j φ).trans (hφU.trans hUD))))⟫ : ℂ) := by
  let q := componentTest j φ
  let v := hodgeTest A J α hs ht D p q (full_componentTest_compact j φ hc)
    ((full_componentTest_support j φ).trans (hφU.trans hUD))
  have hLc : Continuous (fun w => (ComplexMatrix.square EuclideanEnergy.e a b ρ
      (hodgeRawDistribution A J α hs ht D hD p τ w)
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j) := by
    generalize hodgeRawDistribution A J α hs ht D hD p τ = L
    generalize ComplexMatrix.square EuclideanEnergy.e a b ρ = P
    exact continuous_system_eval L P (SchwartzMap.postcompCLM Complex.ofRealCLM φ) j
  have hRc : Continuous (fun w => (⟪hodgeWeakDerivative A J α hs ht w,
      hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht v)⟫ : ℂ)) :=
    Complex.continuous_ofReal.comp ((hodgeWeakDerivative A J α hs ht).continuous.inner continuous_const)
  have hclosed : _root_.IsClosed {w : hodgeEnergy A J α hs ht |
      (ComplexMatrix.square EuclideanEnergy.e a b ρ (hodgeRawDistribution A J α hs ht D hD p τ w)
        (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      (⟪hodgeWeakDerivative A J α hs ht w,
        hodgeWeakDerivative A J α hs ht (hodgeSmooth A J α hs ht v)⟫ : ℂ)} := isClosed_eq hLc hRc
  refine (hodgeSmooth_dense A J α hs ht).induction_on u hclosed ?_
  intro w
  exact hodge_raw_square_energy_smooth A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ φ hc hφU j w

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
