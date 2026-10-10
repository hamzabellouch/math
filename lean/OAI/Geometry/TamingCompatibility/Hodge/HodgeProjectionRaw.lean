import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeDifferentialLocality

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge ManifoldLocalization ComplexMatrix HodgeFrame Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
omit [T2Space X] in
lemma realVectorSchwartz_antiInvariant (p : A.centers) (f : smoothForms X 2) (z : Space) :
    realVectorSchwartz A J α ht D hD p ⟨antiInvariantPart J f.val,IsSmooth.antiInvariantPart f.property J⟩ z =
      UnitaryFrame.antiInvariantPart (realVectorSchwartz A J α ht D hD p f z) := by
  by_cases hz : z ∈ (D p).domain
  · rw [realVectorSchwartz_raw A J α ht D hD p _ hz,
      realVectorSchwartz_raw A J α ht D hD p f hz,
      rawVector_antiInvariantPart J α ht p.val (D p) f.val hz]
    ext i
    fin_cases i <;> simp [UnitaryFrame.antiInvariantPart,UnitaryFrame.jAction] <;> ring
  · have hzero (a : smoothForms X 2) : realVectorSchwartz A J α ht D hD p a z = 0 := by
      ext i
      rw [realVectorSchwartz_apply]
      exact indicator_of_notMem hz _
    simp [hzero,UnitaryFrame.antiInvariantPart,UnitaryFrame.jAction]

omit [T2Space X] in
lemma scalarVectorLinear_antiInvariant (p : A.centers) (f : smoothForms X 2) :
    scalarVectorLinear A J α ht D hD p ⟨antiInvariantPart J f.val,IsSmooth.antiInvariantPart f.property J⟩ =
      SchwartzMap.postcompCLM antiMatrix (scalarVectorLinear A J α ht D hD p f) := by
  rw [← realVectorSchwartz_embed A J α ht D hD p f,
    ← realVectorSchwartz_embed A J α ht D hD p _]
  ext z i
  simp only [SchwartzMap.postcompCLM_apply,realVectorSchwartz_antiInvariant,antiMatrix_embed]
end TamingCompatibility.HodgeChart

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ComplexMatrix TemperedDistribution EuclideanSobolevOperators HilbertSobolev
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
omit [T2Space X] in
lemma hodgeRawDistribution_smooth_antiInvariant (p : A.centers) (τ : 𝓢(Space,ℝ))
    (f : PreL2 A J α hs ht true) :
    hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeSmooth A J α hs ht ⟨antiInvariantPart J f.val,IsSmooth.antiInvariantPart f.property J⟩) =
      fiberMap antiMatrix (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f)) := by
  change smulLeftCLM HodgeScalar.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
    (hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht _)) =
      fiberMap antiMatrix (smulLeftCLM HodgeScalar.F (SchwartzMap.postcompCLM Complex.ofRealCLM τ)
        (hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht f)))
  let fπ : PreL2 A J α hs ht true := ⟨antiInvariantPart J f.val,IsSmooth.antiInvariantPart f.property J⟩
  change smulLeftCLM _ _ (hodgeScalarDistribution A J α hs ht D hD p (hodgeSmooth A J α hs ht fπ)) = _
  rw [hodgeScalarDistribution_smooth A J α hs ht D hD p fπ,
    hodgeScalarDistribution_smooth A J α hs ht D hD p f,fiberMap_product,fiberMap_schwartz]
  congr 2
  exact scalarVectorLinear_antiInvariant A J α ht (fun p => (D p).toData) hD p f
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
variable (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (θ : 𝓢(Space,ℂ)) (hθ : ∀ z ∈ U, θ z * (ρ z : ℂ) = 1)

include hU hUD hτ ha hb hρ hθ

lemma hodge_laplacian_local_distribution (f : PreL2 A J α hs ht true) :
    LocallyEqual U
      (normalizedFullSquare a b ρ θ (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht f)))
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht (hodgeLaplacian A J α hs ht f))) := by
  intro χ hc hχU
  change smulLeftCLM (C 6) χ (smulLeftCLM (C 6) θ _) = _
  rw [coefficient_products_commute χ θ]
  refine (congrArg (smulLeftCLM (C 6) θ)
    (hodge_laplacian_weighted_distribution A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ f χ hc hχU)).trans ?_
  rw [coefficient_products_commute θ χ]
  exact triple_product_cancel χ θ (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
    (fun z hz => hθ z (hχU hz)) _

lemma hodge_laplacian_power_local_distribution
    (G : Fin 4 → Fin 4 → Space → ℝ)
    (hG : ∀ i j z, (ρ z • a i z).adjoint ∘L a j z + (ρ z • a j z).adjoint ∘L a i z =
        (2*G i j z) • ContinuousLinearMap.id ℝ (ComplexMatrix.R 6))
    (k : ℕ) (f : PreL2 A J α hs ht true) :
    LocallyEqual U
      (((normalizedFullSquare a b ρ θ)^k) (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht f)))
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht (((hodgeLaplacian A J α hs ht)^k) f))) := by
  induction k with
  | zero => exact LocallyEqual.refl _ _
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp,pow_succ' (hodgeLaplacian A J α hs ht) k]
    change LocallyEqual U _ (hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeSmooth A J α hs ht (hodgeLaplacian A J α hs ht (((hodgeLaplacian A J α hs ht)^k) f))))
    exact (normalizedFullSquare_local_congr a b ρ θ G hG hU ih).trans
      (hodge_laplacian_local_distribution A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ θ hθ _)
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open TemperedDistribution Set EuclideanEnergy
open scoped SchwartzMap
lemma LocallyEqual.cutoff_self {U : Set V} (ψ : 𝓢(V,ℂ))
    (hψ : ∀ z ∈ U, ψ z = 1) (u : 𝓢'(V,C 6)) :
    LocallyEqual U (smulLeftCLM (C 6) ψ u) u := by
  intro χ _ hc
  rw [smulLeftCLM_smulLeftCLM_apply ψ.hasTemperateGrowth χ.hasTemperateGrowth]
  have he : (ψ : V → ℂ) * χ = (χ : V → ℂ) := by
    ext z
    change ψ z * χ z = χ z
    by_cases hz : z ∈ tsupport χ
    · rw [hψ z (hc hz),one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz,mul_zero]
  rw [he]
lemma LocallyEqual.mono {U W : Set V} {u v : 𝓢'(V,C 6)}
    (h : LocallyEqual U u v) (hWU : W ⊆ U) : LocallyEqual W u v :=
  fun χ hc hχ => h χ hc (hχ.trans hWU)
end TamingCompatibility.ComplexMatrix
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
variable (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (θ : 𝓢(Space,ℂ)) (hθ : ∀ z ∈ U, θ z * (ρ z : ℂ) = 1)
    (G : Fin 4 → Fin 4 → Space → ℝ)
    (hG : ∀ i j z, (ρ z • a i z).adjoint ∘L a j z + (ρ z • a j z).adjoint ∘L a i z =
        (2*G i j z) • ContinuousLinearMap.id ℝ (ComplexMatrix.R 6))
include hU hUD hτ ha hb hρ hθ hG

lemma hodge_commutator_local_distribution (k : ℕ) (f : PreL2 A J α hs ht true) :
    LocallyEqual U
      ((((normalizedFullSquare a b ρ θ)^k)
        (fiberMap antiMatrix (hodgeRawDistribution A J α hs ht D hD p τ
          (hodgeSmooth A J α hs ht f)))) -
        fiberMap antiMatrix (((normalizedFullSquare a b ρ θ)^k)
          (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))))
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht (hodgePowerCommutator A J α hs ht k f))) := by
  have hpi (g : PreL2 A J α hs ht true) :
      hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht (preAntiProjection A J α hs ht g)) =
        fiberMap antiMatrix (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht g)) :=
    hodgeRawDistribution_smooth_antiInvariant A J α hs ht D hD p τ g
  have h1 := hodge_laplacian_power_local_distribution A J α hs ht D hD p τ hU hUD hτ
    a b ρ ha hb hρ θ hθ G hG k (preAntiProjection A J α hs ht f)
  have h2 := (hodge_laplacian_power_local_distribution A J α hs ht D hD p τ hU hUD hτ
    a b ρ ha hb hρ θ hθ G hG k f).fiberMap antiMatrix
  rw [hpi f] at h1
  simpa only [hodgePowerCommutator_apply,map_sub,hpi] using h1.sub h2
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
