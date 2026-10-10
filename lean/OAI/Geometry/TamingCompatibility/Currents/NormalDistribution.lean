import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.LocalFormalAdjoint
import OAI.Geometry.TamingCompatibility.Functional.RawNormal

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume LocalFormalAdjoint
open Set Filter MeasureTheory LineDeriv
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma firstOrder_local (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (s : 𝓢(Space,EuclideanEnergy.Pair))
    (f : Space → EuclideanEnergy.Pair) {z : Space} (he : (s : Space → _) =ᶠ[𝓝 z] f)
    (ha : ∀ i, a i z = normalA J α ht p D i z) (hb : b z = normalB J α ht p D z) :
    firstOrder EuclideanEnergy.e a b s z = normalOperator J α ht p D f z := by
  simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    multiply_apply,lineDerivOpCLM_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,
    ha,hb,he.fderiv_eq,he.eq_of_nhds,normalOperator]

lemma firstOrder_zero_off (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (q : 𝓢(Space,EuclideanEnergy.Pair))
    {z : Space} (hz : z ∉ tsupport q) : firstOrder EuclideanEnergy.e a b q z = 0 := by
  have hd (i : Fin 4) : (∂_{EuclideanEnergy.e i} q : 𝓢(Space,EuclideanEnergy.Pair)) z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))
  simp only [firstOrder,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    multiply_apply,lineDerivOpCLM_apply,hd,image_eq_zero_of_notMem_tsupport hz,map_zero,
    Finset.sum_const_zero,add_zero]

variable [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X)
include hs in
lemma chart_energy_local {u : TwoForm X} (hu : IsSmooth u) (hanti : antiInvariantPart J u = u)
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ D.domain)
    (a : Fin 4 → 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space))
    (b : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p D i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p D z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p z)
    (s q : 𝓢(Space,EuclideanEnergy.Pair))
    (hsU : ∀ z ∈ U, s z = rawPair J α ht p D u z)
    (hqc : HasCompactSupport (q : Space → _)) (hqU : tsupport q ⊆ U) :
    (∫ z, ρ z * ⟪firstOrder EuclideanEnergy.e a b s z,firstOrder EuclideanEnergy.e a b q z⟫) =
      ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht u)
        (codifferential J α ht (manifoldTest J α ht p D q)) x ∂geometricVolume A J α := by
  rw [normal_energy_integral J α ht p D hs A hu hanti (q.smooth ⊤) hqc (hqU.trans hUD)]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport q
  · have hzU := hqU hz
    have he : (s : Space → _) =ᶠ[𝓝 z] rawPair J α ht p D u := by
      filter_upwards [hU.mem_nhds hzU] with y hy
      exact hsU y hy
    rw [firstOrder_local J α ht p D a b s _ he (ha z hzU) (hb z hzU),
      firstOrder_local J α ht p D a b q q Filter.EventuallyEq.rfl (ha z hzU) (hb z hzU),hρ z hzU]
  · rw [firstOrder_zero_off a b q hz,normalOperator_zero_off J α ht p D q hz]
    simp
end TamingCompatibility.GeometricChart

end

end OAI
