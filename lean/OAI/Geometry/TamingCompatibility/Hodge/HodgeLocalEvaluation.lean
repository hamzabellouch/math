import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeRawRegular
import OAI.Geometry.TamingCompatibility.Elliptic.RealSobolevLift

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

def hodgeLocalizedRegularization (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (r : ℝ) (hr : 0 < r) : L2 A J α hs ht true →L[ℝ] 𝓢'(Space,C 6) :=
  ((smulLeftCLM (C 6) χ).restrictScalars ℝ).comp
    ((hodgeRawDistribution A J α hs ht D hD p τ).comp (hodgeRegularizedGraph A J α hs ht r hr))

structure LocalHodgeSmoothing (p : A.centers) (q : Space) (r : ℝ) (hr : 0 < r) where
  reciprocal : 𝓢(Space,ℝ)
  cutoff : 𝓢(Space,ℂ)
  neighborhood : Set Space
  neighborhood_open : IsOpen neighborhood
  center_mem : q ∈ neighborhood
  neighborhood_subset : neighborhood ⊆ (D p).domain
  reciprocal_eq : ∀ z ∈ neighborhood, reciprocal z * coordinateWeight A p z = 1
  cutoff_eq : ∀ z ∈ neighborhood, cutoff z = 1
  lift : L2 A J α hs ht true →L[ℝ] H Space (C 6) 5
  lift_spec : ∀ f, toDistribution Space (C 6) 5 (lift f) =
    hodgeLocalizedRegularization A J α hs ht D hD p reciprocal cutoff r hr f

lemma exists_localHodgeSmoothing (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0)
    (r : ℝ) (hr : 0 < r) : Nonempty (LocalHodgeSmoothing A J α hs ht D hD p q r hr) := by
  obtain ⟨τ,V,hV,hqV,hVD,hτ,hreg⟩ := hodgeRegularization_raw_H5 A J α hs ht D hD p q hq hwq r hr
  obtain ⟨φ,hφ,hφV,U,hU,hqU,hUV,hφone⟩ := SchwartzCutoff.exists_one_near hV hqV
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM φ
  have hχs : tsupport (χ : Space → ℂ) ⊆ tsupport φ :=
    tsupport_comp_subset (map_zero Complex.ofRealCLM) φ
  have hχc : HasCompactSupport (χ : Space → ℂ) :=
    hφ.of_isClosed_subset (isClosed_tsupport χ) hχs
  have hχV : tsupport (χ : Space → ℂ) ⊆ V := hχs.trans hφV
  let L := hodgeLocalizedRegularization A J α hs ht D hD p τ χ r hr
  have hL : ∀ f, MemSobolev 5 2 (L f) := fun f => hreg f χ hχc hχV
  exact ⟨{
    reciprocal := τ
    cutoff := χ
    neighborhood := U
    neighborhood_open := hU
    center_mem := hqU
    neighborhood_subset := hUV.trans hVD
    reciprocal_eq := fun z hz => hτ z (hUV hz)
    cutoff_eq := fun z hz => by simp only [χ,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,hφone z hz,Complex.ofReal_one]
    lift := realSobolevLift 5 L hL
    lift_spec := realSobolevLift_spec 5 L hL }⟩

def localHodgeSmoothing (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0)
    (r : ℝ) (hr : 0 < r) : LocalHodgeSmoothing A J α hs ht D hD p q r hr :=
  Classical.choice (exists_localHodgeSmoothing A J α hs ht D hD p q hq hwq r hr)

namespace LocalHodgeSmoothing
variable {A J α hs ht D hD} {p : A.centers} {q : Space} {r : ℝ} {hr : 0 < r}
variable (L : LocalHodgeSmoothing A J α hs ht D hD p q r hr)

def evaluation (z : Space) : L2 A J α hs ht true →L[ℝ] C 6 :=
  ((sobolevEval 5 (by norm_num [Space]) z).restrictScalars ℝ).comp L.lift

omit [T2Space X] in
lemma evaluation_continuous : Continuous L.evaluation := by
  have h := sobolevEval_continuous (E := Space) (F := C 6) 5 (by norm_num [Space])
  exact ((ContinuousLinearMap.restrictScalarsL ℂ (H Space (C 6) 5) (C 6) ℝ ℝ).continuous.comp h).clm_comp continuous_const

def representative (f : L2 A J α hs ht true) : Space →ᵇ C 6 :=
  sobolevToBounded 5 (by norm_num [Space]) (L.lift f)

omit [T2Space X] in
lemma evaluation_apply (z : Space) (f : L2 A J α hs ht true) :
    L.evaluation z f = L.representative f z := rfl

omit [T2Space X] in
lemma representative_spec (f : L2 A J α hs ht true) :
    boundedDistribution (L.representative f) =
      hodgeLocalizedRegularization A J α hs ht D hD p L.reciprocal L.cutoff r hr f := by
  rw [representative,sobolevToBounded_spec,L.lift_spec]
end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
