import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeProjectionRaw
import OAI.Geometry.TamingCompatibility.Hodge.HodgeLocalCoefficients

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

lemma hodge_commutator_uniform_local_bound (k : ℕ) (hk : k ≤ 2) (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ U →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
          ∃ T : L2 A J α hs ht true →L[ℝ] H Space (C 6) 0,
            (∀ f : PreL2 A J α hs ht true,
              toDistribution Space (C 6) 0
                (T (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f))) =
                smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
                  (hodgeSmooth A J α hs ht (hodgePowerCommutator A J α hs ht (k+1) f)))) ∧
            ∀ v, ‖T v‖ ≤ B * (r⁻¹)^(2*k+1) * ‖v‖ := by
  obtain ⟨τ,ψ,V,hV,hqV,hVD,hτ,hψ,B,hB,hreg⟩ :=
    hodgeRegularization_uniform_local_odd A J α hs ht D hD k hk p q hq hwq
  obtain ⟨U,hU,hqU,hUV,a,b,ρ,θ,G,ha,hb,hρ,hθ,hG⟩ :=
    exists_hodge_local_coefficients A J α hs ht D p hV hVD q hqV
  refine ⟨τ,U,hU,hqU,hUV.trans hVD,fun z hz => hτ z (hUV hz),?_⟩
  intro χ hc hχ
  let N : H Space (C 6) (2*k+1:ℕ) →L[ℝ] H Space (C 6) 0 :=
    normalizedFullSquare_power_commutator_lift k 0 a b ρ θ G hG antiMatrix
  let P : H Space (C 6) 0 →L[ℝ] H Space (C 6) 0 :=
    (HilbertSobolev.product (F := C 6) 0 χ).restrictScalars ℝ
  refine ⟨‖P‖*‖N‖*B,mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hB,?_⟩
  intro r hr hr1
  obtain ⟨L,hL,hLb⟩ := hreg r hr hr1
  refine ⟨P.comp (N.comp L),?_,?_⟩
  · intro f
    generalize hv0 : smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f) = v
    have hv : hodgeRegularizedGraph A J α hs ht r hr v = hodgeSmooth A J α hs ht f := by
      rw [← hv0]
      exact hodgeRegularizedGraph_smoothShift_cube A J α hs ht r hr f
    have hLv := hL v
    rw [hv] at hLv
    have hcut := LocallyEqual.cutoff_self ψ (fun z hz => hψ z (hUV hz))
      (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))
    have h1 := normalizedFullSquare_power_local_congr a b ρ θ G hG hU (k+1)
      (hcut.fiberMap antiMatrix)
    have h2 := (normalizedFullSquare_power_local_congr a b ρ θ G hG hU (k+1) hcut).fiberMap antiMatrix
    have he := (h1.sub h2).trans
      (hodge_commutator_local_distribution A J α hs ht D hD p τ hU (hUV.trans hVD)
        (fun z hz => hτ z (hUV hz)) a b ρ ha hb hρ θ hθ G hG (k+1) f)
    dsimp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',P,N]
    clear_value P N
    generalize hu0 : hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeSmooth A J α hs ht f) = u at he hLv
    generalize hw0 : hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeSmooth A J α hs ht (hodgePowerCommutator A J α hs ht (k+1) f)) = w at he ⊢
    have heχ := he χ hc hχ
    have hs' := normalized_commutator_localized_spec (m := 8) k a b ρ θ G hG antiMatrix χ (L v)
      (smulLeftCLM (C 6) ψ u) _ hLv rfl
    generalize hE : normalizedFullSquare a b ρ θ = E at hs' heχ
    generalize hM : fiberMap (E := Space) antiMatrix = M at hs' heχ
    generalize hz : normalizedFullSquare_power_commutator_lift k 0 a b ρ θ G hG antiMatrix (L v) = z at hs' ⊢
    have hfinal := hs'.trans heχ
    exact hfinal
  · clear_value P N
    exact bounded_triple_composition P N L B ((r⁻¹)^(2*k+1)) hLb
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
lemma embed_norm_sq {n : ℕ} (v : R n) : ‖embed n v‖^2 = ‖v‖^2 := by
  simp only [PiLp.norm_sq_eq_of_L2,embed_apply,Complex.norm_real,Real.norm_eq_abs]
end TamingCompatibility.ComplexMatrix
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldHodge ManifoldVolume GeometricChart HodgeFrame
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X)
  (D : GeometricChart.Data J α ht p)
lemma rawVector_norm_sq (a : TwoForm X) {z : Space} (hz : z ∈ D.domain) :
    ‖rawVector J α ht p D a z‖^2 =
      GeometricAdjoint.pairing J α ht a a ((extChartAt Model p).symm z) := by
  rw [← real_inner_self_eq_norm_sq]
  change ⟪coordinates (fun i => D.frame i z) _,coordinates (fun i => D.frame i z) _⟫ = _
  rw [coordinates_pairing (coordinateMetric J α ht p z) (by simp [Space]) _ (D.frame_gram z hz),
    pairing_chart J α ht p (Or.inr rfl) a a (D.domain_subset hz)]
end TamingCompatibility.HodgeChart
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

def hodgeRawSchwartz (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (f : PreL2 A J α hs ht true) : 𝓢(Space,C 6) :=
  SchwartzMap.smulLeftCLM (C 6) χ
    (SchwartzMap.postcompCLM (embed 6) (SchwartzMap.smulLeftCLM HodgeNormalSymbol.W τ
      (realVectorSchwartz A J α ht (fun p => (D p).toData) hD p f)))

lemma hodgeRawSchwartz_spec (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (f : PreL2 A J α hs ht true) :
    (hodgeRawSchwartz A J α hs ht D hD p τ χ f : 𝓢'(Space,C 6)) =
      smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f)) := by
  rw [hodgeRawDistribution_smooth,product_schwartz]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma hodgeRawSchwartz_norm_sq (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    {U : Set Space} (hU : U ⊆ (D p).domain)
    (hχ : tsupport χ ⊆ U) (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (f : PreL2 A J α hs ht true) (z : Space) :
    ‖hodgeRawSchwartz A J α hs ht D hD p τ χ f z‖^2 =
      ‖χ z‖^2 * ‖rawVector J α ht p.val (D p).toData f.val z‖^2 := by
  rw [hodgeRawSchwartz,SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
    SchwartzMap.postcompCLM_apply]
  rw [norm_smul,mul_pow,embed_norm_sq]
  by_cases hz : z ∈ tsupport χ
  · rw [cutoff_realVector_raw A J α ht (fun p => (D p).toData) hD p f τ
      (hU (hχ hz)) (hτ z (hχ hz))]
  · rw [image_eq_zero_of_notMem_tsupport hz,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_mul]

lemma hodgeRawSchwartz_H0_norm_sq (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    {U : Set Space} (hU : U ⊆ (D p).domain)
    (hχ : tsupport χ ⊆ U) (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (f : PreL2 A J α hs ht true) (u : H Space (C 6) 0)
    (hu : toDistribution Space (C 6) 0 u =
      smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))) :
    ‖u‖^2 = ∫ z, ‖χ z‖^2 * ‖rawVector J α ht p.val (D p).toData f.val z‖^2 := by
  have he : u = schwartzToH 0 (hodgeRawSchwartz A J α hs ht D hD p τ χ f) := by
    apply toDistribution_injective 0
    rw [hu,schwartzToH_spec,hodgeRawSchwartz_spec]
  rw [he,schwartzToH_zero,GeometricChart.schwartz_l2_norm_sq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (hodgeRawSchwartz_norm_sq A J α hs ht D hD p τ χ hU hχ hτ f)
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
