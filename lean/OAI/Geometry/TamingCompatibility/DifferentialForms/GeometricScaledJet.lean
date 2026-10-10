import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.ScaledDual
import OAI.Geometry.TamingCompatibility.DifferentialForms.RawJetEstimate

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator GeometricAdjoint Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

include hs in

lemma ddstar_scaled_jet_bound (L : Space ≃L[ℝ] Space) {K : Set Space}
    (hK : IsCompact K) (hKD : K ⊆ D.domain) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (a : TwoForm X), IsSmooth a → antiInvariantPart J a = a →
      ∀ (U : Set Space), IsOpen U → U ⊆ D.domain →
      ∀ (u : 𝓢(Space,C 2)), (∀ z ∈ U, rawPair J α ht p D a z = retract 2 (u z)) →
      ∀ (z : Space), z ∈ U → z ∈ K → ∀ (r M : ℝ), 0 < r → r ≤ 1 →
      (let v := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm u
       r*‖v (L z)‖ + r^2*∑ i, ‖(∂_{EuclideanEnergy.e i} v) (L z)‖ +
         r^3*∑ i, ∑ j, ‖(∂_{EuclideanEnergy.e j} (∂_{EuclideanEnergy.e i} v)) (L z)‖ ≤ M) →
      r^3*‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht a))
        (extChartAt Model p).symm z‖ ≤ C₀*M := by
  obtain ⟨B,hB,hbound⟩ := JetOperator.exteriorJet_bounded D.domain_open hK hKD
    (deltaComplexA J α ht p D) (deltaComplexB J α ht p D)
    (deltaComplexA_smooth J α hs ht p D) (deltaComplexB_smooth J α hs ht p D)
  let T := JetOperator.linearTransport L (F := C 2)
  refine ⟨B*‖T‖,mul_nonneg hB (norm_nonneg _),fun a ha hanti U hU hUD u hrep z hz hzK r M hr hr1 hj => ?_⟩
  have hM : 0 ≤ M := by
    apply le_trans _ hj
    positivity
  rw [ddstar_local_jet J α hs ht p D ha hanti hU hUD u hrep hz]
  apply (JetOperator.linear_output_scaled_bound
    (JetOperator.exteriorJet (deltaComplexA J α ht p D) (deltaComplexB J α ht p D) z)
    L u z hr hr1 hj).trans
  apply mul_le_mul_of_nonneg_right _ hM
  exact (ContinuousLinearMap.opNorm_comp_le _ T).trans
    (mul_le_mul_of_nonneg_right (hbound z hzK) (norm_nonneg T))
end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma localizedRawSchwartz_raw (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) {z : Space} (hz : z ∈ (D p).domain)
    (hτ : τ z * coordinateWeight A p z = 1) (hχ : χ z = 1) :
    retract 2 (localizedRawSchwartz A J α hs ht D hD p τ χ a z) =
      rawPair J α ht p.val (D p) a.val.val z := by
  simp only [localizedRawSchwartz,SchwartzMap.smulLeftCLM_apply χ.hasTemperateGrowth,hχ,one_smul,
    SchwartzMap.postcompCLM_apply,retract_embed]
  exact cutoff_realPair_raw A J α ht D hD p a.val τ hz hτ

include hD in

lemma ddstar_coordinate_estimate (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∀ (χ : 𝓢(Space,ℂ)), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
      ∀ O K : Set Space, IsOpen O → O ⊆ V → (∀ z ∈ O, χ z = 1) → IsCompact K → K ⊆ O →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)),
        (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
        (∀ v : antiEnergy A J α hs ht,
          ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
            ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ∀ x ∈ K,
          ‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht a.val.val))
            (extChartAt Model p.val).symm x‖ ≤
            C * (‖antiToEnergy A J α hs ht a‖ +
              ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2) g)‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,hest⟩ :=
    raw_two_jet_estimate A J α hs ht D hD p τ hU hUD hτ q hq
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,fun χ hc hχV O K hO hOV hχ hK hKO => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hest χ hc hχV
  have hOD : O ⊆ (D p).domain := hOV.trans (hVW.trans (hWU.trans hUD))
  obtain ⟨L,hL,hLb⟩ := JetOperator.exteriorJet_bounded (D p).domain_open hK (hKO.trans hOD)
    (deltaComplexA J α ht p.val (D p)) (deltaComplexB J α ht p.val (D p))
    (deltaComplexA_smooth J α hs ht p.val (D p)) (deltaComplexB_smooth J α hs ht p.val (D p))
  refine ⟨L*C,mul_nonneg hL hC,fun f a g hg heq x hx => ?_⟩
  let u := localizedRawSchwartz A J α hs ht D hD p τ χ a
  have hr : ∀ z ∈ O, rawPair J α ht p.val (D p) a.val.val z = retract 2 (u z) := by
    intro z hz
    exact (localizedRawSchwartz_raw A J α hs ht D hD p τ χ a (hOD hz)
      (hτ z (hWU (hVW (hOV hz)))) (hχ z hz)).symm
  rw [ddstar_local_jet J α hs ht p.val (D p) a.val.property a.property hO hOD u hr (hKO hx)]
  have hj := JetOperator.exteriorJet_bound
    (deltaComplexA J α ht p.val (D p)) (deltaComplexB J α ht p.val (D p)) u x
  change ‖_‖ ≤ ‖_‖ * coordinateTwoJet u x at hj
  have hjet0 : 0 ≤ coordinateTwoJet u x := by
    exact add_nonneg (add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  have hj' := hj.trans (mul_le_mul_of_nonneg_right (hLb x hx) hjet0)
  have hh := hbound f a g hg heq x
  have hf := hj'.trans (mul_le_mul_of_nonneg_left hh hL)
  simpa only [mul_assoc] using hf

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set ComplexMatrix
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in

lemma closedLift_scaled_local_bound (p : A.centers) (τ : 𝓢(Space,ℝ)) (η : 𝓢(Space,ℂ))
    (L : Space ≃L[ℝ] Space) {U K : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1) (hη : ∀ z ∈ U, η z = 1)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
        (f : antiPre A J α hs ht) (z : Space), z ∈ K →
        ∀ (r M : ℝ), 0 < r → r ≤ 1 →
      (let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f))
       r*‖u (L z)‖ + r^2*∑ i, ‖(∂_{EuclideanEnergy.e i} u) (L z)‖ +
         r^3*∑ i, ∑ j, ‖(∂_{EuclideanEnergy.e j} (∂_{EuclideanEnergy.e i} u)) (L z)‖ ≤ M) →
      r^3*‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
        (extChartAt Model p.val).symm z -
        ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm z‖ ≤ C₀*M := by
  obtain ⟨C₀,hC,hbound⟩ := ddstar_scaled_jet_bound J α hs ht p.val (D p) L hK (hKU.trans hUD)
  refine ⟨C₀,hC,fun H Gs f z hz r M hr hr1 hj => ?_⟩
  rw [closedLiftOfInverse_pullback_sub]
  apply hbound (Gs f).val.val (Gs f).val.property (Gs f).property U hU hUD
    (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f)) _ z (hKU hz) hz r M hr hr1 hj
  intro y hy
  exact (localizedRawSchwartz_raw A J α hs ht D hD p τ η (Gs f) (hUD hy)
    (hτ y hy) (hη y hy)).symm

include D hD in

lemma exists_closed_lift_dual_data :
    ∃ H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht,
      (∀ f, smoothL2 A J α hs ht true (H f).val =
        (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val)) ∧
      (∀ f, IsClosed (H f).val.val) ∧
      (∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
          weakDelta A J α hs ht v⟫ =
        ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫) ∧
      (∀ f, IsClosed (closedLiftOfInverse A J α hs ht H Gs f).val) ∧
      (∀ f, antiInvariantPart J (closedLiftOfInverse A J α hs ht H Gs f).val = f.val.val) ∧
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
        (∀ v : antiEnergy A J α hs ht,
          |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
        ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ C₀*M := by
  obtain ⟨G,H,Gs,hH,hHclosed,hGs,hweak,C₀,hC,hdual⟩ :=
    exists_smooth_inverse_dual_data A J α hs ht D hD
  exact ⟨H,Gs,hH,hHclosed,hweak,closedLiftOfInverse_closed A J α hs ht H Gs hHclosed,
    closedLiftOfInverse_rightInverse A J α hs ht H Gs hweak,C₀,hC,hdual⟩
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
