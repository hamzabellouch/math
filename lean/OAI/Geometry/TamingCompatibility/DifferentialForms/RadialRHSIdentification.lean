import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.NormalizedHarmonicRHS

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [MeasurableSpace X] [BorelSpace X] in
lemma realPairSchwartz_testAnti (p : A.centers) (q : 𝓢(Space,EuclideanEnergy.Pair))
    (hc : HasCompactSupport (q : Space → _)) (hqD : tsupport q ⊆ (D p).domain) (z : Space) :
    realPairSchwartz A J α ht D hD p (testAnti A J α hs ht D p q hc hqD).val z =
      coordinateWeight A p z • q z := by
  by_cases hz : z ∈ (D p).domain
  · erw [realPairSchwartz_raw A J α ht D hD p _ hz]
    congr 1
    exact rawPair_manifoldTest J α ht p.val (D p) hqD hz
  · have hqz : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hqD h))
    erw [realPairSchwartz_apply,hqz,smul_zero]
    simp only [scalar,indicator_of_notMem hz,EuclideanEnergy.pair]
    ext i; fin_cases i <;> rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma weightedRawRHS_testAnti (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (q : 𝓢(Space,EuclideanEnergy.Pair)) (hc : HasCompactSupport (q : Space → _))
    (hqD : tsupport q ⊆ (D p).domain)
    (hτ : ∀ z ∈ tsupport q, τ z * coordinateWeight A p z = 1) :
    weightedRawRHS A J α hs ht D hD p τ ρ (testAnti A J α hs ht D p q hc hqD) =
      (2:ℝ) • SchwartzMap.smulLeftCLM EuclideanEnergy.Pair ρ q := by
  apply SchwartzMap.ext
  intro z
  simp only [weightedRawRHS,_root_.smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ρ.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,
    realPairSchwartz_testAnti A J α hs ht D hD p q hc hqD z]
  by_cases hz : z ∈ tsupport q
  · rw [smul_smul (τ z) (coordinateWeight A p z),hτ z hz,one_smul]
  · simp only [image_eq_zero_of_notMem_tsupport hz,smul_zero]

omit [MeasurableSpace X] [BorelSpace X] in
lemma normalizedRawRHSMap_testAnti (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (L : Space ≃L[ℝ] Space) (q : 𝓢(Space,EuclideanEnergy.Pair))
    (hc : HasCompactSupport (q : Space → _)) (hqD : tsupport q ⊆ (D p).domain)
    (hτ : ∀ z ∈ tsupport q, τ z * coordinateWeight A p z = 1) :
    normalizedRawRHSMap A J α hs ht D hD p τ ρ L (testAnti A J α hs ht D p q hc hqD) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) ((2:ℝ) • SchwartzMap.smulLeftCLM EuclideanEnergy.Pair ρ q)) := by
  rw [normalizedRawRHSMap_apply,weightedRawRHS_testAnti A J α hs ht D hD p τ ρ q hc hqD hτ]

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Function
open scoped ContDiff Topology
variable {E F G D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma norm_iteratedFDeriv_affine_le (f : E → F) (hf : ContDiff ℝ ∞ f)
    (L : D →L[ℝ] E) (b : E) (x : D) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => f (L z-b)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (L x-b)‖ * ‖L‖^n := by
  have he : (fun z => f (L z-b)) = (fun z => f (z-b)) ∘ L := rfl
  have hs : ContDiff ℝ ∞ (fun z => f (z-b)) := hf.comp (contDiff_id.sub contDiff_const)
  rw [he,L.iteratedFDeriv_comp_right hs x
    (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top),
    iteratedFDeriv_comp_sub]
  simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n f (L x-b)) (fun _ => L)

lemma norm_iteratedFDeriv_linear_affine_le (f : E → F) (hf : ContDiff ℝ ∞ f)
    (T : F →L[ℝ] G) (L : D →L[ℝ] E) (b : E) (x : D) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z => T (f (L z-b))) x‖ ≤
      ‖T‖ * ‖iteratedFDeriv ℝ n f (L x-b)‖ * ‖L‖^n := by
  have hg : ContDiff ℝ ∞ (fun z => f (L z-b)) := hf.comp (L.contDiff.sub contDiff_const)
  rw [show (fun z => T (f (L z-b))) = T ∘ (fun z => f (L z-b)) from rfl,
    T.iteratedFDeriv_comp_left hg.contDiffAt (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  calc
    _ ≤ ‖T‖ * ‖iteratedFDeriv ℝ n (fun z => f (L z-b)) x‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖T‖ * (‖iteratedFDeriv ℝ n f (L x-b)‖ * ‖L‖^n) :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_affine_le f hf L b x n) (norm_nonneg _)
    _ = _ := by ring

end TamingCompatibility.RadialPotential

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv

def complexComponentCLM (j : Fin 2) : ℝ →L[ℝ] C 2 :=
  (embed 2).comp (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j 1))

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [MeasurableSpace X] [BorelSpace X] in
lemma normalizedRawRHSMap_component_apply (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (L : Space ≃L[ℝ] Space) (j : Fin 2) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain)
    (hτ : ∀ z ∈ tsupport φ, τ z * coordinateWeight A p z = 1) (z : Space) :
    normalizedRawRHSMap A J α hs ht D hD p τ ρ L
      (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
        ((componentTest_support j φ).trans hφD)) z =
      (2:ℝ) • complexComponentCLM j (ρ (L.symm z) * φ (L.symm z)) := by
  rw [normalizedRawRHSMap_testAnti A J α hs ht D hD p τ ρ L _ _ _
    (fun x hx => hτ x (componentTest_support j φ hx))]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    SchwartzMap.postcompCLM_apply,_root_.smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ρ.hasTemperateGrowth,componentTest_apply,
    complexComponentCLM,ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply]
  simp only [map_smul,smul_smul]

omit [MeasurableSpace X] [BorelSpace X] in
lemma normalizedRawRHSMap_component_derivative_le (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (L : Space ≃L[ℝ] Space) (j : Fin 2) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain)
    (hτ : ∀ z ∈ tsupport φ, τ z * coordinateWeight A p z = 1)
    (k : ℕ) (v : Fin k → Space) (hv : ∀ i, ‖v i‖ ≤ 1) (x : Space) :
    ‖(∂^{v} (normalizedRawRHSMap A J α hs ht D hD p τ ρ L
      (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
        ((componentTest_support j φ).trans hφD)))) x‖ ≤
      ‖(2:ℝ) • complexComponentCLM j‖ *
        ‖iteratedFDeriv ℝ k (fun z => ρ z * φ z) (L.symm x)‖ * ‖L.symm.toContinuousLinearMap‖^k := by
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  have he : (normalizedRawRHSMap A J α hs ht D hD p τ ρ L
      (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
        ((componentTest_support j φ).trans hφD)) : Space → C 2) =
      fun z => ((2:ℝ) • complexComponentCLM j) (ρ (L.symm z) * φ (L.symm z)) :=
    funext (normalizedRawRHSMap_component_apply A J α hs ht D hD p τ ρ L j φ hc hφD hτ)
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (fun z => ((2:ℝ) • complexComponentCLM j)
        (ρ (L.symm z) * φ (L.symm z))) x‖ := by
      exact (ContinuousMultilinearMap.le_opNorm _ v).trans (by
        simpa using mul_le_mul_of_nonneg_left
          (Finset.prod_le_one₀ (fun i _ => norm_nonneg (v i)) (fun i _ => hv i)) (norm_nonneg _))
    _ ≤ _ := by
      simpa only [sub_zero,ContinuousLinearEquiv.coe_coe] using RadialPotential.norm_iteratedFDeriv_linear_affine_le
        (fun z => ρ z * φ z) ((ρ.smooth ⊤).mul (φ.smooth ⊤))
        ((2:ℝ) • complexComponentCLM j) L.symm.toContinuousLinearMap 0 x k

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
