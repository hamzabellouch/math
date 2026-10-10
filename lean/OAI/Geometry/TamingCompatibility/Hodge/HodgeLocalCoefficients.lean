import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCommutatorPowers

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
include hs in

lemma exists_hodge_local_coefficients (p : A.centers) {U : Set Space}
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain) (q : Space) (hq : q ∈ U) :
    ∃ W : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧
      ∃ a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q),
      ∃ b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q),
      ∃ ρ : 𝓢(Space,ℝ), ∃ θ : 𝓢(Space,ℂ), ∃ G : Fin 4 → Fin 4 → Space → ℝ,
      (∀ z ∈ W, ∀ i, a i z = normalA J α ht p.val (D p).toData i z) ∧
      (∀ z ∈ W, b z = normalB J α ht p.val (D p).toData z) ∧
      (∀ z ∈ W, ρ z = chartDensity J α p.val z) ∧
      (∀ z ∈ W, θ z * (ρ z : ℂ) = 1) ∧
      ∀ i j z, (ρ z • a i z).adjoint ∘L a j z + (ρ z • a j z).adjoint ∘L a i z =
        (2*G i j z) • ContinuousLinearMap.id ℝ (ComplexMatrix.R 6) := by
  obtain ⟨φ,hφ,hφU,V,hV,hqV,hVU,hφone⟩ := SchwartzCutoff.exists_one_near hU hq
  have hφD := hφU.trans hUD
  let a := patchA J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let b := patchB J α hs ht p.val (D p).toData (φ.smooth ⊤) hφ hφD
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset) (φ.smooth ⊤) hφ hφD
  have hρ : ∀ z ∈ V, ρ z = chartDensity J α p.val z := by
    intro z hz
    simp only [ρ,SchwartzCutoff.schwartz_apply,hφone z hz,one_smul]
  have hρq : ρ q ≠ 0 := by
    rw [hρ q hqV]
    exact ne_of_gt (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq)))
  obtain ⟨κ,-,-,W,hW,hqW,hWV,hκ⟩ := SchwartzCutoff.exists_reciprocal hV
    ((ρ.smooth ⊤).contDiffOn) hqV hρq
  let θ := SchwartzMap.postcompCLM Complex.ofRealCLM κ
  let G := fun i j z => ρ z*φ z*φ z*GeometricChart.normalMetric J α ht p.val (D p).toData i j z
  refine ⟨W,hW,hqW,hWV.trans hVU,a,b,ρ,θ,G,?_,?_,?_,?_,?_⟩
  · intro z hz i
    simp only [a,patchA,SchwartzCutoff.schwartz_apply,hφone z (hWV hz),one_smul]
  · intro z hz
    simp only [b,patchB,SchwartzCutoff.schwartz_apply,hφone z (hWV hz),one_smul]
  · exact fun z hz => hρ z (hWV hz)
  · intro z hz
    change (κ z : ℂ) * (ρ z : ℂ) = 1
    exact_mod_cast hκ z hz
  · exact patchA_polarized J α ht p.val (D p).toData (φ.smooth ⊤) hφ hφD ρ
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

def normalizedFullSquare_power_commutator_lift (k n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6) :
    H V (C 6) ((n:ℝ)+2*k+1) →L[ℝ] H V (C 6) n :=
  let P := normalizedFullSquare a b ρ θ
  let F := (((P^(k+1)).comp (fiberMap M) - (fiberMap M).comp (P^(k+1))).comp
    (toDistribution V (C 6) ((n:ℝ)+2*k+1))).restrictScalars ℝ
  realSobolevLift n F (fun u => normalizedFullSquare_power_commutator_order
    k n a b ρ θ g ha M (toDistribution_memSobolev _ u))

lemma normalizedFullSquare_power_commutator_lift_spec (k n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    (u : H V (C 6) ((n:ℝ)+2*k+1)) :
    toDistribution V (C 6) n (normalizedFullSquare_power_commutator_lift k n a b ρ θ g ha M u) =
      ((normalizedFullSquare a b ρ θ)^(k+1)) (fiberMap M (toDistribution V (C 6) ((n:ℝ)+2*k+1) u)) -
      fiberMap M (((normalizedFullSquare a b ρ θ)^(k+1)) (toDistribution V (C 6) ((n:ℝ)+2*k+1) u)) := by
  unfold normalizedFullSquare_power_commutator_lift
  exact realSobolevLift_spec _ _ _ _
lemma normalizedFullSquare_power_commutator_lift_zero_spec (k : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    (u : H V (C 6) (2*k+1:ℕ)) :
    toDistribution V (C 6) 0 (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u) =
      ((normalizedFullSquare a b ρ θ)^(k+1)) (fiberMap M (toDistribution V (C 6) (2*k+1:ℕ) u)) -
      fiberMap M (((normalizedFullSquare a b ρ θ)^(k+1)) (toDistribution V (C 6) (2*k+1:ℕ) u)) := by
  have h := normalizedFullSquare_power_commutator_lift_spec k 0 a b ρ θ g ha M u
  simpa only [toDistribution,Nat.cast_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,zero_add] using h
end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev TemperedDistribution EuclideanEnergy Set
open scoped SchwartzMap
variable {m : ℕ}
lemma normalized_commutator_localized_spec (k : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    (M : C 6 →L[ℂ] C 6) (χ : 𝓢(V,ℂ)) (u : H V (C 6) (2*k+1:ℕ))
    (v w : 𝓢'(V,C 6))
    (hu : toDistribution V (C 6) (2*k+1:ℕ) u = v)
    (hw : smulLeftCLM (C 6) χ
      (((normalizedFullSquare a b ρ θ)^(k+1)) (fiberMap M v) -
        fiberMap M (((normalizedFullSquare a b ρ θ)^(k+1)) v)) = smulLeftCLM (C 6) χ w) :
    toDistribution V (C 6) 0 (product 0 χ
      (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u)) = smulLeftCLM (C 6) χ w := by
  have hp : toDistribution V (C 6) 0 (product 0 χ
      (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u)) =
    smulLeftCLM (C 6) χ (toDistribution V (C 6) 0
      (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u)) := by
    simpa only [toDistribution,Nat.cast_zero] using toDistribution_product (F := C 6) 0 χ
      (normalizedFullSquare_power_commutator_lift k 0 a b ρ θ g ha M u)
  rw [hp,normalizedFullSquare_power_commutator_lift_zero_spec,hu]
  exact hw
end TamingCompatibility.ComplexMatrix
namespace TamingCompatibility
lemma bounded_triple_composition {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : G →L[ℝ] H) (N : F →L[ℝ] G) (L : E →L[ℝ] F) (B t : ℝ)
    (h : ∀ v, ‖L v‖ ≤ B*t*‖v‖) (v : E) :
    ‖(P.comp (N.comp L)) v‖ ≤ ‖P‖*‖N‖*B*t*‖v‖ := by
  calc
    _ ≤ ‖P‖*‖N (L v)‖ := P.le_opNorm _
    _ ≤ ‖P‖*(‖N‖*‖L v‖) := mul_le_mul_of_nonneg_left (N.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖P‖*(‖N‖*(B*t*‖v‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring
end TamingCompatibility

end
end

end
end

end OAI
