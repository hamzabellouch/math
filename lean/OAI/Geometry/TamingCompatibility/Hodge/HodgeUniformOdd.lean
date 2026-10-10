import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeScaleSmoothing
import OAI.Geometry.TamingCompatibility.Hodge.HodgeScaleH3

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

lemma hodgeRegularization_uniform_local_odd (k : ℕ) (hk : k ≤ 2) (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) (2*k+1:ℕ),
          (∀ f, toDistribution Space (C 6) (2*k+1:ℕ) (L f) =
            smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
              (hodgeRegularizedGraph A J α hs ht r hr f))) ∧
          ∀ f, ‖L f‖ ≤ B*(r⁻¹)^(2*k+1)*‖f‖ := by
  interval_cases k
  · simp only [mul_zero,zero_add,pow_one]
    obtain ⟨τ,U,hU,hqU,hUD,hτ,B,hB,hreg⟩ :=
      hodgeRegularization_uniform_local_H1 A J α hs ht D hD p q hq hwq
    obtain ⟨φ,-,-,W,hW,hqW,hWU,hφone⟩ := SchwartzCutoff.exists_one_near hU hqU
    let χ := SchwartzMap.postcompCLM Complex.ofRealCLM φ
    let P := (HilbertSobolev.product (F := C 6) 1 χ).restrictScalars ℝ
    refine ⟨τ,χ,W,hW,hqW,hWU.trans hUD,fun z hz => hτ z (hWU hz),?_,
      ‖P‖*B,mul_nonneg (norm_nonneg _) hB,fun r hr hr1 => ?_⟩
    · intro z hz
      change (φ z : ℂ) = 1
      rw [hφone z hz,Complex.ofReal_one]
    · obtain ⟨L,hL,hb⟩ := hreg r hr hr1
      refine ⟨P.comp L,?_,?_⟩
      · intro f
        have hh : toDistribution Space (C 6) 1 (product 1 χ (L f)) =
            smulLeftCLM (C 6) χ (toDistribution Space (C 6) 1 (L f)) := by
          simpa only [toDistribution, Nat.cast_one] using
            toDistribution_product (F := C 6) 1 χ (L f)
        rw [hL f] at hh
        simpa [P,toDistribution] using hh
      · intro f
        calc
          _ ≤ ‖P‖*‖L f‖ := P.le_opNorm _
          _ ≤ ‖P‖*(B*r⁻¹*‖f‖) := mul_le_mul_of_nonneg_left (hb f) (norm_nonneg P)
          _ = _ := by ring
  · simpa using hodgeRegularization_uniform_local_H3 A J α hs ht D hD p q hq hwq
  · simpa using hodgeRegularization_uniform_local_H5 A J α hs ht D hD p q hq hwq
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

lemma fiberMap_directionalPrincipal (M : C 6 →L[ℂ] C 6)
    (g : Fin 4 → Fin 4 → 𝓢(V,ℂ)) (u : 𝓢'(V,C 6)) :
    fiberMap M (directionalPrincipal e g u) = directionalPrincipal e g (fiberMap M u) := by
  simp only [directionalPrincipal,map_sum,fiberMap_product,fiberMap_derivative]

lemma fullShiftedSquare_memSobolev (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2) 2 u) :
    MemSobolev n 2 (fullShiftedSquare a b ρ ζ u) := by
  rw [full_shifted_square_expansion a b ρ ζ g ha]
  apply MemSobolev.add
  · apply MemSobolev.neg
    apply memSobolev_sum
    intro i _
    apply memSobolev_sum
    intro j _
    apply memSobolev_nat_product
    convert (hu.lineDerivOp (m := e j)).lineDerivOp (m := e i) using 1; ring
  · exact matrixLowerOrder_memSobolev n _ _ _ _ _ (hu.mono (by linarith))

lemma fullShiftedSquare_commutator_memSobolev (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (fullShiftedSquare a b ρ ζ (fiberMap M u) -
      fiberMap M (fullShiftedSquare a b ρ ζ u)) := by
  let L := matrixLowerOrder
    (fun q : Fin 4 × Fin 6 × Fin 6 =>
      squareFirst e (fun i => coefficient (a i)) (coefficient b)
        (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b) q.1 q.2.1 q.2.2)
    (fun q => unit 6 6 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 6 × Fin 6 =>
      (squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i))
        (fullWeightedAdj ρ b)+scalarMatrix 6 ζ) q.1 q.2)
    (fun q => unit 6 6 q.1 q.2)
  have he : fullShiftedSquare a b ρ ζ (fiberMap M u) -
      fiberMap M (fullShiftedSquare a b ρ ζ u) = L (fiberMap M u) - fiberMap M (L u) := by
    rw [full_shifted_square_expansion a b ρ ζ g ha,
      full_shifted_square_expansion a b ρ ζ g ha]
    simp only [map_add,map_neg,fiberMap_directionalPrincipal]
    change -_ + L _ - (-_ + fiberMap M (L _)) = _
    abel
  rw [he]
  exact (matrixLowerOrder_memSobolev n _ _ _ _ _ (MemSobolev_fiberMap hu M)).sub
    (MemSobolev_fiberMap (matrixLowerOrder_memSobolev n _ _ _ _ _ hu) M)

def fullShiftedSquare_commutator_lift (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6) :
    H V (C 6) ((n:ℝ)+1) →L[ℝ] H V (C 6) n :=
  let F : H V (C 6) ((n:ℝ)+1) →L[ℂ] 𝓢'(V,C 6) :=
    ((fullShiftedSquare a b ρ ζ).comp (fiberMap M) -
      (fiberMap M).comp (fullShiftedSquare a b ρ ζ)).comp
        (toDistribution V (C 6) ((n:ℝ)+1))
  realSobolevLift n (F.restrictScalars ℝ)
    (fun u => fullShiftedSquare_commutator_memSobolev n a b ρ ζ g ha M
      (toDistribution_memSobolev _ u))

lemma fullShiftedSquare_commutator_lift_spec (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    (u : H V (C 6) ((n:ℝ)+1)) :
    toDistribution V (C 6) n (fullShiftedSquare_commutator_lift n a b ρ ζ g ha M u) =
      fullShiftedSquare a b ρ ζ (fiberMap M (toDistribution V (C 6) ((n:ℝ)+1) u)) -
      fiberMap M (fullShiftedSquare a b ρ ζ (toDistribution V (C 6) ((n:ℝ)+1) u)) := by
  unfold fullShiftedSquare_commutator_lift
  exact realSobolevLift_spec _ _ _ _
end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
