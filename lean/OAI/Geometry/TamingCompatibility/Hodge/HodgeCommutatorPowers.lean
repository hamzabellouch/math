import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeUniformOdd

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

def normalizedFullSquare
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) : 𝓢'(V,C 6) →L[ℂ] 𝓢'(V,C 6) :=
  (smulLeftCLM (C 6) θ).comp (fullShiftedSquare a b ρ 0)

lemma normalizedFullSquare_order (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2) 2 u) :
    MemSobolev n 2 (normalizedFullSquare a b ρ θ u) :=
  memSobolev_nat_product n θ (fullShiftedSquare_memSobolev n a b ρ 0 g ha hu)

lemma normalizedFullSquare_commutator_order (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (normalizedFullSquare a b ρ θ (fiberMap M u) -
      fiberMap M (normalizedFullSquare a b ρ θ u)) := by
  change MemSobolev _ _ (smulLeftCLM (C 6) θ _ - fiberMap M (smulLeftCLM (C 6) θ _))
  rw [fiberMap_product,← map_sub]
  exact memSobolev_nat_product n θ (fullShiftedSquare_commutator_memSobolev n a b ρ 0 g ha M hu)

lemma operator_power_order (P : 𝓢'(V,C 6) →L[ℂ] 𝓢'(V,C 6))
    (hP : ∀ (n : ℕ) {u}, MemSobolev ((n:ℝ)+2) 2 u → MemSobolev n 2 (P u))
    (k n : ℕ) {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2*k) 2 u) :
    MemSobolev n 2 ((P^k) u) := by
  induction k generalizing n with
  | zero => simpa using hu
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp]
    apply hP n
    have h := ih (n+2)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
    apply h
    convert hu using 1; push_cast; ring

lemma operator_power_commutator_order (P : 𝓢'(V,C 6) →L[ℂ] 𝓢'(V,C 6))
    (M : C 6 →L[ℂ] C 6)
    (hP : ∀ (n : ℕ) {u}, MemSobolev ((n:ℝ)+2) 2 u → MemSobolev n 2 (P u))
    (hC : ∀ (n : ℕ) {u}, MemSobolev ((n:ℝ)+1) 2 u →
      MemSobolev n 2 (P (fiberMap M u)-fiberMap M (P u)))
    (k n : ℕ) {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2*k+1) 2 u) :
    MemSobolev n 2 ((P^(k+1)) (fiberMap M u)-fiberMap M ((P^(k+1)) u)) := by
  induction k generalizing n with
  | zero => simpa using hC n (by simpa using hu)
  | succ k ih =>
    have he : (P ^ (k+1+1)) (fiberMap M u)-fiberMap M ((P^(k+1+1)) u) =
        P ((P^(k+1)) (fiberMap M u)-fiberMap M ((P^(k+1)) u)) +
          (P (fiberMap M ((P^(k+1)) u))-fiberMap M (P ((P^(k+1)) u))) := by
      rw [pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,map_sub]
      abel
    rw [he]
    apply MemSobolev.add
    · apply hP n
      have h := ih (n+2)
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
      apply h
      convert hu using 1; push_cast; ring
    · apply hC n
      have h := operator_power_order P hP (k+1) (n+1) (u := u)
      norm_num only [Nat.cast_add, Nat.cast_one] at h
      apply h
      convert hu using 1; push_cast; ring

lemma normalizedFullSquare_power_commutator_order (k n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2*k+1) 2 u) :
    MemSobolev n 2 (((normalizedFullSquare a b ρ θ)^(k+1)) (fiberMap M u)-
      fiberMap M (((normalizedFullSquare a b ρ θ)^(k+1)) u)) := by
  exact operator_power_commutator_order _ M
    (fun n _ hu => normalizedFullSquare_order n a b ρ θ g ha hu)
    (fun n _ hu => normalizedFullSquare_commutator_order n a b ρ θ g ha M hu) k n hu
end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodge_laplacian_weighted_distribution (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (a : Fin 4 → 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q))
    (b : 𝓢(Space,HodgeNormalSymbol.W →L[ℝ] HodgeNormalSymbol.Q)) (ρ : 𝓢(Space,ℝ))
    (ha : ∀ z ∈ U, ∀ i, a i z = normalA J α ht p.val (D p).toData i z)
    (hb : ∀ z ∈ U, b z = normalB J α ht p.val (D p).toData z)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (f : PreL2 A J α hs ht true)
    (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχU : tsupport χ ⊆ U) :
    smulLeftCLM (C 6) χ (fullShiftedSquare a b ρ 0
      (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))) =
    smulLeftCLM (C 6) χ (smulLeftCLM (C 6) (SchwartzMap.postcompCLM Complex.ofRealCLM ρ)
      (hodgeRawDistribution A J α hs ht D hD p τ
        (hodgeSmooth A J α hs ht (hodgeLaplacian A J α hs ht f)))) := by
  apply localize_eq_of_real_tests _ χ hc hχU
  intro φ hφ hφU
  have hzero (u : 𝓢'(Space,C 6)) : smulLeftCLM (C 6) (0 : 𝓢(Space,ℂ)) u = 0 := by
    change smulLeftCLM (C 6) (fun _ => 0) u = 0
    rw [smulLeftCLM_const]
    exact zero_smul ℂ u
  change (square EuclideanEnergy.e a b ρ _ + smulLeftCLM (C 6) (0 : 𝓢(Space,ℂ)) _) (SchwartzMap.postcompCLM Complex.ofRealCLM φ) = _
  rw [hzero,add_zero]
  ext j
  rw [hodge_raw_square_energy_smooth A J α hs ht D hD p τ hU hUD hτ a b ρ ha hb hρ φ hφ hφU j,
    hodge_raw_weighted_pair A J α hs ht D hD p τ ρ hUD hτ hρ φ hφ hφU j,
    hodgeInclusion_smooth,hodgeLaplacian_green_weak]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
