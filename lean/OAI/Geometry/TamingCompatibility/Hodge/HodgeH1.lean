import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.LinearUniform
import OAI.Geometry.TamingCompatibility.Hodge.HodgeScalarSquare
import OAI.Geometry.TamingCompatibility.Hodge.HodgeNormalDistribution
import OAI.Geometry.TamingCompatibility.Hodge.HodgeFrameH1

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeGraph_norm_sq (a : PreL2 A J α hs ht true) :
    ‖hodgeGraph A J α hs ht a‖^2 =
      (∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂ManifoldVolume.geometricVolume A J α) +
      (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
        (codifferential J α ht a.val) x +
        GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a.val))
          (codifferential J α ht (starTwo J α ht a.val)) x ∂ManifoldVolume.geometricVolume A J α) := by
  rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
  change ‖smoothL2 A J α hs ht true a‖^2 +
    (‖smoothL2 A J α hs ht false (hodgeDelta A J α hs ht a)‖^2 +
      ‖smoothL2 A J α hs ht false (hodgeDelta A J α hs ht (preStar A J α hs ht a))‖^2) = _
  rw [(smoothL2 A J α hs ht true).norm_map,(smoothL2 A J α hs ht false).norm_map,
    (smoothL2 A J α hs ht false).norm_map,preL2_norm_sq,preL2_norm_sq,preL2_norm_sq]
  let := ManifoldVolume.geometricVolume_finite A J α hs ht
  have h₁ := GeometricAdjoint.codifferential_smooth J α hs ht a.property
  have h₂ := GeometricAdjoint.codifferential_smooth J α hs ht
    (starTwo_smooth J α hs ht a.property)
  rw [integral_add
    ((GeometricAdjoint.pairing_one_smooth J α hs ht h₁ h₁).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((GeometricAdjoint.pairing_one_smooth J α hs ht h₂ h₂).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  rfl

lemma hodgeSmooth_dense : DenseRange (hodgeSmooth A J α hs ht) :=
  ClosureLinear.toClosure_dense (hodgeGraph A J α hs ht)

def hodgeToH1 : PreL2 A J α hs ht true →ₗ[ℝ] globalH1 A 2 :=
  ClosureLinear.toClosure (localizeH1 A 2)

include hD in
lemma hodgeToH1_bound : ∃ C : ℝ, ∀ a : PreL2 A J α hs ht true,
    ‖hodgeToH1 A J α hs ht a‖ ≤ C * ‖hodgeSmooth A J α hs ht a‖ := by
  classical
  choose C hC hb using localized_jet_bound A J α hs ht D hD
  let B : ℝ := 1 + ∑ p : A.centers, C p
  have hB : 0 < B := by
    have hsum : 0 ≤ ∑ p : A.centers, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hcB (p : A.centers) : C p ≤ B :=
    (Finset.single_le_sum (fun p _ => (hC p).le) (Finset.mem_univ p)).trans
      (by change (∑ p : A.centers, C p) ≤ 1 + (∑ p : A.centers, C p); linarith)
  let N : ℝ := Fintype.card DerivativeIndex * Fintype.card A.centers
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨Real.sqrt (N*B),fun a => ?_⟩
  have hsq : ‖hodgeToH1 A J α hs ht a‖^2 ≤ N*B*‖hodgeSmooth A J α hs ht a‖^2 := by
    change ‖localizeH1 A 2 a‖^2 ≤ N*B*‖hodgeGraph A J α hs ht a‖^2
    simp only [PiLp.norm_sq_eq_of_L2]
    have hlocal (j : DerivativeIndex) (p : A.centers) :
        ‖localizeH1 A 2 a j p‖^2 ≤ B*‖hodgeGraph A J α hs ht a‖^2 := by
      have h := hb p a j
      rw [← hodgeGraph_norm_sq A J α hs ht a] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hcB p) (sq_nonneg _))
    calc
      _ ≤ ∑ j : DerivativeIndex, ∑ p : A.centers, B*‖hodgeGraph A J α hs ht a‖^2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun p _ => hlocal j p
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [N]; ring
  have hroot : (Real.sqrt (N*B)*‖hodgeSmooth A J α hs ht a‖)^2 =
      N*B*‖hodgeSmooth A J α hs ht a‖^2 := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hN hB.le)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp (hsq.trans_eq hroot.symm)

def hodgeEnergyToH1 : hodgeEnergy A J α hs ht →L[ℝ] globalH1 A 2 :=
  (hodgeToH1 A J α hs ht).extendOfNorm (hodgeSmooth A J α hs ht)

include hD in
lemma hodgeEnergyToH1_smooth (a : PreL2 A J α hs ht true) :
    hodgeEnergyToH1 A J α hs ht (hodgeSmooth A J α hs ht a) = hodgeToH1 A J α hs ht a :=
  LinearMap.extendOfNorm_eq (hodgeSmooth_dense A J α hs ht) (hodgeToH1_bound A J α hs ht D hD) a
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

lemma full_metric_square_regular
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j)
    {u : 𝓢'(V,C 6)} (hu : MemSobolevLoc U 1 u)
    (hf : ∀ n : ℕ, MemSobolevLoc U n (square e a b ρ u)) :
    ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ n : ℕ, MemSobolevLoc W n u := by
  let G := fullPrincipalScalar a ρ
  have hg : ∀ i j, G i j p = (c * ∑ t, frame t i * frame t j : ℝ) := by
    intro i j
    rw [fullPrincipalScalar_apply a ρ g ha,hgp]
  have hk : 0 < ((2*Real.pi)^2)⁻¹ := by positivity
  obtain ⟨A,hA⟩ := exists_principal_normalization metric frame hframe c _ hc hk G p hg
  let B := squareFirst e (fun i => coefficient (a i)) (coefficient b)
    (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)
  let Cc := squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)
  apply linearly_normalized_interior_regular hU p hp e G A hA
    (fun q : Fin 4 × Fin 6 × Fin 6 => B q.1 q.2.1 q.2.2)
    (fun q => unit 6 6 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 6 × Fin 6 => Cc q.1 q.2) (fun q => unit 6 6 q.1 q.2) hu
  intro n
  have h := hf n
  rw [full_square_scalar_expansion e a b ρ g ha] at h
  rw [add_assoc,entries_lowerOrder] at h
  exact h

end TamingCompatibility.ComplexMatrix

noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma full_metric_square_uniform_regular
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j)
    : ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ (n : ℕ) (u : 𝓢'(V,C 6)),
      MemSobolevLoc U 1 u → MemSobolevLoc U n (square e a b ρ u) →
      MemSobolevLoc W ((n:ℝ)+2) u := by
  let G := fullPrincipalScalar a ρ
  have hg : ∀ i j, G i j p = (c * ∑ t, frame t i * frame t j : ℝ) := by
    intro i j
    rw [fullPrincipalScalar_apply a ρ g ha,hgp]
  have hk : 0 < ((2*Real.pi)^2)⁻¹ := by positivity
  obtain ⟨A,hA⟩ := exists_principal_normalization metric frame hframe c _ hc hk G p hg
  let B := squareFirst e (fun i => coefficient (a i)) (coefficient b)
    (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)
  let Cc := squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)
  obtain ⟨W,hW,hpW,hWU,hall⟩ := linearly_normalized_uniform_regular hU p hp e G A hA
    (fun q : Fin 4 × Fin 6 × Fin 6 => B q.1 q.2.1 q.2.2)
    (fun q => unit 6 6 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 6 × Fin 6 => Cc q.1 q.2) (fun q => unit 6 6 q.1 q.2)
  refine ⟨W,hW,hpW,hWU,?_⟩
  intro n u hu hf
  apply hall n u hu
  have h := hf
  rw [full_square_scalar_expansion e a b ρ g ha] at h
  rw [add_assoc,entries_lowerOrder] at h
  exact h

end TamingCompatibility.ComplexMatrix

noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma full_metric_square_uniform_estimate
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j) :
    ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ (n : ℕ)
      (χ : 𝓢(V,ℂ)), HasCompactSupport (χ : V → ℂ) → tsupport χ ⊆ W →
      ∃ T : localSolutionSpace U n (square e a b ρ) →L[ℂ] H V (C 6) ((n:ℝ)+2),
      ∀ u, toDistribution V (C 6) ((n:ℝ)+2) (T u) =
        smulLeftCLM (C 6) χ (toDistribution V (C 6) 1 u.val.1) := by
  obtain ⟨W,hW,hpW,hWU,hreg⟩ := full_metric_square_uniform_regular hU p hp metric frame hframe
    a b ρ g ha c hc hgp
  refine ⟨W,hW,hpW,hWU,fun n χ hχ hχW => ?_⟩
  exact local_regular_estimate U W n (square e a b ρ) (hreg n) χ hχ hχW

end TamingCompatibility.ComplexMatrix

end
end
end
end

end
end

end OAI
