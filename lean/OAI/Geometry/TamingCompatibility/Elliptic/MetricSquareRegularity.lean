import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScalarSquare
import OAI.Geometry.TamingCompatibility.Functional.NormalizedFrame
import OAI.Geometry.TamingCompatibility.DifferentialForms.SquareLower

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma metric_square_regular
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 2 →L[ℝ] R m)) (b : 𝓢(V,R 2 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 2))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j)
    {u : 𝓢'(V,C 2)} (hu : MemSobolevLoc U 1 u)
    (hf : ∀ n : ℕ, MemSobolevLoc U n (square e a b ρ u)) :
    ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ n : ℕ, MemSobolevLoc W n u := by
  let G := principalScalar a ρ
  have hg : ∀ i j, G i j p = (c * ∑ t, frame t i * frame t j : ℝ) := by
    intro i j
    rw [principalScalar_apply a ρ g ha,hgp]
  have hk : 0 < ((2*Real.pi)^2)⁻¹ := by positivity
  obtain ⟨A,hA⟩ := exists_principal_normalization metric frame hframe c _ hc hk G p hg
  let B := squareFirst e (fun i => coefficient (a i)) (coefficient b)
    (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  let Cc := squareZero e (coefficient b) (fun i => weightedAdj ρ (a i)) (weightedAdj ρ b)
  apply linearly_normalized_interior_regular hU p hp e G A hA
    (fun q : Fin 4 × Fin 2 × Fin 2 => B q.1 q.2.1 q.2.2)
    (fun q => unit 2 2 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 2 × Fin 2 => Cc q.1 q.2) (fun q => unit 2 2 q.1 q.2) hu
  intro n
  have h := hf n
  rw [square_scalar_expansion e a b ρ g ha] at h
  rw [add_assoc,entries_lowerOrder] at h
  exact h

end TamingCompatibility.ComplexMatrix

end

end OAI
