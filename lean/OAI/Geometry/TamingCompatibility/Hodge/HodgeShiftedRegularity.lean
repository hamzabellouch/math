import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.LinearUniform
import OAI.Geometry.TamingCompatibility.Hodge.HodgeScalarSquare

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open LocalMatrixOperator EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

def fullShiftedSquare (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m))
    (b : 𝓢(V,R 6 →L[ℝ] R m)) (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) :
    𝓢'(V,C 6) →L[ℂ] 𝓢'(V,C 6) := square e a b ρ + smulLeftCLM (C 6) ζ

lemma full_shifted_square_expansion (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m))
    (b : 𝓢(V,R 6 →L[ℝ] R m)) (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ))
    (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (u : 𝓢'(V,C 6)) :
    fullShiftedSquare a b ρ ζ u =
      -directionalPrincipal e (fullPrincipalScalar a ρ) u +
      matrixLowerOrder
        (fun q : Fin 4 × Fin 6 × Fin 6 =>
          squareFirst e (fun i => coefficient (a i)) (coefficient b)
            (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b) q.1 q.2.1 q.2.2)
        (fun q => unit 6 6 q.2.1 q.2.2) (fun q => e q.1)
        (fun q : Fin 6 × Fin 6 =>
          (squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i))
            (fullWeightedAdj ρ b)+scalarMatrix 6 ζ) q.1 q.2)
        (fun q => unit 6 6 q.1 q.2) u := by
  rw [← entries_lowerOrder]
  have hm := multiply_add (squareZero e (coefficient b)
    (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)) (scalarMatrix 6 ζ) u
  rw [multiply_scalarMatrix] at hm
  change multiply (squareZero e (coefficient b)
    (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)+scalarMatrix 6 ζ) u = _ at hm
  rw [hm]
  change square e a b ρ u + smulLeftCLM (C 6) ζ u = _
  rw [full_square_scalar_expansion e a b ρ g ha]
  simp only [directionalPrincipal,add_assoc]

lemma full_shifted_square_uniform_regular
    {U : Set V} (hU : IsOpen U) (p : V) (hp : p ∈ U)
    (metric : MetricModel.Metric V) (frame : Fin 4 → V)
    (hframe : ∀ i j, metric.bilinear (frame i) (frame j) = if i=j then 1 else 0)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    (c : ℝ) (hc : 0 < c)
    (hgp : ∀ i j, g i j p = c * ∑ t, frame t i * frame t j) :
    ∃ W : Set V, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ∀ (n : ℕ) (u : 𝓢'(V,C 6)),
      MemSobolevLoc U 1 u → MemSobolevLoc U n (fullShiftedSquare a b ρ ζ u) →
      MemSobolevLoc W ((n:ℝ)+2) u := by
  let G := fullPrincipalScalar a ρ
  have hg : ∀ i j, G i j p = (c * ∑ t, frame t i * frame t j : ℝ) := by
    intro i j
    rw [fullPrincipalScalar_apply a ρ g ha,hgp]
  have hk : 0 < ((2*Real.pi)^2)⁻¹ := by positivity
  obtain ⟨A,hA⟩ := exists_principal_normalization metric frame hframe c _ hc hk G p hg
  let B := squareFirst e (fun i => coefficient (a i)) (coefficient b)
    (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)
  let Cc := squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i))
    (fullWeightedAdj ρ b)+scalarMatrix 6 ζ
  obtain ⟨W,hW,hpW,hWU,hall⟩ := linearly_normalized_uniform_regular hU p hp e G A hA
    (fun q : Fin 4 × Fin 6 × Fin 6 => B q.1 q.2.1 q.2.2)
    (fun q => unit 6 6 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 6 × Fin 6 => Cc q.1 q.2) (fun q => unit 6 6 q.1 q.2)
  refine ⟨W,hW,hpW,hWU,?_⟩
  intro n u hu hf
  apply hall n u hu
  have h := hf
  rw [full_shifted_square_expansion a b ρ ζ g ha] at h
  exact h
end TamingCompatibility.ComplexMatrix

end

end OAI
