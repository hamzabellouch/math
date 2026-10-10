import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.MatrixH1Smooth
import OAI.Geometry.TamingCompatibility.Elliptic.DirectionalPrincipal
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScalarSquare
import OAI.Geometry.TamingCompatibility.DifferentialForms.SquareLower

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution Filter
open scoped SchwartzMap LineDeriv Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma directionalPrincipal_locality {ι : Type*} [Fintype ι]
    (v : ι → E) (a : ι → ι → 𝓢(E,ℂ)) (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (directionalPrincipal v a (smulLeftCLM F h u)) =
      smulLeftCLM F g (directionalPrincipal v a u) := by
  simp only [directionalPrincipal,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [coefficient_products_commute g (a i j),distribution_second_product,map_add,
    cutoff_mul_cutoff g h hh,cutoff_secondCommutator_zero g h hh,add_zero]
  exact coefficient_products_commute (a i j) g _
end TamingCompatibility.HilbertSobolev

namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution Filter
open scoped SchwartzMap LineDeriv Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {m : ℕ}

lemma square_cutoff_locality (v : ι → E) (a : ι → 𝓢(E,R 2 →L[ℝ] R m))
    (b : 𝓢(E,R 2 →L[ℝ] R m)) (ρ : 𝓢(E,ℝ)) (G : ι → ι → E → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 2))
    (g h : 𝓢(E,ℂ)) (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,C 2)) :
    smulLeftCLM (C 2) g (square v a b ρ (smulLeftCLM (C 2) h u)) =
      smulLeftCLM (C 2) g (square v a b ρ u) := by
  rw [square_scalar_expansion v a b ρ G hG,square_scalar_expansion v a b ρ G hG,
    add_assoc,add_assoc,entries_lowerOrder,entries_lowerOrder]
  simp only [map_add,map_neg]
  rw [show (∑ i,∑ j,smulLeftCLM (C 2) (principalScalar a ρ i j)
      (∂_{v i} (∂_{v j} (smulLeftCLM (C 2) h u)))) =
      directionalPrincipal v (principalScalar a ρ) (smulLeftCLM (C 2) h u) from rfl,
    directionalPrincipal_locality v (principalScalar a ρ) g h hh u,
    matrixLowerOrder_locality _ _ _ _ _ g h hh u]
  rfl
end TamingCompatibility.ComplexMatrix

end

end OAI
