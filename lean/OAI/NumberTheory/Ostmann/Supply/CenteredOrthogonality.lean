import OAI.NumberTheory.Ostmann.Supply.CenteredProjection
import OAI.NumberTheory.Ostmann.Supply.SpectralApproximation

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
section Generic
variable {ι : Type*} [Fintype ι]
local notation "H" => EuclideanSpace ℂ ι

theorem centeredSpace_orthogonal_of_constant (S : Finset ι) (f : H) (c : ℂ)
    (hc : ∀ x ∈ S, f x = c) : f ∈ (centeredSpace S)ᗮ := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro g hg
  rw [PiLp.inner_apply]
  calc
    (∑ x, inner ℂ (f x) (g x)) = ∑ x ∈ S, inner ℂ (f x) (g x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hx hxs
      simp [hg.1 x hxs]
    _ = ∑ x ∈ S, conj c*g x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [hc x hx, RCLike.inner_apply, mul_comm]
    _ = 0 := by rw [← Finset.mul_sum, hg.2, mul_zero]

theorem centeredProjection_eq_zero_of_constant (S : Finset ι) (f : H) (c : ℂ)
    (hc : ∀ x ∈ S, f x = c) : centeredProjection S f = 0 := by
  change (centeredSpace S).starProjection f = 0
  rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
  exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    (centeredSpace_orthogonal_of_constant S f c hc)
end Generic

section Cyclic
variable {p : ℕ} [NeZero p]

theorem centeredProjection_normalizedVector (S : Finset (ZMod p)) :
    centeredProjection S (normalizedVector S) = 0 := by
  apply centeredProjection_eq_zero_of_constant S (normalizedVector S)
    (((1-density S)/Real.sqrt (density S*(1-density S)) : ℝ) : ℂ)
  intro x hx
  simp [normalizedVector, normalizedIndicator, centeredIndicator, hx]

theorem centeredProjection_compl_normalizedVector (S : Finset (ZMod p)) :
    centeredProjection Sᶜ (normalizedVector S) = 0 := by
  apply centeredProjection_eq_zero_of_constant Sᶜ (normalizedVector S)
    (((-density S)/Real.sqrt (density S*(1-density S)) : ℝ) : ℂ)
  intro x hx
  have hxs := Finset.mem_compl.mp hx
  simp [normalizedVector, normalizedIndicator, centeredIndicator, hxs]
end Cyclic
end Ostmann.Supply

end

end OAI
