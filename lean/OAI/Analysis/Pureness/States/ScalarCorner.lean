import OAI.Analysis.Pureness.Divisibility.Fullness
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace OAI
namespace CuntzPureness
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteDimensional_of_scalar_sandwich (hsimple : TopologicallySimple A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0)
    (hcorner : ∀ a : A, ∃ z : ℂ, h * a * h = z • h) : FiniteDimensional ℂ A := by
  classical
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hh0
  let g : Fin n × Fin n → A := fun ij => star (s ij.1) * h * s ij.2
  let T : (Fin n × Fin n → ℂ) →ₗ[ℂ] A := {
    toFun := fun c => ∑ ij, c ij • g ij
    map_add' := by
      intro c d
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro z c
      simp only [Pi.smul_apply, smul_smul, smul_eq_mul, Finset.smul_sum, RingHom.id_apply] }
  apply Module.Finite.of_surjective T
  intro a
  choose c hc using fun i j : Fin n => hcorner (s i * a * star (s j))
  refine ⟨fun ij => c ij.1 ij.2, ?_⟩
  change (∑ ij : Fin n × Fin n, c ij.1 ij.2 • g ij) = a
  symm
  calc
    a = (∑ i : Fin n, star (s i) * h * s i) * a *
        (∑ j : Fin n, star (s j) * h * s j) := by rw [hs, one_mul, mul_one]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        star (s i) * (h * (s i * a * star (s j)) * h) * s j := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, c i j • (star (s i) * h * s j) := by
      simp only [hc, mul_smul_comm, smul_mul_assoc]
    _ = _ := by simp only [Fintype.sum_prod_type, g]

theorem exists_nonscalar_sandwich (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) :
    ∃ a : A, ∀ z : ℂ, h * a * h ≠ z • h := by
  by_contra hn
  push Not at hn
  exact hinf (finiteDimensional_of_scalar_sandwich hsimple h hh hh0 hn)
end CuntzPureness

end OAI
