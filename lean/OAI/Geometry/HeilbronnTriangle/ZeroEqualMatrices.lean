import OAI.Geometry.HeilbronnTriangle.ZeroEqualAdditional
import OAI.Geometry.HeilbronnTriangle.EqualCoordinatePacking

namespace OAI


noncomputable section

namespace Problem355.ZeroEqualAdditional

open IntegralPlaneLattice

theorem weighted_matrix_shell_bound
    (q : ℕ) [Fact q.Prime] (L : Submodule ℤ (Fin 3 → ℤ))
    (E : ℤ) (hE : IsUnit (E : ZMod q)) (hL : ∀ v, E • v ∈ L)
    (i j : Fin 3) (hij : i ≠ j)
    (S : Finset (Fin 3 → ℤ)) (z : (Fin 3 → ℤ) → (Fin 3 → ℤ))
    (hz : ∀ x ∈ S, dotProduct x (z x) = 1)
    (hspan : ∀ x ∈ S, ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j)
    (A : (Fin 3 → ℤ) → Finset (Fin 3 → Fin 3 → ℤ))
    (weight : (Fin 3 → Fin 3 → ℤ) → ℝ)
    (R X I h W : ℝ) (hR : 1 ≤ R) (hX : 0 ≤ X) (hI : 0 < I) (hW : 0 ≤ W)
    (g : (Fin 3 → ℤ) → ℝ)
    (hshell : ∀ x ∈ S, R ≤ ‖LatticeBox.realVector x‖ ∧
      ‖LatticeBox.realVector x‖ ≤ 2 * R)
    (hg : ∀ x ∈ S, 0 < g x)
    (hpairing : ∀ x ∈ S, g x ^ 3 ≤ I * h ^ 2)
    (hcovol : ∀ x ∈ S, ZLattice.covolume (latticeIn x L) =
      I * ‖LatticeBox.realVector x‖ / g x)
    (hrow : ∀ x ∈ S, ∀ a ∈ A x, ∀ k, a k ∈ integerPlaneIn x L)
    (hcoord : ∀ x ∈ S, ∀ a ∈ A x, ∀ k, (a k i : ZMod q) = (a k j : ZMod q))
    (hnorm : ∀ x ∈ S, ∀ a ∈ A x, ∀ k, ‖castVec (a k)‖ ≤ X)
    (hpair : ∀ x ∈ S, ∀ a ∈ A x, ∃ k l : Fin 3,
      LinearIndependent ℝ ![castVec (a k), castVec (a l)])
    (hweight : ∀ x ∈ S, ∀ a ∈ A x, weight a ≤ W) :
    ∑ x ∈ S, ∑ a ∈ A x, weight a ≤
      125 * W * (9 * Real.pi) ^ 3 * X ^ 6 * h ^ 2 / ((q : ℝ) ^ 3 * I ^ 2) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  apply sum_shell_bound S R X I h q W hR hI hq hW g
    (fun x => ∑ a ∈ A x, weight a) hshell hg hpairing
  intro x hx
  have hc := EqualCoordinatePacking.matrices_card_le q x (z x) (hz x hx)
    L E hE hL i j hij (hspan x hx) (A x) X hX
    (hrow x hx) (hcoord x hx) (hnorm x hx) (hpair x hx)
  rw [hcovol x hx] at hc
  calc
    ∑ a ∈ A x, weight a ≤ ∑ _a ∈ A x, W := Finset.sum_le_sum (hweight x hx)
    _ = W * ((A x).card : ℝ) := by simp [mul_comm]
    _ ≤ W * (9 * Real.pi * X ^ 2 /
        ((q : ℝ) * (I * ‖LatticeBox.realVector x‖ / g x))) ^ 3 :=
      mul_le_mul_of_nonneg_left hc hW

end Problem355.ZeroEqualAdditional

end

end OAI
