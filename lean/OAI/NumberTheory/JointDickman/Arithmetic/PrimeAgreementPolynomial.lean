import OAI.NumberTheory.JointDickman.Arithmetic.PrimePhasePolynomial
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDistanceComparison
import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge

namespace OAI

/-! # Large-frequency distance from small-prime agreement -/
namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

theorem prime_agreement_distance_polynomial {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (P : Finset ℕ) (A : ℝ) (hA : 1 ≤ A) (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ f : ArithmeticFunction ℂ,
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ p : ℕ, p.Prime → p ∉ P → (p:ℝ) ≤ X^c → f p = 1) →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ X^A → R ≤ primeDistanceSquared f X t := by
  let M : ℝ := -Real.log c+1+∑ p ∈ P, 1/(p:ℝ)
  have htail := (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).eventually
    (eventually_le_nhds (lt_add_one (-Real.log c)))
  filter_upwards [prime_cosine_defect_polynomial A hA (R+2*M),htail]
    with X hX htailX
  intro f hf heq t htlo ht
  let g := characterArithmetic (1 : DirichletCharacter ℂ 1)
  have hg : ∀ n, ‖g n‖ ≤ 1 := characterArithmetic_norm_le_one _
  have hgp (p : ℕ) (hp : p.Prime) : g p = 1 := by
    dsimp [g]
    rw [characterArithmetic_prime _ hp,
      show (p:ZMod 1) = 1 from Subsingleton.elim _ _]
    exact map_one _
  have hh := primeDistanceSquared_lower_of_agree f g hf hg P X (X^c) t (by
    intro p hp hpP hpX
    rw [heq p hp hpP hpX,hgp p hp])
  have hd := hX t htlo ht
  rw [← principalDistance_eq_cosine] at hd
  change R+2*M ≤ primeDistanceSquared g X t at hd
  dsimp only [M] at hd
  linarith

end JointDickman

end OAI
