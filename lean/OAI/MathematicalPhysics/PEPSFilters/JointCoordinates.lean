import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.Clipping
import OAI.MathematicalPhysics.PEPSFilters.JointSpectrum

namespace OAI

/-! Joint density coordinates for clipped regularized maximizers. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set

namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def coordinateDensity (p : SpectralCoordinate n) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ p.1 (Matrix.diagonal fun i => (p.2.val i : ℂ))

omit [Nonempty n] in
lemma coordinateDensity_positive (p : SpectralCoordinate n) : (coordinateDensity p).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact_mod_cast p.2.property.1 i

omit [Nonempty n] in
lemma trace_coordinateDensity (p : SpectralCoordinate n) : (coordinateDensity p).trace = 1 := by
  unfold coordinateDensity
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, p.1.property.1, Matrix.one_mul]
  simpa only [Matrix.trace_diagonal, ← Complex.ofReal_sum, Complex.ofReal_one] using
    congrArg Complex.ofReal p.2.property.2

omit [Nonempty n] in
lemma coordinateDensity_commute {b a : ℝ} (hb : 0 < b) (ha : 0 < a)
    (p : SpectralCoordinate n) (B : Matrix n n ℂ)
    (h : Commute (regularizedCoordinateMatrix b a p) B) : Commute (coordinateDensity p) B := by
  have hh := conj_diagonal_commute_fn p.1 (fun i => (p.2.val i + b) ^ (a/2)) B h
    (fun t => ((t ^ (2/a) - b : ℝ) : ℂ))
  have hi (i : n) : ((p.2.val i + b) ^ (a/2)) ^ (2/a) - b = p.2.val i := by
    rw [← Real.rpow_mul (add_nonneg (p.2.property.1 i) hb.le)]
    have he : a / 2 * (2/a) = 1 := by field_simp
    rw [he, Real.rpow_one]
    ring
  simpa only [coordinateDensity, hi] using hh

omit [Nonempty n] in
lemma regularizedCoordinateMatrix_eq_of_density_eq (b a : ℝ) (p s : SpectralCoordinate n)
    (h : coordinateDensity p = coordinateDensity s) :
    regularizedCoordinateMatrix b a p = regularizedCoordinateMatrix b a s :=
  conj_diagonal_fn_congr p.1 s.1 p.2.val s.2.val h (fun t => (((t+b) ^ (a/2) : ℝ) : ℂ))

omit [Nonempty n] in
lemma exists_joint_coordinate {b a : ℝ} (hb : 0 < b) (ha : 0 < a)
    (p : SpectralCoordinate n) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hc : Commute (regularizedCoordinateMatrix b a p) ρ) :
    ∃ s : SpectralCoordinate n,
      regularizedCoordinateMatrix b a s = regularizedCoordinateMatrix b a p ∧
      ρ = Unitary.conjStarAlgAut ℂ _ s.1 (Matrix.diagonal fun i => (marginalDiagonal s.1 ρ i : ℂ)) := by
  obtain ⟨U, α, β, hA, hB⟩ := exists_joint_diagonal (coordinateDensity_positive p).isHermitian
    hρ.isHermitian (coordinateDensity_commute hb ha p ρ hc)
  have hα : star (U : Matrix n n ℂ) * coordinateDensity p * (U : Matrix n n ℂ) =
      Matrix.diagonal (fun i => (α i : ℂ)) := by
    rw [hA, Unitary.conjStarAlgAut_apply]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star (U : Matrix n n ℂ)) (U : Matrix n n ℂ),
      U.property.1, Matrix.one_mul, Matrix.mul_one]
  have hβ : star (U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ) =
      Matrix.diagonal (fun i => (β i : ℂ)) := by
    rw [hB, Unitary.conjStarAlgAut_apply]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star (U : Matrix n n ℂ)) (U : Matrix n n ℂ),
      U.property.1, Matrix.one_mul, Matrix.mul_one]
  have hnonneg : ∀ i, 0 ≤ α i := by
    have hh := (coordinateDensity_positive p).conjTranspose_mul_mul_same (U : Matrix n n ℂ)
    change (star (U : Matrix n n ℂ) * coordinateDensity p * (U : Matrix n n ℂ)).PosSemidef at hh
    rw [hα] at hh
    intro i
    exact_mod_cast (Matrix.posSemidef_diagonal_iff.mp hh) i
  have hsum : ∑ i, α i = 1 := by
    have hh := congrArg Matrix.trace hA
    rw [trace_coordinateDensity, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      U.property.1, Matrix.one_mul, Matrix.trace_diagonal] at hh
    have hh' := congrArg Complex.re hh
    simpa only [Complex.one_re, ← Complex.ofReal_sum, Complex.ofReal_re] using hh'.symm
  let s : SpectralCoordinate n := (U, ⟨α, hnonneg, hsum⟩)
  refine ⟨s, regularizedCoordinateMatrix_eq_of_density_eq b a s p hA.symm, ?_⟩
  convert hB using 2
  congr 1
  funext i
  simp only [s, marginalDiagonal, hβ, Matrix.diagonal_apply_eq, Complex.ofReal_re]

end PolynomialPEPS.PinnedEntropy.NestedFilter
namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder

theorem exists_regularized_maximizer_clipped {L q m : ℕ} [NeZero q]
    {X : Fin m → Finset (Vertex L)} {b : ℝ} (hb : 0 < b)
    (Ω : State L q) (hΩ : Ω ≠ 0) (hX : Monotone X)
    {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) :
    ∃ p : CoordinateFamily q X, IsRegularizedMaximizer hb.le Ω a p ∧
      (∀ j, Commute (regularizedFilters hb.le a p j).matrix
        (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j))) ∧
      ∀ j, let ρ := reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j)
        ρ = Unitary.conjStarAlgAut ℂ _ (p j).1
          (Matrix.diagonal fun i => (marginalDiagonal (p j).1 ρ i : ℂ)) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ i, (p j).2.val i + b = max b (marginalDiagonal (p j).1 ρ i / c) := by
  classical
  obtain ⟨p₀, hp₀, hc₀⟩ := exists_regularized_maximizer_commute hb Ω hX ha
  choose p he hd using fun j => exists_joint_coordinate hb (ha j) (p₀ j)
    (reducedDensity_posSemidef (X j) (output (regularizedFilters hb.le a p₀) Ω)) (hc₀ j)
  have hf : regularizedFilters hb.le a p = regularizedFilters hb.le a p₀ := by
    funext j
    change PositiveFilter.mk _ _ = PositiveFilter.mk _ _
    congr 1
    exact he j
  have hp : IsRegularizedMaximizer hb.le Ω a p := by
    intro s
    rw [hf]
    exact hp₀ s
  have hc : ∀ j, Commute (regularizedFilters hb.le a p j).matrix
      (reducedDensity (output (regularizedFilters hb.le a p) Ω) (X j)) := by
    rw [hf]
    exact hc₀
  refine ⟨p, hp, hc, ?_⟩
  intro j
  refine ⟨?_, regularized_maximizer_clip hb ha hΩ hX hp hc j⟩
  rw [hf]
  exact hd j

end PolynomialPEPS.PinnedEntropy.NestedFilter

end

end OAI
