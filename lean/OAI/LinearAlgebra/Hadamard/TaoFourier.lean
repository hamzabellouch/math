import OAI.LinearAlgebra.Hadamard.Fourier
import OAI.LinearAlgebra.Hadamard.TaoSymmetry

namespace OAI

/-! Fourier norm invariance for the cubic matrix under permutations and negation. -/

namespace HadamardSix.CubicSymmetry

lemma character_star (x : Index → ℂ) (a : Charge) :
    character (fun i => star (x i)) a = star (character x a) := by
  unfold character
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (map_zpow₀ (starRingEnd ℂ) (x i) (a i)).symm

lemma g_star (H : Matrix6) (a : Charge) :
    g (fun i j => star (H i j)) a = star (g H a) := by
  simp only [g, character_star, star_mul, star_sum, star_inv₀, star_ofNat]
  ring

lemma norm_g_phases_columns (H : Matrix6) {a : Charge}
    (ha : Balanced a) (q : Equiv.Perm Index)
    (U V : Index → ℂ)
    (hU : ∀ i, ‖U i‖ = 1)
    (hV : ∀ j, ‖V j‖ = 1) :
    ‖g (fun i j => U i * H i (q j) * V j) a‖ = ‖g H a‖ := by
  have hc := g_column_phases (fun i j => U i * H i (q j))
    ha V (fun j => unit_ne_zero (hV j))
  have hr := g_row_phases (fun i j => H i (q j)) a U
  have hp := g_permute_columns H a q
  have heq : g (fun i j => U i * H i (q j) * V j) a =
      character U a * g H a :=
    hc.trans (hr.trans (congrArg (fun z : ℂ => character U a * z) hp))
  calc
    ‖g (fun i j => U i * H i (q j) * V j) a‖ =
        ‖character U a * g H a‖ := congrArg (fun z : ℂ => ‖z‖) heq
    _ = ‖g H a‖ := by
      rw [norm_mul, character_norm U hU a, one_mul]

/-- The Fourier norm of the cubic matrix is invariant under all permutations of a balanced
charge. -/
theorem norm_g_permute (a : Charge) (ha : Balanced a)
    (p : Equiv.Perm Index) :
    ‖g taoMatrix (permuteCharge p a)‖ = ‖g taoMatrix a‖ := by
  classical
  obtain ⟨q, conjugate, U, V, hU, hV, he⟩ :=
    every_row_permutation_complex p.symm
  let K : Matrix6 := fun i j =>
    if conjugate then star (taoMatrix i j) else taoMatrix i j
  have hrow :
      (fun i j => taoMatrix (p.symm i) j) =
        (fun i j => U i * K i (q.symm j) * V (q.symm j)) := by
    funext i j
    calc
      taoMatrix (p.symm i) j =
          U i * V (q.symm j) * K i (q.symm j) := by
        simpa [K] using he i (q.symm j)
      _ = U i * K i (q.symm j) * V (q.symm j) := by ring
  calc
    ‖g taoMatrix (permuteCharge p a)‖ =
        ‖g (fun i j => U i * K i (q.symm j) * V (q.symm j)) a‖ := by
      rw [g_permuteCharge, hrow]
    _ = ‖g K a‖ :=
      norm_g_phases_columns K ha q.symm U
        (fun j => V (q.symm j)) hU (fun j => hV (q.symm j))
    _ = ‖g taoMatrix a‖ := by
      cases conjugate with
      | false => rfl
      | true =>
        change ‖g (fun i j => star (taoMatrix i j)) a‖ = ‖g taoMatrix a‖
        rw [g_star]
        simp

/-- Negation preserves the Fourier norm even without a balance assumption. -/
theorem norm_g_neg (a : Charge) :
    ‖g taoMatrix (-a)‖ = ‖g taoMatrix a‖ := by
  rw [g_neg tao_unimodular]
  simp

/-- Signed permutations preserve the Fourier norm of every balanced charge. -/
theorem norm_g_signed_permute (a : Charge) (ha : Balanced a)
    (p : Equiv.Perm Index) (negate : Bool) :
    ‖g taoMatrix
        (if negate then -(permuteCharge p a) else permuteCharge p a)‖ =
      ‖g taoMatrix a‖ := by
  cases negate with
  | false => exact norm_g_permute a ha p
  | true =>
    exact (norm_g_neg (permuteCharge p a)).trans (norm_g_permute a ha p)

/-- Every row permutation of the cubic matrix extends using column permutations, unit
phases and optional conjugation, and its Fourier norm is invariant under signed permutations
of balanced charges. -/
def FullCubicSymmetry : Prop :=
  (∀ p : Equiv.Perm Index,
    ∃ (q : Equiv.Perm Index) (conjugate : Bool) (U V : Index → ℂ),
      (∀ i, ‖U i‖ = 1) ∧ (∀ j, ‖V j‖ = 1) ∧
      ∀ i j, taoMatrix (p i) (q j) =
        U i * V j * (if conjugate then star (taoMatrix i j) else taoMatrix i j)) ∧
  (∀ (a : Charge), Balanced a → ∀ (p : Equiv.Perm Index) (negate : Bool),
    ‖g taoMatrix (if negate then -(permuteCharge p a) else permuteCharge p a)‖ =
      ‖g taoMatrix a‖)

theorem cubic_symmetry : FullCubicSymmetry := by
  constructor
  · exact every_row_permutation_complex
  · intro a ha p negate
    exact norm_g_signed_permute a ha p negate

end HadamardSix.CubicSymmetry

end OAI
