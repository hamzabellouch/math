import OAI.NumberTheory.DukePrimeDegree.Geometry.RootCurveExtraction
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-!
# The actual vector space of subgroup velocities

Velocities are derivatives of genuine curves in the subgroup at its
identity. Multiplication adds velocities and a linear reparametrization
scales them. Conjugating the subgroup conjugates this vector space.
No Lie-subgroup or homogeneous-support assertion is assumed here.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def HasIdentityMatrixDerivative {n : ℕ} (γ : ℝ → G n)
    (V : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  γ 0 = 1 ∧ ∀ i j, HasDerivAt (fun t => (γ t).val i j) (V i j) 0

lemma HasIdentityMatrixDerivative.hasMatrixVelocity {n : ℕ}
    {γ : ℝ → G n} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : HasIdentityMatrixDerivative γ V) : HasMatrixVelocity γ V :=
  hasMatrixVelocity_of_hasDerivAt γ h.1 V h.2

lemma HasIdentityMatrixDerivative.mul {n : ℕ}
    {γ δ : ℝ → G n} {V W : Matrix (Fin n) (Fin n) ℝ}
    (hγ : HasIdentityMatrixDerivative γ V) (hδ : HasIdentityMatrixDerivative δ W) :
    HasIdentityMatrixDerivative (fun t => γ t * δ t) (V + W) := by
  refine ⟨by simp only [hγ.1, hδ.1, mul_one], ?_⟩
  intro i j
  have hd := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hγ.2 i k).mul (hδ.2 k j))
  convert hd using 1
  · funext t
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_apply,
      Pi.mul_apply]
  · simp only [Finset.sum_add_distrib, ← Matrix.mul_apply, hγ.1, hδ.1,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply]

lemma HasIdentityMatrixDerivative.reparametrize {n : ℕ}
    {γ : ℝ → G n} {V : Matrix (Fin n) (Fin n) ℝ}
    (hγ : HasIdentityMatrixDerivative γ V) (c : ℝ) :
    HasIdentityMatrixDerivative (fun t => γ (c * t)) (c • V) := by
  refine ⟨by simpa only [mul_zero] using hγ.1, ?_⟩
  intro i j
  have hc : HasDerivAt (fun t : ℝ => c * t) c 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul c
  have houter : HasDerivAt (fun t => (γ t).val i j) (V i j) (c * 0) := by
    simpa only [mul_zero] using hγ.2 i j
  simpa only [mul_zero, Function.comp_def, Matrix.smul_apply, smul_eq_mul, mul_comm] using
    houter.comp 0 hc

/-- The finite-dimensional real subspace comes from actual subgroup
curves. In particular, it is not an arbitrary assigned frame. -/
def matrixVelocitySpace {n : ℕ} (H : Subgroup (G n)) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {V | ∃ γ : ℝ → G n, (∀ t, γ t ∈ H) ∧ HasIdentityMatrixDerivative γ V}
  zero_mem' := by
    refine ⟨fun _ => 1, fun _ => H.one_mem, rfl, ?_⟩
    intro i j
    simpa only [Matrix.zero_apply] using hasDerivAt_const (0 : ℝ)
      ((1 : G n).val i j)
  add_mem' := by
    rintro V W ⟨γ, hγH, hγ⟩ ⟨δ, hδH, hδ⟩
    exact ⟨fun t => γ t * δ t, fun t => H.mul_mem (hγH t) (hδH t), hγ.mul hδ⟩
  smul_mem' := by
    rintro c V ⟨γ, hγH, hγ⟩
    exact ⟨fun t => γ (c * t), fun t => hγH _, hγ.reparametrize c⟩

lemma matrixVelocitySpace_mono {n : ℕ} {H L : Subgroup (G n)} (hHL : H ≤ L) :
    matrixVelocitySpace H ≤ matrixVelocitySpace L := by
  rintro V ⟨γ, hγ, hd⟩
  exact ⟨γ, fun t => hHL (hγ t), hd⟩

/-- Finite-dimensionality makes the actual velocity space closed; no
closed-subgroup theorem is required for this linear fact. -/
lemma isClosed_matrixVelocitySpace {n : ℕ} (H : Subgroup (G n)) :
    IsClosed (matrixVelocitySpace H : Set (Matrix (Fin n) (Fin n) ℝ)) :=
  (matrixVelocitySpace H).closed_of_finiteDimensional

private lemma hasDerivAt_matrix_mul_const {n : ℕ}
    (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (V B : Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i j, HasDerivAt (fun t => F t i j) (V i j) 0) (i j : Fin n) :
    HasDerivAt (fun t => (F t * B) i j) ((V * B) i j) 0 := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun k _ => (hF i k).mul_const (B k j))
  convert hd using 1
  · funext t
    simp only [Matrix.mul_apply, Finset.sum_apply]
  · rfl

private lemma hasDerivAt_const_matrix_mul {n : ℕ}
    (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (V B : Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i j, HasDerivAt (fun t => F t i j) (V i j) 0) (i j : Fin n) :
    HasDerivAt (fun t => (B * F t) i j) ((B * V) i j) 0 := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun k _ => (hF k j).const_mul (B i k))
  convert hd using 1
  · funext t
    simp only [Matrix.mul_apply, Finset.sum_apply]
  · rfl

lemma HasIdentityMatrixDerivative.conjugate {n : ℕ}
    {γ : ℝ → G n} {V : Matrix (Fin n) (Fin n) ℝ}
    (hγ : HasIdentityMatrixDerivative γ V) (a : G n) :
    HasIdentityMatrixDerivative (fun t => a * γ t * a⁻¹)
      (a.val * V * a⁻¹.val) := by
  refine ⟨by simp only [hγ.1, mul_one, mul_inv_cancel], ?_⟩
  intro i j
  have hleft := hasDerivAt_const_matrix_mul (fun t => (γ t).val) V a.val hγ.2
  have hfull := hasDerivAt_matrix_mul_const (fun t => a.val * (γ t).val)
    (a.val * V) a⁻¹.val hleft i j
  simpa only [Matrix.SpecialLinearGroup.coe_mul] using hfull

/-- Conjugation acts on the actual curve-velocity spaces. This is the
covariance needed before applying finite-dimensional recurrence. -/
theorem conjugate_mem_matrixVelocitySpace {n : ℕ}
    (H L : Subgroup (G n)) (a : G n)
    (hconj : ∀ h ∈ H, a * h * a⁻¹ ∈ L)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ matrixVelocitySpace H) :
    a.val * V * a⁻¹.val ∈ matrixVelocitySpace L := by
  obtain ⟨γ, hγ, hd⟩ := hV
  exact ⟨fun t => a * γ t * a⁻¹, fun t => hconj (γ t) (hγ t), hd.conjugate a⟩

end DukePrimeDegree

end

end OAI
