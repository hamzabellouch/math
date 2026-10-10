import OAI.GroupTheory.PolycyclicRecognition.Analysis.CayleyBallCutoff
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace OAI

/-! # Finite-dimensional function spaces are detected on a word ball

This supplies positivity of the expanding quadratic forms used in the
harmonic-function dimension argument.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

def wordBallVanishing (S : Finset G) (R : ℕ) (V : Submodule ℝ (G → ℝ)) : Submodule ℝ V where
  carrier := {f | ∀ x ∈ wordBall S R, f.val x = 0}
  zero_mem' := by intro x _; rfl
  add_mem' := by intro f g hf hg x hx; change f.val x + g.val x = 0; rw [hf x hx, hg x hx, add_zero]
  smul_mem' := by intro c f hf x hx; change c * f.val x = 0; rw [hf x hx, mul_zero]

theorem wordBallVanishing_antitone (S : Finset G) (V : Submodule ℝ (G → ℝ)) :
    Antitone (fun R => wordBallVanishing S R V) := by
  intro m n hmn f hf x hx
  exact hf x (wordBall_mono S hmn hx)

theorem exists_wordBall_detects_finiteDimensional_functions
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (V : Submodule ℝ (G → ℝ)) [Module.Finite ℝ V] :
    ∃ R : ℕ, ∀ f : V, (∀ x ∈ wordBall S R, f.val x = 0) → f = 0 := by
  let K : ℕ →o (Submodule ℝ V)ᵒᵈ :=
    ⟨fun R => wordBallVanishing S R V, wordBallVanishing_antitone S V⟩
  obtain ⟨R, hR⟩ := IsArtinian.monotone_stabilizes K
  refine ⟨R, fun f hf => ?_⟩
  apply Subtype.ext
  funext x
  obtain ⟨n, hn⟩ := wordBall_exhaustive S hS hgen x
  have he : wordBallVanishing S R V = wordBallVanishing S (max R n) V :=
    hR (max R n) (le_max_left _ _)
  have hf' : f ∈ wordBallVanishing S (max R n) V := he ▸ hf
  exact hf' x (wordBall_mono S (le_max_right _ _) hn)

def wordBallQuadraticValue (S : Finset G) (R : ℕ) (f : G → ℝ) : ℝ :=
  ∑ x ∈ wordBall S R, (f x) ^ 2

theorem wordBallQuadraticValue_nonneg (S : Finset G) (R : ℕ) (f : G → ℝ) :
    0 ≤ wordBallQuadraticValue S R f := sum_nonneg (fun _ _ => sq_nonneg _)

theorem wordBallQuadraticValue_mono (S : Finset G) (f : G → ℝ) :
    Monotone (fun R => wordBallQuadraticValue S R f) := by
  intro m n hmn
  exact sum_le_sum_of_subset_of_nonneg (wordBall_mono S hmn) (fun _ _ _ => sq_nonneg _)

theorem exists_wordBallQuadraticValue_positive
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (V : Submodule ℝ (G → ℝ)) [Module.Finite ℝ V] :
    ∃ R : ℕ, ∀ f : V, f ≠ 0 → 0 < wordBallQuadraticValue S R f.val := by
  obtain ⟨R, hR⟩ := exists_wordBall_detects_finiteDimensional_functions S hS hgen V
  refine ⟨R, fun f hf => ?_⟩
  have hn : ∃ x ∈ wordBall S R, f.val x ≠ 0 := by
    by_contra! h
    exact hf (hR f h)
  obtain ⟨x, hx, hfx⟩ := hn
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hfx)
    (single_le_sum (fun _ _ => sq_nonneg _) hx)

def wordBallQuadraticForm (S : Finset G) (R : ℕ) (V : Submodule ℝ (G → ℝ)) :
    QuadraticForm ℝ V :=
  ∑ x ∈ wordBall S R, (QuadraticMap.sq : QuadraticForm ℝ ℝ).comp
    ((LinearMap.proj x : (G → ℝ) →ₗ[ℝ] ℝ).comp V.subtype)

@[simp] theorem wordBallQuadraticForm_apply (S : Finset G) (R : ℕ)
    (V : Submodule ℝ (G → ℝ)) (f : V) :
    wordBallQuadraticForm S R V f = wordBallQuadraticValue S R f.val := by
  simp [wordBallQuadraticForm, wordBallQuadraticValue, QuadraticMap.sq_apply, pow_two]

theorem exists_wordBallQuadraticForm_posDef
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (V : Submodule ℝ (G → ℝ)) [Module.Finite ℝ V] :
    ∃ R : ℕ, (wordBallQuadraticForm S R V).PosDef := by
  obtain ⟨R, hR⟩ := exists_wordBallQuadraticValue_positive S hS hgen V
  exact ⟨R, fun f hf => by simpa only [wordBallQuadraticForm_apply] using hR f hf⟩

end PolycyclicRecognition

end

end OAI
