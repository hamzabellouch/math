import OAI.GroupTheory.PolycyclicRecognition.Analysis.CayleyWordBallAlgebra
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! # The shortest-word length for the fixed symmetric generating set -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type*} [Group G] [DecidableEq G]

theorem wordBall_exhaustive (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ n, g ∈ wordBall S n := by
  let H : Subgroup G := {
    carrier := {x | ∃ n, x ∈ wordBall S n}
    one_mem' := ⟨0, one_mem_wordBall S 0⟩
    mul_mem' := by
      rintro x y ⟨m, hm⟩ ⟨n, hn⟩
      exact ⟨m + n, mul_mem_wordBall hm hn⟩
    inv_mem' := by
      rintro x ⟨n, hn⟩
      exact ⟨n, inv_mem_wordBall hS hn⟩ }
  have hs : Subgroup.closure (S : Set G) ≤ H := (Subgroup.closure_le H).2 (by
    intro s hs
    refine ⟨1, (mem_wordBall_iff S 1 s).mpr ?_⟩
    exact ⟨[s], le_rfl, by simpa using hs, by simp⟩)
  rw [hgen] at hs
  exact hs (Subgroup.mem_top g)

def cayleyWordLength (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) : ℕ :=
  Nat.find (wordBall_exhaustive S hS hgen g)

theorem cayleyWordLength_le_iff (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) (n : ℕ) :
    cayleyWordLength S hS hgen g ≤ n ↔ g ∈ wordBall S n := by
  constructor
  · intro hn
    exact wordBall_mono S hn (Nat.find_spec (wordBall_exhaustive S hS hgen g))
  · exact fun hg => Nat.find_min' _ hg

theorem cayleyWordLength_mul_le (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (x y : G) :
    cayleyWordLength S hS hgen (x * y) ≤
      cayleyWordLength S hS hgen x + cayleyWordLength S hS hgen y := by
  apply (cayleyWordLength_le_iff S hS hgen _ _).mpr
  exact mul_mem_wordBall (Nat.find_spec (wordBall_exhaustive S hS hgen x))
    (Nat.find_spec (wordBall_exhaustive S hS hgen y))

theorem cayleyWordLength_generator_le (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) {s : G} (hs : s ∈ S) :
    cayleyWordLength S hS hgen s ≤ 1 := by
  apply (cayleyWordLength_le_iff S hS hgen _ _).mpr
  exact (mem_wordBall_iff S 1 s).mpr ⟨[s], le_rfl, by simpa using hs, by simp⟩

theorem cayleyWordLength_edge_difference (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (x : G) {s : G} (hs : s ∈ S) :
    |(cayleyWordLength S hS hgen (x * s) : ℝ) - cayleyWordLength S hS hgen x| ≤ 1 := by
  have h₁ := (cayleyWordLength_mul_le S hS hgen x s).trans
    (Nat.add_le_add_left (cayleyWordLength_generator_le S hS hgen hs) _)
  have h₂ := (cayleyWordLength_mul_le S hS hgen (x * s) s⁻¹).trans
    (Nat.add_le_add_left (cayleyWordLength_generator_le S hS hgen (hS s hs)) _)
  simp only [mul_inv_cancel_right] at h₂
  have h₁' : (cayleyWordLength S hS hgen (x * s) : ℝ) ≤
      (cayleyWordLength S hS hgen x : ℝ) + 1 := by exact_mod_cast h₁
  have h₂' : (cayleyWordLength S hS hgen x : ℝ) ≤
      (cayleyWordLength S hS hgen (x * s) : ℝ) + 1 := by exact_mod_cast h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PolycyclicRecognition

end

end OAI
