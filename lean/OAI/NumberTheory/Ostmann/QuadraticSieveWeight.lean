import Mathlib

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

noncomputable def sieveBump : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def sieveWeight : 𝓢(ℝ, ℂ) :=
  (sieveBump.hasCompactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp sieveBump.contDiff)

@[simp] theorem sieveWeight_apply (x : ℝ) : sieveWeight x = (sieveBump x : ℂ) := rfl

theorem sieveBump_nonneg (x : ℝ) : 0 ≤ sieveBump x := sieveBump.nonneg

theorem sieveBump_le_one (x : ℝ) : sieveBump x ≤ 1 := sieveBump.le_one

theorem sieveBump_one {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) : sieveBump x = 1 := by
  apply sieveBump.one_of_mem_closedBall
  change |x - 3 / 2| ≤ 1 / 2
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem sieveBump_zero {x : ℝ} (hx : x ≤ 1 / 2 ∨ 5 / 2 ≤ x) : sieveBump x = 0 := by
  apply sieveBump.zero_of_le_dist
  change (1 : ℝ) ≤ |x - 3 / 2|
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

@[simp] theorem sieveWeight_one {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) : sieveWeight x = 1 := by
  simp [sieveBump_one hx]

theorem sieveWeight_zero {x : ℝ} (hx : x ≤ 1 / 2 ∨ 5 / 2 ≤ x) : sieveWeight x = 0 := by
  simp [sieveBump_zero hx]

theorem sieveWeight_compact : HasCompactSupport sieveWeight :=
  sieveBump.hasCompactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) rfl

theorem sieveWeight_support_pos : tsupport sieveWeight ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  have hs : Function.support sieveWeight ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2) := by
    intro y hy
    have hn : sieveWeight y ≠ 0 := hy
    constructor <;> by_contra h
    · exact hn (sieveWeight_zero (Or.inl (le_of_not_ge h)))
    · exact hn (sieveWeight_zero (Or.inr (le_of_not_ge h)))
  have hcl := closure_minimal hs isClosed_Icc hx
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hcl.1

end Ostmann.QuadraticSieve

end OAI
