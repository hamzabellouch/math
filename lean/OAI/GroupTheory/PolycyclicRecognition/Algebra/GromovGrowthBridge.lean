import OAI.GroupTheory.PolycyclicRecognition.Algebra.GromovInput
import Gromov.PolynomialGrowth

namespace OAI

/-!
# Gromov's theorem from Aaron Hill's formalization

Aaron Hill's `FormalConjecturesCheck.gromov_forward` proves Gromov's
polynomial-growth theorem for arbitrary groups. Its list-defined Cayley balls
agree with the finite word balls used here, and their polynomial bounds
are equivalent without an additional finite-generation or countability hypothesis.
-/

namespace PolycyclicRecognition

universe u
variable {J : Type u} [Group J] [DecidableEq J]

/-- For symmetric generators the two concrete definitions of word ball agree. -/
theorem cayleyBall_eq_wordBall (T : Finset J)
    (hT : ∀ t ∈ T, t⁻¹ ∈ T) (n : ℕ) :
    FormalConjecturesCheck.CayleyBall (T : Set J) n = (wordBall T n : Set J) := by
  ext g
  rw [Finset.mem_coe, mem_wordBall_iff]
  constructor
  · rintro ⟨l, hl, hm, hp⟩
    refine ⟨l, hl, fun t ht => ?_, hp⟩
    rcases hm t ht with h | h
    · exact h
    · simpa only [inv_inv] using hT t⁻¹ h
  · rintro ⟨l, hl, hm, hp⟩
    exact ⟨l, hl, fun t ht => Or.inl (hm t ht), hp⟩

/-- The imported theorem's growth function counts exactly our finite ball. -/
theorem growthFunction_eq_card_wordBall (T : Finset J)
    (hT : ∀ t ∈ T, t⁻¹ ∈ T) (n : ℕ) :
    FormalConjecturesCheck.GrowthFunction (T : Set J) n = (wordBall T n).card := by
  rw [FormalConjecturesCheck.GrowthFunction, cayleyBall_eq_wordBall T hT,
    Set.ncard_coe_finset]

/-- The positive real constant in the imported growth convention can absorb
both the shift by one and a possibly zero natural constant. -/
theorem hasPolynomialGrowth_of_wordBall (T : Finset J)
    (hT : ∀ t ∈ T, t⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set J) = ⊤)
    (hgrowth : ∃ C b : ℕ, ∀ n, (wordBall T n).card ≤ C * (1 + n) ^ b) :
    FormalConjecturesCheck.HasPolynomialGrowth J := by
  obtain ⟨C, b, h⟩ := hgrowth
  refine ⟨(T : Set J), T.finite_toSet, hgen, ((C : ℝ) + 1) * 2 ^ b, b,
    mul_pos (by positivity) (by positivity), ?_⟩
  intro n hn
  rw [growthFunction_eq_card_wordBall T hT]
  have hcard : ((wordBall T n).card : ℝ) ≤ (C : ℝ) * (1 + (n : ℝ)) ^ b := by
    exact_mod_cast h n
  have hshift : (1 : ℝ) + n ≤ 2 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc
    ((wordBall T n).card : ℝ) ≤ (C : ℝ) * (1 + (n : ℝ)) ^ b := hcard
    _ ≤ ((C : ℝ) + 1) * (2 * (n : ℝ)) ^ b := by gcongr; linarith
    _ = (((C : ℝ) + 1) * 2 ^ b) * (n : ℝ) ^ b := by rw [mul_pow]; ring

end PolycyclicRecognition

end OAI
