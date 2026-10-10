import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ScoreDegreeLowNormalized

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

lemma power_tail_card {T : Type*} [Fintype T] (f : T→ℝ) (hf : ∀ z,0 ≤ f z)
    (k : ℕ) (t M : ℝ) (ht : 0 < t) (hM : (∑ z,f z^k) ≤ M) :
    ((Finset.univ.filter fun z => t ≤ f z).card:ℝ) ≤ M/t^k := by
  apply (le_div_iff₀ (pow_pos ht k)).mpr
  calc
    _ = ∑ z∈Finset.univ.filter (fun z => t ≤ f z),t^k := by simp
    _ ≤ ∑ z∈Finset.univ.filter (fun z => t ≤ f z),f z^k := by
      apply Finset.sum_le_sum
      intro z hz
      exact pow_le_pow_left₀ ht.le (Finset.mem_filter.mp hz).2 k
    _ ≤ ∑ z,f z^k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro z _ _; exact pow_nonneg (hf z) k)
    _ ≤ M := hM

noncomputable def lowMomentBudget (Q M A B b L : ℝ) (p R N₁ N₂ : ℕ) : ℝ :=
  certificateMajorant Q M B b L p R 200 N₁ N₂ +
    (1+(p:ℝ)^200*A)+B+(Q/B+(p:ℝ)^200*(M/B))

lemma lowMomentBudget_bounds (Q M A B b L : ℝ) (p R N₁ N₂ : ℕ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 < B)
    (hb : 0 ≤ b) (hL : 0 ≤ L) :
    0 ≤ lowMomentBudget Q M A B b L p R N₁ N₂ ∧
    certificateMajorant Q M B b L p R 200 N₁ N₂ ≤ lowMomentBudget Q M A B b L p R N₁ N₂ ∧
    1+(p:ℝ)^200*A ≤ lowMomentBudget Q M A B b L p R N₁ N₂ ∧
    Q+(p:ℝ)^200*M ≤ (lowMomentBudget Q M A B b L p R N₁ N₂)^2 := by
  have hc := certificateMajorant_nonneg Q M B b L p R 200 N₁ N₂ hQ hM hB.le hb hL
  have hrow : 0 ≤ 1+(p:ℝ)^200*A := by positivity
  have hx : 0 ≤ Q/B+(p:ℝ)^200*(M/B) := by positivity
  have hCB : B ≤ lowMomentBudget Q M A B b L p R N₁ N₂ := by
    unfold lowMomentBudget; linarith
  have hCx : Q/B+(p:ℝ)^200*(M/B) ≤ lowMomentBudget Q M A B b L p R N₁ N₂ := by
    unfold lowMomentBudget; linarith
  have hC := hB.le.trans hCB
  refine ⟨hC,?_,?_,?_⟩
  · unfold lowMomentBudget; linarith
  · unfold lowMomentBudget; linarith
  · calc
      _ = B*(Q/B+(p:ℝ)^200*(M/B)) := by field_simp
      _ ≤ lowMomentBudget Q M A B b L p R N₁ N₂ *
          lowMomentBudget Q M A B b L p R N₁ N₂ := mul_le_mul hCB hCx hx hC
      _ = _ := (sq _).symm

end SharpRamseyFive.ScoreGeometry

end OAI
