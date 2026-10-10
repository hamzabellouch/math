import Mathlib.Analysis.Normed.Group.Bounded
import OAI.Geometry.NodalSets.Elliptic.SmoothJet

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T ι : Type*} [TopologicalSpace T] [Fintype ι]

def polynomialFamily (p : ι → CPoly) (c : T → ι → ℂ) (t : T) : Coord → ℂ :=
  fun x ↦ ∑ i, c t i • reval (p i) x

omit [TopologicalSpace T] in
lemma polynomialFamily_contDiff (p : ι → CPoly) (c : T → ι → ℂ) (t : T) :
    ContDiff ℝ ∞ (polynomialFamily p c t) := by
  exact ContDiff.sum (fun i _ ↦ (reval_contDiff (p i)).const_smul (c t i))

omit [TopologicalSpace T] in
lemma polynomialFamily_iteratedFDeriv (p : ι → CPoly) (c : T → ι → ℂ) (t : T)
    (k : ℕ) (x : Coord) :
    iteratedFDeriv ℝ k (polynomialFamily p c t) x =
      ∑ i, c t i • iteratedFDeriv ℝ k (reval (p i)) x := by
  unfold polynomialFamily
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
    (((reval_contDiff (p i)).const_smul (c t i)).of_le
      (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  exact iteratedFDeriv_const_smul_apply'
    ((reval_contDiff (p i)).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt

theorem polynomialFamily_derivative_continuous (p : ι → CPoly) (c : T → ι → ℂ)
    (hc : ∀ i, Continuous (fun t ↦ c t i)) (k : ℕ) :
    Continuous (fun tx : T × Coord ↦ iteratedFDeriv ℝ k (polynomialFamily p c tx.1) tx.2) := by
  simp_rw [polynomialFamily_iteratedFDeriv]
  apply continuous_finsetSum
  intro i _
  exact ((hc i).comp continuous_fst).smul
    (((reval_contDiff (p i)).continuous_iteratedFDeriv (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).comp continuous_snd)

theorem polynomialFamily_uniform_derivative_bound (p : ι → CPoly) (c : T → ι → ℂ)
    (hc : ∀ i, Continuous (fun t ↦ c t i)) (s : Set T) (hs : IsCompact s)
    (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (polynomialFamily p c t) x‖ ≤ C := by
  have hcompact := hs.prod (isCompact_closedBall (0 : Coord) R)
  have hbounded := (hcompact.image (polynomialFamily_derivative_continuous p c hc k)).isBounded
  obtain ⟨C, hC, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  apply hbound
  exact ⟨(t, x), ⟨ht, by simpa using hx⟩, rfl⟩

end
end Yau.Jets

end OAI
