import OAI.Analysis.MarkovType.JConvexityBasic
import OAI.Analysis.MarkovType.TriangularBasic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

structure ApproximateTailSystem (n : ℕ) (η : ℝ) where
  vectors : Fin n → X
  functionals : Fin n → StrongDual ℝ X
  vectors_bound : ∀ i, ‖vectors i‖ ≤ 1
  functionals_bound : ∀ j, ‖functionals j‖ ≤ 1
  pairing_error : ∀ i j,
    |functionals j (vectors i) - (if j ≤ i then (1 : ℝ) else 0)| ≤ η

variable {X}

theorem exists_large_cut_sums_of_not_jConvex (h : ¬ AmbientJConvex X)
    (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) ∧
      ∀ r : Fin n, (n : ℝ) * (1 - δ) < ‖cutSum x r‖ := by
  classical
  by_contra hex
  apply h
  refine ⟨n, hn, δ, hδ, hδ1, ?_⟩
  intro x hx
  by_contra hcut
  apply hex
  refine ⟨x, hx, ?_⟩
  intro r
  exact lt_of_not_ge (fun hr => hcut ⟨r, hr⟩)

theorem norming_cut_entry_error {n : ℕ} {δ : ℝ}
    (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ 1) (r : Fin n)
    (g : StrongDual ℝ X) (hg : ‖g‖ ≤ 1)
    (hgnorm : g (cutSum x r) = ‖cutSum x r‖)
    (hcut : (n : ℝ) * (1 - δ) < ‖cutSum x r‖) (i : Fin n) :
    |g (x i) - cutSign r i| < (n : ℝ) * δ := by
  classical
  have hvalue (j : Fin n) : |g (x j)| ≤ 1 := by
    calc
      |g (x j)| = ‖g (x j)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖g‖ * ‖x j‖ := g.le_opNorm (x j)
      _ ≤ 1 * 1 := mul_le_mul hg (hx j) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hsigned (j : Fin n) : cutSign r j * g (x j) ≤ 1 := by
    calc
      cutSign r j * g (x j) ≤ |cutSign r j * g (x j)| := le_abs_self _
      _ = |g (x j)| := by rw [abs_mul, abs_cutSign, one_mul]
      _ ≤ 1 := hvalue j
  have hdeficit (j : Fin n) : 0 ≤ 1 - cutSign r j * g (x j) :=
    sub_nonneg.mpr (hsigned j)
  have hsum : ∑ j : Fin n, cutSign r j * g (x j) = ‖cutSum x r‖ := by
    rw [← hgnorm]
    simp only [cutSum, map_sum, map_smul, smul_eq_mul]
  have htotal : (∑ j : Fin n, (1 - cutSign r j * g (x j))) =
      (n : ℝ) - ‖cutSum x r‖ := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have hone : 1 - cutSign r i * g (x i) ≤
      ∑ j : Fin n, (1 - cutSign r j * g (x j)) :=
    Finset.single_le_sum (fun j _ => hdeficit j) (Finset.mem_univ i)
  have herror : |g (x i) - cutSign r i| = 1 - cutSign r i * g (x i) := by
    by_cases hir : i < r
    · simp only [cutSign, ite_eq_left hir, one_mul]
      rw [abs_of_nonpos (sub_nonpos.mpr (abs_le.mp (hvalue i)).2)]
      ring
    · simp only [cutSign, ite_eq_right hir, neg_one_mul, sub_neg_eq_add]
      rw [abs_of_nonneg (by linarith [(abs_le.mp (hvalue i)).1] : 0 ≤ g (x i) + 1)]
      ring
  rw [herror]
  rw [htotal] at hone
  nlinarith

theorem exists_approximate_tail_of_cut_functionals {n : ℕ} (hn : 0 < n)
    (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ 1)
    (g : Fin n → StrongDual ℝ X) (hg : ∀ r, ‖g r‖ ≤ 1)
    (η : ℝ) (herror : ∀ r i, |g r (x i) - cutSign r i| ≤ η) :
    Nonempty (ApproximateTailSystem X n η) := by
  classical
  let z : Fin n := ⟨0, hn⟩
  let φ : Fin n → StrongDual ℝ X := fun j => (- (1 / 2) : ℝ) • (g j + g z)
  have hz (i : Fin n) : cutSign z i = -1 := by
    have hiz : ¬ i < z := by
      change ¬ i.val < 0
      exact Nat.not_lt_zero i.val
    simp only [cutSign, ite_eq_right hiz]
  have hφbound (j : Fin n) : ‖φ j‖ ≤ 1 := by
    calc
      ‖φ j‖ = (1 / 2 : ℝ) * ‖g j + g z‖ := by
        dsimp [φ]
        rw [norm_smul (α := ℝ) (x := g j + g z)]
        norm_num
      _ ≤ (1 / 2 : ℝ) * (‖g j‖ + ‖g z‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ 1 := by linarith [hg j, hg z]
  have hφerror (i j : Fin n) :
      |φ j (x i) - (if j ≤ i then (1 : ℝ) else 0)| ≤ η := by
    have hid : φ j (x i) - (if j ≤ i then (1 : ℝ) else 0) =
        (- (1 / 2) : ℝ) *
          ((g j (x i) - cutSign j i) + (g z (x i) - cutSign z i)) := by
      simp only [φ, smul_apply, add_apply,
        smul_eq_mul, hz]
      by_cases hij : i < j
      · simp only [cutSign, ite_eq_left hij, ite_eq_right (not_le_of_gt hij)]
        ring
      · simp only [cutSign, ite_eq_right hij, ite_eq_left (le_of_not_gt hij)]
        ring
    rw [hid, abs_mul]
    have hhalf : |(- (1 / 2) : ℝ)| = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    calc
      (1 / 2 : ℝ) *
          |(g j (x i) - cutSign j i) + (g z (x i) - cutSign z i)|
          ≤ (1 / 2 : ℝ) *
            (|g j (x i) - cutSign j i| + |g z (x i) - cutSign z i|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
      _ ≤ η := by linarith [herror j i, herror z i]
  exact ⟨⟨x, φ, hx, hφbound, hφerror⟩⟩

theorem approximateTailSystem_of_not_jConvex (h : ¬ AmbientJConvex X)
    (n : ℕ) (hn : 2 ≤ n) (η : ℝ) (hη : 0 < η) :
    Nonempty (ApproximateTailSystem X n η) := by
  classical
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let δ : ℝ := min (η / (2 * (n : ℝ))) (1 / 2)
  have hδ : 0 < δ := by
    exact lt_min (div_pos hη (mul_pos (by norm_num) hnreal)) (by norm_num)
  have hδ1 : δ < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδbound : (n : ℝ) * δ ≤ η := by
    have hle : δ ≤ η / (2 * (n : ℝ)) := min_le_left _ _
    have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hnreal)).mp hle
    nlinarith
  obtain ⟨x, hx, hcut⟩ := exists_large_cut_sums_of_not_jConvex h n hn δ hδ hδ1
  have hdual : ∀ r : Fin n, ∃ g : StrongDual ℝ X,
      ‖g‖ ≤ 1 ∧ g (cutSum x r) = ‖cutSum x r‖ :=
    fun r => exists_dual_vector'' ℝ (cutSum x r)
  choose g hg hgnorm using hdual
  apply exists_approximate_tail_of_cut_functionals hnpos x hx g hg η
  intro r i
  exact (norming_cut_entry_error x hx r (g r) (hg r) (hgnorm r) (hcut r) i).le.trans hδbound

end MarkovSuperreflexivity

end

end OAI
