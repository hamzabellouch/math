import OAI.Combinatorics.ProgressionColoring.ConstructionModel
import OAI.Combinatorics.ProgressionColoring.OuterModelChoice
import OAI.Combinatorics.ProgressionColoring.CyclicSignatures
import OAI.Combinatorics.ProgressionColoring.AffineEntropyNat
import OAI.Combinatorics.ProgressionColoring.UniformBudget

namespace OAI

/-!
# The sparse budget for the actual construction

The outer choice contains every actual cyclic label word. Its proved row bound
therefore controls the literal signatures of the actual affine family. All
arithmetic and mesh estimates are discharged for the chosen prime-scale data;
the resulting eventual threshold is uniform over those data and outer choices.
-/

noncomputable section

open Filter

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters SparsePerturbation CyclicColoring

variable {k : ℕ}

@[simp] theorem actualFullLabel_eq_fullLabel (s : Data k) (hk : 3 ≤ k)
    (n : Group s) :
    actualFullLabel (mesh s hk) s.q (dimension k) (lambda k)
      (firstLabel s hk) n = fullLabel s hk n := rfl

@[simp] theorem actualFullLabelWord_eq_fullLabelWord (s : Data k) (hk : 3 ≤ k)
    (ad : Group s × Group s) :
    actualFullLabelWord (k := k) (mesh s hk) s.q (dimension k) (lambda k)
      (firstLabel s hk) ad = fullLabelWord s hk ad := rfl

namespace OuterChoice

theorem words_card_pos {s : Data k} {hk : 3 ≤ k} (o : OuterChoice s hk) :
    0 < o.words.card :=
  Finset.card_pos.mpr ⟨fullLabelWord s hk (0, 0), o.word_mem (0, 0)⟩

theorem card_global_words_le {s : Data k} {hk : 3 ≤ k}
    [NeZero (s.q ^ dimension k)] (o : OuterChoice s hk) :
    ((nonzeroProgressions (s.q ^ dimension k)).image
      (actualFullLabelWord (k := k) (mesh s hk) s.q (dimension k) (lambda k)
        (firstLabel s hk))).card ≤ o.words.card := by
  classical
  apply Finset.card_le_card
  intro w hw
  obtain ⟨ad, _, rfl⟩ := Finset.mem_image.mp hw
  exact o.word_mem ad

/-- The degree-six global row count has entropy constant 520. -/
theorem log_words_card_le {s : Data k} {hk : 3 ≤ k}
    (o : OuterChoice s hk) (hk32 : 32 ≤ k) :
    Real.log (o.words.card : ℝ) ≤
      520 * (k : ℝ) ^ (3 / 10 : ℝ) * Real.log k := by
  let F : ℝ := ((uniformCount k + Fintype.card (mesh s hk).Label : ℕ) : ℝ)
  have hL : (1 : ℝ) ≤ lambda k := by
    exact_mod_cast Nat.succ_le_of_lt (lambda_pos k)
  have hF : (1 : ℝ) ≤ F := by
    dsimp [F]
    exact_mod_cast ((Nat.succ_le_of_lt (uniformCount_pos hk)).trans
      (Nat.le_add_right (uniformCount k) (Fintype.card (mesh s hk).Label)))
  have hLlog : Real.log (lambda k : ℝ) ≤
      (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) := by
    calc
      Real.log (lambda k : ℝ) ≤
          ((dimension k ^ 2 : ℕ) : ℝ) * Real.log (2 * (cutoff k : ℝ)) :=
        log_dilation_le (h₀ := dimension k ^ 2) (cutoff_pos (by omega : 1 ≤ k))
      _ = (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) :=
        congrArg (fun x : ℝ => x * Real.log (2 * (cutoff k : ℝ)))
          (Nat.cast_pow (dimension k) 2)
  have hmesh : F ≤ (k : ℝ) ^ 2 * (lambda k : ℝ) +
      28 * (k : ℝ) ^ 3 * Real.log k := by
    dsimp [F]
    rw [Nat.cast_add, uniformCount, Nat.cast_mul, Nat.cast_pow]
    exact add_le_add_right (card_second_labels_le s hk) _
  have hcount : (o.words.card : ℝ) ≤
      (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ (6 : ℕ)) ^
        (2 * dimension k) := by
    dsimp [F]
    exact_mod_cast o.card_le
  have hpos : (0 : ℝ) < o.words.card := by exact_mod_cast o.words_card_pos
  have h := log_global_count_le (e := 6) hk32 hL hF hpos hLlog hmesh hcount
  norm_num at h
  exact h

/-- The actual affine family retains the actual geometric keys and colors. -/
theorem card_affine_signatures_le {s : Data k} {hk : 3 ≤ k}
    [NeZero (s.q ^ dimension k)] (o : OuterChoice s hk) :
    ((affineProgressions s.q (dimension k) (lambda k) k).image
      (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
        (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card ≤
      o.words.card * (25 * (k * (dimension k * s.q ^ 2 + 1) + 1) ^ 8) := by
  classical
  have h := card_actual_affine_signatures_le
    (mesh s hk) s.q (dimension k) (lambda k) k (firstLabel s hk) o.color
  simp only [actualFullLabel_eq_fullLabel] at h
  exact h.trans (Nat.mul_le_mul_right _ o.card_global_words_le)

/-- Literal affine signatures have entropy constant 628, also when their
finite image is empty. -/
theorem log_affine_signatures_le {s : Data k} {hk : 3 ≤ k}
    [NeZero (s.q ^ dimension k)] (o : OuterChoice s hk) (hk32 : 32 ≤ k) :
    Real.log (max 1
      (((affineProgressions s.q (dimension k) (lambda k) k).image
        (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
          (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card : ℝ)) ≤
      628 * (k : ℝ) ^ (9 / 10 : ℝ) * Real.log k := by
  classical
  have hcount := o.card_affine_signatures_le
  have hcast :
      (((affineProgressions s.q (dimension k) (lambda k) k).image
        (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
          (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card : ℝ) ≤
      (o.words.card : ℝ) * (25 *
        ((k : ℝ) * ((dimension k : ℝ) * (s.q : ℝ) ^ 2 + 1) + 1) ^ 8) := by
    exact_mod_cast hcount
  have hcountR :
      (((affineProgressions s.q (dimension k) (lambda k) k).image
        (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
          (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card : ℝ) ≤
      25 * (o.words.card : ℝ) *
        ((k : ℝ) * ((dimension k : ℝ) * (s.q : ℝ) ^ 2 + 1) + 1) ^ 8 := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcast
  have hG : (1 : ℝ) ≤ o.words.card := by
    exact_mod_cast Nat.succ_le_of_lt o.words_card_pos
  have hq : (1 : ℝ) ≤ s.q := by
    exact_mod_cast (show 1 ≤ s.q by have := s.two_le; omega)
  have hprime := scalar_log_q_le (by omega : 2 ≤ k)
    (s.log_upper (by omega) (dimension_pos (by omega : 1 ≤ k)))
  have h := affine_nat_entropy_bound hk32 hG hq (by norm_num : (0 : ℝ) ≤ 520)
    hcountR (o.log_words_card_le hk32) hprime
  norm_num at h
  exact h

end OuterChoice

/-- A single threshold makes the exact sparse-perturbation budget less than
one for every actual arithmetic datum and every actual outer choice. -/
theorem eventually_outerChoice_sparse_budget :
    ∀ᶠ k : ℕ in atTop, ∀ hk : 3 ≤ k, ∀ s : Data k, ∀ o : OuterChoice s hk,
      letI : NeZero (s.q ^ dimension k) := groupSize_neZero s
      2 * (groupSize s : ℝ) ^ 2 * flipProbability k ^ ((k + 399) / 400) +
        2 * (((affineProgressions s.q (dimension k) (lambda k) k).image
          (cyclicSignature (k := k) (fun n => o.color (fullLabel s hk n))
            (perturbationKey (mesh s hk) s.q (dimension k) (lambda k)))).card : ℝ) *
          (1 - flipProbability k) ^ ((k + 3) / 4) < 1 := by
  filter_upwards [eventually_ge_atTop (32 : ℕ),
    eventually_sparse_budget (C := 628) (by norm_num)] with k hk32 hb hk s o
  let : NeZero (s.q ^ dimension k) := groupSize_neZero s
  exact hb s.q s.pos _
    (s.log_upper (by omega) (dimension_pos (by omega : 1 ≤ k)))
    (o.log_affine_signatures_le hk32)

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
