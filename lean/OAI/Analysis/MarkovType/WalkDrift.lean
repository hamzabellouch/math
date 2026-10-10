import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Analysis.MarkovType.WordReduction
import OAI.Analysis.MarkovType.WeightedEvents

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity.FiniteWalkDrift

variable {A : Type*} [sectionFintypeA : Fintype A]

noncomputable def uniformWordMean (n : ℕ) (F : (Fin n → A) → ℝ) : ℝ :=
  ((4 : ℝ)⁻¹) ^ n * ∑ w, F w

theorem sum_word_snoc (n : ℕ) (F : (Fin (n + 1) → A) → ℝ) :
    (∑ w, F w) = ∑ u : Fin n → A, ∑ a : A, F (Fin.snoc u a) := by
  classical
  calc
    (∑ w, F w) = ∑ p : A × (Fin n → A), F (Fin.snoc p.2 p.1) := by
      exact (Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => A)) F).symm
    _ = ∑ u : Fin n → A, ∑ a : A, F (Fin.snoc u a) :=
      Fintype.sum_prod_type_right _

theorem uniformWordMean_nonneg (n : ℕ) (F : (Fin n → A) → ℝ)
    (hF : ∀ w, 0 ≤ F w) : 0 ≤ uniformWordMean n F := by
  unfold uniformWordMean
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun w _ => hF w)

theorem uniformWordMean_mono (n : ℕ) (F G : (Fin n → A) → ℝ)
    (hFG : ∀ w, F w ≤ G w) : uniformWordMean n F ≤ uniformWordMean n G := by
  unfold uniformWordMean
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun w _ => hFG w)

theorem uniformWordMean_add (n : ℕ) (F G : (Fin n → A) → ℝ) :
    uniformWordMean n (fun w => F w + G w) =
      uniformWordMean n F + uniformWordMean n G := by
  simp only [uniformWordMean, Finset.sum_add_distrib, mul_add]

theorem uniformWordMean_const (hcard : Fintype.card A = 4) (n : ℕ) (c : ℝ) :
    uniformWordMean n (fun _ : Fin n → A => c) = c := by
  classical
  have hc : (Fintype.card (Fin n → A) : ℝ) = (4 : ℝ) ^ n := by
    simp only [Fintype.card_fun, Fintype.card_fin, hcard, Nat.cast_pow, Nat.cast_ofNat]
  rw [uniformWordMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  calc
    ((4 : ℝ)⁻¹) ^ n * ((4 : ℝ) ^ n * c) = (((4 : ℝ)⁻¹) * 4) ^ n * c := by
      rw [mul_pow]
      ring
    _ = c := by norm_num

theorem uniformWordMass_sum (hcard : Fintype.card A = 4) (n : ℕ) :
    (∑ _w : Fin n → A, ((4 : ℝ)⁻¹) ^ n) = 1 := by
  have h := uniformWordMean_const (A := A) hcard n 1
  simpa only [uniformWordMean, Finset.mul_sum, mul_one] using h

theorem uniformWordMean_snoc (n : ℕ) (F : (Fin (n + 1) → A) → ℝ) :
    uniformWordMean (n + 1) F =
      uniformWordMean n (fun u => (4 : ℝ)⁻¹ * ∑ a : A, F (Fin.snoc u a)) := by
  simp only [uniformWordMean, sum_word_snoc, pow_succ, Finset.mul_sum, mul_assoc]

theorem fixed_prefix_extension_sum [DecidableEq A]
    (n : ℕ) (u : Fin n → A) (f : A → ℝ) :
    (∑ w : Fin (n + 1) → A,
      if Fin.init w = u then ((4 : ℝ)⁻¹) ^ (n + 1) * f (w (Fin.last n)) else 0) =
    ((4 : ℝ)⁻¹) ^ n * ((4 : ℝ)⁻¹ * ∑ a, f a) := by
  classical
  rw [sum_word_snoc]
  simp only [Fin.init_snoc, Fin.snoc_last]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, pow_succ]
  ring

theorem fixed_prefix_mass [DecidableEq A]
    (hcard : Fintype.card A = 4) (n : ℕ) (u : Fin n → A) :
    (∑ w : Fin (n + 1) → A,
      if Fin.init w = u then ((4 : ℝ)⁻¹) ^ (n + 1) else 0) = ((4 : ℝ)⁻¹) ^ n := by
  have h := fixed_prefix_extension_sum n u (fun _ => (1 : ℝ))
  simpa only [mul_one, Finset.sum_const, Finset.card_univ, hcard,
    nsmul_eq_mul, Nat.cast_ofNat, inv_mul_cancel₀ (by norm_num : (4 : ℝ) ≠ 0)] using h

omit sectionFintypeA in
theorem list_ofFn_snoc [Fintype A] (n : ℕ) (u : Fin n → A) (a : A) :
    List.ofFn (Fin.snoc u a) = List.ofFn u ++ [a] := by
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

theorem uniformWordMean_length_succ (hcard : Fintype.card A = 4)
    (lengthFn : List A → ℕ)
    (happend : ∀ w : List A,
      4 * lengthFn w + 2 ≤ ∑ a : A, lengthFn (w ++ [a]))
    (n : ℕ) :
    uniformWordMean n (fun w => (lengthFn (List.ofFn w) : ℝ)) + 1 / 2 ≤
      uniformWordMean (n + 1) (fun w => (lengthFn (List.ofFn w) : ℝ)) := by
  classical
  rw [uniformWordMean_snoc]
  have hpoint : ∀ u : Fin n → A,
      (lengthFn (List.ofFn u) : ℝ) + 1 / 2 ≤
        (4 : ℝ)⁻¹ * ∑ a : A, (lengthFn (List.ofFn (Fin.snoc u a)) : ℝ) := by
    intro u
    have hR : (4 : ℝ) * (lengthFn (List.ofFn u) : ℝ) + 2 ≤
        ∑ a : A, (lengthFn (List.ofFn u ++ [a]) : ℝ) := by
      have h := (Nat.cast_le (α := ℝ)).mpr (happend (List.ofFn u))
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using h
    simp only [list_ofFn_snoc]
    norm_num only [inv_eq_one_div] at *
    linarith
  have havg := uniformWordMean_mono n
    (fun u => (lengthFn (List.ofFn u) : ℝ) + 1 / 2)
    (fun u => (4 : ℝ)⁻¹ * ∑ a : A, (lengthFn (List.ofFn (Fin.snoc u a)) : ℝ)) hpoint
  rw [uniformWordMean_add, uniformWordMean_const hcard] at havg
  exact havg

theorem uniformWordMean_length_ge (hcard : Fintype.card A = 4)
    (lengthFn : List A → ℕ)
    (happend : ∀ w : List A,
      4 * lengthFn w + 2 ≤ ∑ a : A, lengthFn (w ++ [a]))
    (n : ℕ) :
    (n : ℝ) / 2 ≤ uniformWordMean n (fun w => (lengthFn (List.ofFn w) : ℝ)) := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_div]
      exact uniformWordMean_nonneg 0 _ (fun _ => Nat.cast_nonneg _)
  | succ n ih =>
      have hs := uniformWordMean_length_succ hcard lengthFn happend n
      have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      rw [hn]
      linarith

omit sectionFintypeA in
theorem length_ofFn_le [Fintype A] (lengthFn : List A → ℕ)
    (hbound : ∀ w : List A, lengthFn w ≤ w.length) (n : ℕ) (w : Fin n → A) :
    (lengthFn (List.ofFn w) : ℝ) ≤ (n : ℝ) := by
  have h : lengthFn (List.ofFn w) ≤ n := by
    simpa only [List.length_ofFn] using hbound (List.ofFn w)
  exact (Nat.cast_le (α := ℝ)).mpr h

theorem weightedMean_length_ge_of_uniform_letters {Ω : Type*} [Fintype Ω]
    (hcard : Fintype.card A = 4) (n : ℕ)
    (μ : Ω → ℝ) (letters : Ω → Fin n → A)
    (hletters : ∀ F : (Fin n → A) → ℝ,
      (∑ ω, μ ω * F (letters ω)) =
        ((Fintype.card A : ℝ)⁻¹) ^ n * ∑ w, F w)
    (lengthFn : List A → ℕ)
    (happend : ∀ w : List A,
      4 * lengthFn w + 2 ≤ ∑ a : A, lengthFn (w ++ [a])) :
    (n : ℝ) / 2 ≤ ∑ ω, μ ω * (lengthFn (List.ofFn (letters ω)) : ℝ) := by
  rw [hletters (fun w => (lengthFn (List.ofFn w) : ℝ))]
  simpa only [hcard, Nat.cast_ofNat, uniformWordMean] using
    uniformWordMean_length_ge hcard lengthFn happend n

theorem reducedLength_uniform_mean_ge (n : ℕ) :
    (n : ℝ) / 2 ≤ uniformWordMean n
      (fun w : Fin n → Letter => (reducedLength (List.ofFn w) : ℝ)) := by
  exact uniformWordMean_length_ge (by decide : Fintype.card Letter = 4)
    reducedLength sum_reducedLength_append_ge n

theorem reducedLength_ofFn_le (n : ℕ) (w : Fin n → Letter) :
    (reducedLength (List.ofFn w) : ℝ) ≤ (n : ℝ) := by
  exact length_ofFn_le reducedLength reducedLength_le n w

theorem reducedLength_weighted_mean_ge {Ω : Type*} [Fintype Ω]
    (n : ℕ) (μ : Ω → ℝ) (letters : Ω → Fin n → Letter)
    (hletters : ∀ F : (Fin n → Letter) → ℝ,
      (∑ ω, μ ω * F (letters ω)) =
        ((Fintype.card Letter : ℝ)⁻¹) ^ n * ∑ w, F w) :
    (n : ℝ) / 2 ≤ ∑ ω, μ ω * (reducedLength (List.ofFn (letters ω)) : ℝ) := by
  exact weightedMean_length_ge_of_uniform_letters
    (by decide : Fintype.card Letter = 4) n μ letters hletters
    reducedLength sum_reducedLength_append_ge

theorem reducedLength_tail_all_good {Ω : Type*} [Fintype Ω]
    (n : ℕ) (hn : 0 < n) (μ : Ω → ℝ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (letters : Ω → Fin n → Letter)
    (hletters : ∀ F : (Fin n → Letter) → ℝ,
      (∑ ω, μ ω * F (letters ω)) =
        ((Fintype.card Letter : ℝ)⁻¹) ^ n * ∑ w, F w)
    (bad : Fin n → Ω → Prop)
    (hbad : ∀ i, eventMass μ (bad i) ≤ 1 / (10 * (n : ℝ))) :
    (3 : ℝ) / 20 ≤ eventMass μ (fun ω =>
      (n : ℝ) / 4 ≤ (reducedLength (List.ofFn (letters ω)) : ℝ) ∧
      ∀ i, ¬ bad i ω) := by
  apply three_twentieths_le_tail_all_good μ hμ hμsum n hn
    (fun ω => (reducedLength (List.ofFn (letters ω)) : ℝ))
    (fun ω => reducedLength_ofFn_le n (letters ω)) _ bad hbad
  exact reducedLength_weighted_mean_ge n μ letters hletters

end MarkovSuperreflexivity.FiniteWalkDrift

end OAI
