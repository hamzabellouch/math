import OAI.NumberTheory.ShortEgyptian.DeterministicMean

namespace OAI

universe uα

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem residue_val {q v : ℕ} (hq : 0 < q) (hv : 0 < v) :
    let _ : NeZero q := ⟨hq.ne'⟩
    residue v q (quotient v q) = (-(v : ZMod q)).val := by
  let : NeZero q := ⟨hq.ne'⟩
  dsimp
  obtain ⟨hres, heq⟩ := residue_spec hv hq
  have hc : (v : ZMod q) + (residue v q (quotient v q) : ℕ) = 0 := by
    have hh := congrArg (fun n : ℕ => (n : ZMod q)) heq
    simpa using hh
  have hc' : ((residue v q (quotient v q) : ℕ) : ZMod q) = -(v : ZMod q) := by
    linear_combination hc
  rw [← hc', ZMod.val_natCast_of_lt hres]

theorem fourth_floor_bound (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256) :
    1 ≤ ⌊1 / δ ^ 4⌋₊ ∧ 1 ≤ 2 * (⌊1 / δ ^ 4⌋₊ : ℝ) * δ ^ 4 := by
  have hpow : 0 < δ ^ 4 := pow_pos hδ _
  have hpow2 : δ ^ 4 ≤ 1 / 2 := by
    have hh := pow_le_pow_left₀ hδ.le hδsmall 4
    norm_num at hh ⊢
    linarith
  have hf := Nat.lt_floor_add_one (1 / δ ^ 4)
  have hinv : 2 ≤ 1 / δ ^ 4 := (le_div_iff₀ hpow).mpr (by linarith)
  have hfloor : (1 : ℝ) ≤ ⌊1 / δ ^ 4⌋₊ := by
    exact_mod_cast ((Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ 1 / δ ^ 4 by norm_num only [Nat.cast_one]; linarith)))
  refine ⟨by exact_mod_cast hfloor, ?_⟩
  have hh := (div_lt_iff₀ hpow).mp hf
  nlinarith

theorem stdAddChar_nat_phase {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = phase ((n : ℝ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold phase
  congr 1
  push_cast
  ring

theorem residue_list_discrepancy {α : Type uα} [Fintype α] [Nonempty α]
    (t : α → ℕ) (Q q : ℕ) (hQ : 0 < Q) (hq : 0 < q) (ht : ∀ i, 0 < t i)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256)
    (hFourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖(∑ i, phase ((l : ℝ) * Q * t i / q)) / (Fintype.card α : ℂ)‖ ≤ δ ^ 3) :
    δ * Fintype.card α / 2 ≤
      ((Finset.univ.filter fun i => (residue (Q * t i) q (quotient (Q * t i) q) : ℝ) < δ * q).card : ℝ) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  have hfourth := fourth_floor_bound δ hδ hδsmall
  have hh := indexed_residue_discrepancy (fun i => ((Q * t i : ℕ) : ZMod q)) δ hδ hδsmall
    ⌊1 / δ ^ 4⌋₊ hfourth.1 hfourth.2 (by
      intro l hl hlH
      unfold indexedCharAverage
      have heq (i : α) : ZMod.stdAddChar ((l : ZMod q) * ((Q * t i : ℕ) : ZMod q)) =
          phase ((l : ℝ) * Q * t i / q) := by
        rw [← Nat.cast_mul, stdAddChar_nat_phase]
        push_cast
        rw [mul_assoc]
      simp_rw [heq]
      exact hFourier l hl hlH)
  have heq : (Finset.univ.filter fun i => ((-((Q * t i : ℕ) : ZMod q)).val : ℝ) < δ * q) =
      (Finset.univ.filter fun i => (residue (Q * t i) q (quotient (Q * t i) q) : ℝ) < δ * q) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [residue_val hq (Nat.mul_pos hQ (ht i))]
  rwa [heq] at hh

end ShortEgyptian

end OAI
