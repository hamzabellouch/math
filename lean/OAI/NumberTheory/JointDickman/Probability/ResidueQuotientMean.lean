import OAI.NumberTheory.JointDickman.Counting.PeriodicAverages

namespace OAI

/-! # Uniform residue means descend to every divisor of the period -/

namespace JointDickman
open Finset

/-- A whole number of periods has exactly the uniform residue mean. -/
theorem periodic_mean_at_multiple {d q : ℕ} [NeZero d] (hq : 0 < q)
    (hd : d ∣ q) (F : ZMod d → ℝ) :
    (∑ n ∈ range q, F n) / (q : ℝ) = (∑ a : ZMod d, F a) / (d : ℝ) := by
  obtain ⟨k, hk⟩ := hd
  have he : q = k*d := hk.trans (Nat.mul_comm _ _)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hk0 : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by intro h; simp [h] at he; omega
    exact_mod_cast this
  have hs := periodic_sum_blocks (fun a => (F a : ℂ)) k 0
  simp only [add_zero, sum_range_zero, add_zero] at hs
  have hs' : (∑ n ∈ range (k*d), F n) = (k : ℝ) * ∑ n ∈ range d, F n := by
    exact_mod_cast hs
  have hf := residue_sum_eq_range (fun a => (F a : ℂ))
  have hf' : (∑ a : ZMod d, F a) = ∑ n ∈ range d, F n := by exact_mod_cast hf
  rw [he, hs', hf', Nat.cast_mul]
  field_simp

/-- Taking a representative and reducing modulo a divisor preserves the
uniform law, with all fibers having equal size. -/
theorem residue_quotient_mean {d q : ℕ} [NeZero d] [NeZero q]
    (hd : d ∣ q) (F : ZMod d → ℝ) :
    (∑ a : ZMod q, F (a.val : ZMod d)) / (q : ℝ) =
      (∑ a : ZMod d, F a) / (d : ℝ) := by
  have hs := residue_sum_eq_range (fun a : ZMod q => (F (a.val : ZMod d) : ℂ))
  have hs' : (∑ a : ZMod q, F (a.val : ZMod d)) = ∑ n ∈ range q, F n := by
    have hn (n : ℕ) (hn : n ∈ range q) : (n : ZMod q).val = n :=
      ZMod.val_natCast_of_lt (mem_range.mp hn)
    have hr : (∑ n ∈ range q, F ((n : ZMod q).val : ZMod d)) =
        ∑ n ∈ range q, F n := sum_congr rfl (fun n hn' => by rw [hn n hn'])
    exact (by exact_mod_cast hs : (∑ a : ZMod q, F (a.val : ZMod d)) =
      ∑ n ∈ range q, F ((n : ZMod q).val : ZMod d)).trans hr
  rw [hs']
  exact periodic_mean_at_multiple (NeZero.pos q) hd F

end JointDickman

end OAI
