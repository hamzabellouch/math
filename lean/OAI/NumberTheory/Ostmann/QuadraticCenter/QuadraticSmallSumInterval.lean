import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticSmallSumEnergy

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem nat_residue_fiber_card_le {d : ℕ} [NeZero d]
    (T : Finset ℕ) (X : ℕ) (b : ZMod d) (hupper : ∀ n ∈ T, n ≤ X) :
    (T.filter (fun n : ℕ => (n : ZMod d) = b)).card ≤ X / d + 1 := by
  classical
  calc
    _ ≤ (Finset.range (X / d + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun n : ℕ => n / d)
      · intro n hn
        exact Finset.mem_range.mpr (lt_of_le_of_lt
          (Nat.div_le_div_right (hupper n (Finset.mem_filter.mp hn).1)) (Nat.lt_succ_self _))
      · intro n hn m hm hquot
        change n / d = m / d at hquot
        have hcast : (n : ZMod d) = m :=
          (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
        have hmod : n % d = m % d := by
          simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast
        have hn' := Nat.mod_add_div n d
        rw [hmod, hquot] at hn'
        exact hn'.symm.trans (Nat.mod_add_div m d)
    _ = _ := Finset.card_range _

theorem sum_natCast_le_twice_period_sum {d : ℕ} [NeZero d]
    (T : Finset ℕ) (f : ZMod d → ℝ) (hf : ∀ b, 0 ≤ f b)
    {N : ℝ} (hN : (d : ℝ) ≤ N) (hupper : ∀ n ∈ T, (n : ℝ) ≤ N) :
    ∑ n ∈ T, f (n : ZMod d) ≤ (2 * N / d) * ∑ b, f b := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hN0 : 0 ≤ N := hd.le.trans hN
  apply sum_comp_le_fiber_bound T (fun n : ℕ => (n : ZMod d)) f (2 * N / d) hf
  intro b
  have hc := nat_residue_fiber_card_le T ⌊N⌋₊ b
    (fun n hn => (Nat.le_floor_iff hN0).mpr (hupper n hn))
  have hc' : ((T.filter (fun n : ℕ => (n : ZMod d) = b)).card : ℝ) ≤
      ((⌊N⌋₊ / d : ℕ) : ℝ) + 1 := by exact_mod_cast hc
  have hq : ((⌊N⌋₊ / d : ℕ) : ℝ) ≤ N / d :=
    Nat.cast_div_le.trans (div_le_div_of_nonneg_right (Nat.floor_le hN0) hd.le)
  have h1 : (1 : ℝ) ≤ N / d := (le_div_iff₀ hd).mpr (by simpa using hN)
  calc
    _ ≤ N / d + 1 := hc'.trans (add_le_add hq le_rfl)
    _ ≤ N / d + N / d := add_le_add le_rfl h1
    _ = _ := by ring

theorem centeredProductTransform_square_interval_l1_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (c : ZMod (∏ i, p i))
    (T : Finset ℕ) {N : ℝ} (hN : ((∏ i, p i : ℕ) : ℝ) ≤ N)
    (hupper : ∀ n ∈ T, (n : ℝ) ≤ N) :
    ∑ w ∈ T, ‖centeredProductTransform p hcop S (c * (w : ZMod (∏ i, p i)) ^ 2)‖ ≤
      2 * N * Real.sqrt ((2 : ℝ) ^ Fintype.card ι) := by
  have hd : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast Nat.pos_of_neZero (∏ i, p i)
  have hN0 : 0 ≤ N := hd.le.trans hN
  calc
    _ ≤ (2 * N / (∏ i, p i : ℕ)) *
        ∑ w, ‖centeredProductTransform p hcop S (c * w ^ 2)‖ :=
      sum_natCast_le_twice_period_sum T _ (fun _ => norm_nonneg _) hN hupper
    _ ≤ (2 * N / (∏ i, p i : ℕ)) *
        ((∏ i, p i : ℕ) * Real.sqrt ((2 : ℝ) ^ Fintype.card ι)) :=
      mul_le_mul_of_nonneg_left (centeredProductTransform_square_l1_le p hp hcop S c)
        (by positivity)
    _ = _ := by field_simp

end Ostmann.QuadraticCenter

end

end OAI
