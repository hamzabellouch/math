import OAI.NumberTheory.Ostmann.ZeroDensity.ResidueRieszFinite

namespace OAI

/-! # An elementary bound for residue-class Mangoldt sums -/

namespace Ostmann

open scoped BigOperators

theorem residue_index_card_bound (q a N : ℕ) (_hq : 0 < q) :
    ((Finset.Icc 0 N).filter (fun n : ℕ => (n : ZMod q) = (a : ZMod q))).card ≤ N / q + 1 := by
  classical
  let S := (Finset.Icc 0 N).filter (fun n : ℕ => (n : ZMod q) = (a : ZMod q))
  have hinj : Set.InjOn (fun n : ℕ => n / q) S := by
    intro n hn m hm hnm
    have hnmod : n % q = a % q := by
      exact (ZMod.natCast_eq_natCast_iff n a q).mp (Finset.mem_filter.mp hn).2
    have hmmod : m % q = a % q := by
      exact (ZMod.natCast_eq_natCast_iff m a q).mp (Finset.mem_filter.mp hm).2
    have he := Nat.div_add_mod n q
    have he' := Nat.div_add_mod m q
    change n / q = m / q at hnm
    rw [hnm, hnmod] at he
    rw [hmmod] at he'
    omega
  have hsub : S.image (fun n => n / q) ⊆ Finset.range (N / q + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    have hnN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hnN)
  calc
    _ = (S.image (fun n => n / q)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (N / q + 1)).card := Finset.card_le_card hsub
    _ = _ := Finset.card_range _

theorem residuePsi_nonneg (q a : ℕ) (X : ℝ) : 0 ≤ residuePsi q a X :=
  Finset.sum_nonneg (fun n _ => residueMangoldtWeight_nonneg q a n)

theorem residuePsi_counting_bound (q a : ℕ) (X : ℝ) (hq : 0 < q) (hX : 1 ≤ X) :
    residuePsi q a X ≤ (X / q + 1) * Real.log X := by
  classical
  let S := (Finset.Icc 0 ⌊X⌋₊).filter (fun n : ℕ => (n : ZMod q) = (a : ZMod q))
  have he : residuePsi q a X = ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := by
    simp only [residuePsi, residueMangoldtWeight, S, Finset.sum_filter]
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hb (n : ℕ) (hn : n ∈ S) : ArithmeticFunction.vonMangoldt n ≤ Real.log X := by
    by_cases hn0 : n = 0
    · subst n; simpa using hlog
    have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff (by linarith : 0 ≤ X)).mp
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) hnX)
  have hcard : (S.card : ℝ) ≤ X / q + 1 := by
    have hc : (S.card : ℝ) ≤ (⌊X⌋₊ / q : ℕ) + 1 := by
      exact_mod_cast residue_index_card_bound q a ⌊X⌋₊ hq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hquot : ((⌊X⌋₊ / q : ℕ) : ℝ) ≤ X / q := by
      apply (le_div_iff₀ hqR).mpr
      have hh : (((⌊X⌋₊ / q) * q : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self ⌊X⌋₊ q
      simp only [Nat.cast_mul] at hh
      exact hh.trans (Nat.floor_le (by linarith))
    linarith
  rw [he]
  calc
    _ ≤ ∑ _n ∈ S, Real.log X := Finset.sum_le_sum hb
    _ = (S.card : ℝ) * Real.log X := by simp
    _ ≤ (X / q + 1) * Real.log X := mul_le_mul_of_nonneg_right hcard hlog

end Ostmann

end OAI
