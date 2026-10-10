import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeDyadic

namespace OAI

namespace Ostmann.QuadraticSieve

def aggregateDivisorBlock (L k : ℕ) : Finset ℕ :=
  (Finset.Ioc (2^k) (2*2^k)).filter (fun d => d ≤ L)

@[simp] theorem mem_aggregateDivisorBlock {L k d : ℕ} :
    d ∈ aggregateDivisorBlock L k ↔ d ∈ Finset.Icc 2 L ∧ Nat.log 2 (d-1) = k := by
  simp only [aggregateDivisorBlock, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  have hpow : 0 < 2^k := by positivity
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hL⟩
    refine ⟨⟨by omega,hL⟩,Nat.log_eq_of_pow_le_of_lt_pow (by omega) ?_⟩
    rw [pow_succ]
    omega
  · rintro ⟨⟨hd,hL⟩,hk⟩
    have hlo := Nat.pow_log_le_self 2 (show d-1 ≠ 0 by omega)
    have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (d-1)
    rw [hk] at hlo hhi
    rw [pow_succ] at hhi
    omega

theorem sum_Icc_one_eq_boundary_dyadic {E : Type*} [AddCommMonoid E]
    (L : ℕ) (hL : 0 < L) (F : ℕ → E) :
    (∑ d ∈ Finset.Icc 1 L, F d) = F 1 +
      ∑ k ∈ Finset.range (Nat.log 2 L+1), ∑ d ∈ aggregateDivisorBlock L k, F d := by
  classical
  have hset : Finset.Icc 1 L = insert 1 (Finset.Icc 2 L) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  congr 1
  have hmaps (d : ℕ) (hd : d ∈ Finset.Icc 2 L) :
      Nat.log 2 (d-1) ∈ Finset.range (Nat.log 2 L+1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) (by have hh := Finset.mem_Icc.mp hd; omega))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps F]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ext d
  simp only [Finset.mem_filter, mem_aggregateDivisorBlock]

theorem sum_Icc_one_eq_boundary_dyadic_indicator {E : Type*} [AddCommMonoid E]
    (L : ℕ) (hL : 0 < L) (F : ℕ → E) :
    (∑ d ∈ Finset.Icc 1 L, F d) = F 1 +
      ∑ k ∈ Finset.range (Nat.log 2 L+1), ∑ d ∈ Finset.Ioc (2^k) (2*2^k),
        if d ≤ L then F d else 0 := by
  rw [sum_Icc_one_eq_boundary_dyadic L hL F]
  simp only [aggregateDivisorBlock, Finset.sum_filter]

theorem norm_sum_Icc_one_le_boundary_dyadic (L : ℕ) (hL : 0 < L) (F : ℕ → ℂ)
    (R : ℝ) (hfirst : ‖F 1‖ ≤ R)
    (hblocks : ∀ k ∈ Finset.range (Nat.log 2 L+1),
      ‖∑ d ∈ aggregateDivisorBlock L k, F d‖ ≤ R) :
    ‖∑ d ∈ Finset.Icc 1 L, F d‖ ≤ (Nat.log 2 L+2 : ℕ)*R := by
  rw [sum_Icc_one_eq_boundary_dyadic L hL F]
  apply (norm_add_le _ _).trans
  apply (add_le_add hfirst ((norm_sum_le _ _).trans (Finset.sum_le_sum hblocks))).trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end Ostmann.QuadraticSieve

end OAI
