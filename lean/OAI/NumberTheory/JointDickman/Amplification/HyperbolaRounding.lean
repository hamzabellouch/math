import OAI.NumberTheory.JointDickman.Amplification.SmallBilinearVariables

namespace OAI

/-! # Rounding a prime hyperbola to finitely many rectangles -/
namespace JointDickman
open Finset

lemma interval_sum_difference_norm (c : ℕ → ℂ) (Z K M : ℕ)
    (hZ : Z ≤ K) (hK : K ≤ M) (W : ℝ)
    (hc : ∀ m ∈ Ioc K M, ‖c m‖ ≤ W) :
    ‖(∑ m ∈ Ioc Z M, c m) - ∑ m ∈ Ioc Z K, c m‖ ≤ (M-K:ℕ)*W := by
  have he := sum_Ioc_consecutive c hZ hK
  rw [← he,add_sub_cancel_left]
  calc
    _ ≤ ∑ m ∈ Ioc K M, ‖c m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Ioc K M, W := sum_le_sum hc
    _ = _ := by simp

lemma rounded_cutoff_le (Z D M : ℕ) (hZ : Z ≤ M) :
    max Z (D*(M/D)) ≤ M := by
  exact max_le hZ (by simpa [mul_comm] using Nat.div_mul_le_self M D)

lemma rounded_cutoff_error (Z D M : ℕ) (hD : 0 < D) :
    M-max Z (D*(M/D)) < D := by
  have he : M-D*(M/D) = M%D := by
    have h := Nat.mod_add_div M D
    omega
  have hle : M-max Z (D*(M/D)) ≤ M-D*(M/D) :=
    Nat.sub_le_sub_left (le_max_right _ _) M
  exact (hle.trans_eq he).trans_lt (Nat.mod_lt M hD)

lemma rounded_hyperbola_error (P : Finset ℕ) (M : ℕ → ℕ)
    (c : ℕ → ℕ → ℂ) (Z D : ℕ) (hD : 0 < D)
    (hZ : ∀ p ∈ P, Z ≤ M p)
    (hc : ∀ p ∈ P, ∀ m ∈ Ioc Z (M p), ‖c p m‖ ≤ Real.log p) :
    ‖(∑ p ∈ P, ∑ m ∈ Ioc Z (M p), c p m) -
      ∑ p ∈ P, ∑ m ∈ Ioc Z (max Z (D*(M p/D))), c p m‖ ≤
      (D:ℝ)*∑ p ∈ P, Real.log p := by
  rw [←sum_sub_distrib,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hK := rounded_cutoff_le Z D (M p) (hZ p hp)
  have hn := interval_sum_difference_norm (c p) Z (max Z (D*(M p/D))) (M p)
    (le_max_left _ _) hK (Real.log p) (fun m hm => hc p hp m
      (mem_Ioc.mpr ⟨lt_of_le_of_lt (le_max_left _ _) (mem_Ioc.mp hm).1,
        (mem_Ioc.mp hm).2⟩))
  apply hn.trans
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast (rounded_cutoff_error Z D (M p) hD).le)
    (Real.log_natCast_nonneg p)

lemma rounded_hyperbola_rectangles {R : Type*} [AddCommMonoid R]
    (P : Finset ℕ) (M : ℕ → ℕ) (c : ℕ → ℕ → R) (Z D H : ℕ)
    (hH : ∀ p ∈ P, M p/D < H) :
    (∑ p ∈ P, ∑ m ∈ Ioc Z (max Z (D*(M p/D))), c p m) =
      ∑ k ∈ range H, ∑ p ∈ P.filter (fun p => M p/D=k),
        ∑ m ∈ Ioc Z (max Z (D*k)), c p m := by
  classical
  symm
  calc
    _ = ∑ k ∈ range H, ∑ p ∈ P.filter (fun p => M p/D=k),
        ∑ m ∈ Ioc Z (max Z (D*(M p/D))), c p m := by
      apply sum_congr rfl
      intro k hk
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ = _ := sum_fiberwise_of_maps_to (fun p hp => mem_range.mpr (hH p hp)) _

lemma quotient_cell_count (M H : ℕ) (hH : 0 < H) :
    M/(M/H+1) < H := by
  apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos (M/H))).mpr
  have h := Nat.lt_mul_div_succ M hH
  simpa [mul_comm] using h

/-- The grid width is at most its real target plus one. -/
lemma quotient_cell_width (M H : ℕ) (hH : 0 < H) :
    ((M/H+1:ℕ):ℝ) ≤ (M:ℝ)/H+1 := by
  simp only [Nat.cast_add,Nat.cast_one]
  exact add_le_add (nat_div_cast_le M H hH) le_rfl

end JointDickman

end OAI
