import OAI.NumberTheory.JointDickman.Analysis.MellinProfileBlock
import OAI.NumberTheory.JointDickman.Analysis.MellinSieveGrid
import OAI.NumberTheory.JointDickman.Arithmetic.DyadicPrimePartition
import OAI.NumberTheory.JointDickman.Analysis.CharacterLFunctionCutoff

namespace OAI

/-! # Summing logarithmic blocks for the divisor-grid kernel -/
namespace JointDickman
open Finset Filter
open scoped Topology

/-- Dyadic recombination of logarithmic phase cancellation, with explicit
frequency and cutoff inequalities. -/
theorem mellin_profile_high_blocks (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ V : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (N d t : ℝ) (Z K J : ℕ), 0 < d → d ≤ N → 0 < Z → V ≤ Z →
        K ≤ 2^J*Z → ((2^J*Z:ℕ):ℝ)^(1/2:ℝ) ≤ |t/(2*Real.pi)| →
        |t/(2*Real.pi)| ≤ (Z:ℝ)^B →
        ‖∑ n ∈ Ioc Z K, mellinSieveFunction N t (d*n)‖ ≤
          (J:ℝ)*A*(N/d)^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hδ1,hbound⟩ := mellin_dilated_profile_block_uniform B hB
  obtain ⟨V,hV⟩ := eventually_atTop.mp hbound
  refine ⟨A,δ,V,hA,hδ,hδ1,?_⟩
  intro N d t Z K J hd hdN hZ hVZ hK hlo hhi
  have hblocks := sum_dyadic_blocks (Ioc Z K)
    (fun n => mellinSieveFunction N t (d*n)) Z J (by
      intro n hn
      exact ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans hK⟩)
  rw [hblocks]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ range J, A*(N/d)^(1-δ) := by
      apply sum_le_sum
      intro j hj
      have hjJ : j ≤ J := (mem_range.mp hj).le
      have hZU : Z ≤ 2^j*Z := by
        simpa only [one_mul] using Nat.mul_le_mul_right Z (Nat.one_le_pow j 2 (by norm_num))
      have hUU : 2^j*Z ≤ 2^J*Z := Nat.mul_le_mul_right Z
        (Nat.pow_le_pow_right (by norm_num) hjJ)
      have he : ((Ioc Z K).filter (fun n => 2^j*Z < n ∧ n ≤ 2^(j+1)*Z)) =
          Icc (2^j*Z+1) (min K (2^(j+1)*Z)) := by
        ext n
        simp only [mem_filter, mem_Ioc, mem_Icc, le_min_iff]
        omega
      rw [he]
      have hcast := sum_nat_Icc_int_cast (fun n : ℤ => mellinSieveFunction N t (d*n))
        (2^j*Z+1) (min K (2^(j+1)*Z))
      simp only [Int.cast_natCast] at hcast
      rw [hcast]
      apply hV ((2^j*Z:ℕ):ℝ) (hVZ.trans (by exact_mod_cast hZU)) N d t _ _ hd hdN
      · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hUU) (by norm_num)).trans hlo
      · exact hhi.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hZU) (by linarith))
      · push_cast
        linarith
      · have hh : min K (2^(j+1)*Z) ≤ 2*(2^j*Z) := by
          have hm := min_le_right K (2^(j+1)*Z)
          simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm
        exact_mod_cast hh
    _ = _ := by simp; ring

lemma mellin_profile_small_sum {N d : ℝ} (hN : 0 < N) (hd : 0 ≤ d)
    (t : ℝ) (M Z : ℕ) (hMZ : M ≤ Z) :
    ‖∑ m ∈ Icc 1 M, mellinSieveFunction N t (d*m)‖ ≤ d*(Z:ℝ)^2/N := by
  have hpoint (m : ℕ) (hm : m ∈ Icc 1 M) :
      ‖mellinSieveFunction N t (d*m)‖ ≤ d*(Z:ℝ)/N := by
    apply (norm_mellinSieveFunction_le hN (mul_nonneg hd (Nat.cast_nonneg m)) t).trans
    apply div_le_div_of_nonneg_right _ hN.le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Icc.mp hm).2.trans hMZ) hd
  calc
    _ ≤ ∑ m ∈ Icc 1 M, ‖mellinSieveFunction N t (d*m)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Icc 1 M, d*(Z:ℝ)/N := sum_le_sum hpoint
    _ = (M:ℝ)*(d*(Z:ℝ)/N) := by simp
    _ ≤ (Z:ℝ)*(d*(Z:ℝ)/N) := mul_le_mul_of_nonneg_right (by exact_mod_cast hMZ) (by positivity)
    _ = _ := by ring

lemma mellinSieveDiscreteKernel_grid (N t : ℝ) (K d : ℕ) (hd : 0 < d) :
    mellinSieveDiscreteKernel K d N t =
      ∑ m ∈ Icc 1 (K/d), mellinSieveFunction N t ((d:ℝ)*m) := by
  unfold mellinSieveDiscreteKernel mellinSampleKernel
  change (∑ n ∈ (Icc 1 K).filter (fun n => d ∣ n), mellinSieveFunction N t n) = _
  rw [← sum_grid_eq_filter (fun n => mellinSieveFunction N t n) K d hd,
    riemann_sum_range_succ_eq_Icc (fun m => mellinSieveFunction N t ((d*m:ℕ):ℝ))]
  apply sum_congr rfl
  intro m hm
  simp only [Nat.cast_mul]

/-- The actual high-frequency divisor-kernel error. Every term on the
right is explicit; the phase saving comes from the proved derivative estimates. -/
theorem mellinSieve_high_error (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ V : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (N t : ℝ) (d K Z J : ℕ), 0 < d → (d:ℝ) ≤ N → 0 < Z → V ≤ Z →
        K/d ≤ 2^J*Z → ((2^J*Z:ℕ):ℝ)^(1/2:ℝ) ≤ |t/(2*Real.pi)| →
        |t/(2*Real.pi)| ≤ (Z:ℝ)^B →
        ‖mellinSieveDiscreteKernel K d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
          (d:ℝ)*(Z:ℝ)^2/N + (J:ℝ)*A*(N/d)^(1-δ) + 4*N/((d:ℝ)*(4+t^2)) := by
  obtain ⟨A,δ,V,hA,hδ,hδ1,hbound⟩ := mellin_profile_high_blocks B hB
  refine ⟨A,δ,V,hA,hδ,hδ1,?_⟩
  intro N t d K Z J hd hdN hZ hV hK hlo hhi
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hN : 0 < N := hdR.trans_le hdN
  have hb := hbound N d t Z (K/d) J hdR hdN hZ hV hK hlo hhi
  have he : (∑ m ∈ Icc 1 (K/d), mellinSieveFunction N t ((d:ℝ)*m)) =
      (∑ m ∈ Icc 1 (min Z (K/d)), mellinSieveFunction N t ((d:ℝ)*m)) +
        ∑ m ∈ Ioc Z (K/d), mellinSieveFunction N t ((d:ℝ)*m) := by
    have hu : Icc 1 (K/d) = Icc 1 (min Z (K/d)) ∪ Ioc Z (K/d) := by
      ext m
      simp only [mem_Icc, mem_Ioc, mem_union, le_min_iff]
      omega
    rw [hu, sum_union]
    apply disjoint_left.mpr
    intro m hm hm'
    have := (mem_Icc.mp hm).2
    have := (mem_Ioc.mp hm').1
    omega
  rw [mellinSieveDiscreteKernel_grid N t K d hd, he]
  have hs := mellin_profile_small_sum hN hdR.le t (min Z (K/d)) Z (min_le_left _ _)
  have hm : ‖mellinSieveMainKernel N t/(d:ℂ)‖ = 4*N/((d:ℝ)*(4+t^2)) := by
    rw [norm_div, norm_mellinSieveMainKernel hN.le, Complex.norm_natCast]
    field_simp
  calc
    _ ≤ ‖∑ m ∈ Icc 1 (min Z (K/d)), mellinSieveFunction N t ((d:ℝ)*m)‖ +
        ‖∑ m ∈ Ioc Z (K/d), mellinSieveFunction N t ((d:ℝ)*m)‖ +
          ‖mellinSieveMainKernel N t/(d:ℂ)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by rw [hm]; exact add_le_add (add_le_add hs hb) le_rfl

end JointDickman

end OAI
