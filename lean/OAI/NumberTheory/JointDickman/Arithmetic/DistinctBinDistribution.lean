import OAI.NumberTheory.JointDickman.Arithmetic.RepeatedPrimeDensity
import OAI.NumberTheory.JointDickman.Amplification.BinMarginalInput

namespace OAI

/-! # Removing prime multiplicities in the finite-bin marginal law -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem primeBin_subset_allLarge {J k : ℕ} {x : ℝ} (hJ : 0 < J)
    (hk : 0 < k) (hkJ : k < J) (hx : 1 ≤ x) :
    primeBin x J k ⊆ allLargeBinPrimes J x := by
  intro p hp
  obtain ⟨hpp,hlo,hhi⟩ := (mem_primeBin_iff (by linarith) J k p).mp hp
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hl : x^((1 : ℝ)/J) ≤ x^((k : ℝ)/J) :=
    Real.rpow_le_rpow_of_exponent_le hx
      (div_le_div_of_nonneg_right (by exact_mod_cast hk) hJr.le)
  have hu : x^(((k : ℝ)+1)/J) ≤ x := by
    have he : ((k : ℝ)+1)/J ≤ 1 := (div_le_one hJr).mpr (by exact_mod_cast hkJ)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx he
  exact mem_filter.mpr ⟨mem_Ioc.mpr
    ⟨(Nat.floor_lt (Real.rpow_nonneg (by linarith) _)).mpr (hl.trans_lt hlo),
      (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (hhi.trans hu)⟩,hpp⟩

noncomputable def distinctBinVector (J : ℕ) (x : ℝ) (n : ℕ) : BinCountState J :=
  fun i => ⟨min (distinctBinCount (primeBin x J (i.val+1)) n) J,
    (min_le_right _ _).trans_lt (Nat.lt_succ_self J)⟩

theorem canonical_eq_distinctBinVector {J n : ℕ} {x : ℝ} (hJ : 0 < J)
    (hx : 1 ≤ x) (hn : n ≠ 0)
    (hsq : ∀ p ∈ allLargeBinPrimes J x, ¬p^2 ∣ n) :
    canonicalBinVector J x n = distinctBinVector J x n := by
  funext i
  apply Fin.ext
  change min (binCount (primeBin x J (i.val+1)) n) J = _
  have hs : ∀ p ∈ primeBin x J (i.val+1), ¬p^2 ∣ n := by
    intro p hp
    exact hsq p (primeBin_subset_allLarge hJ (by omega) (by have := i.isLt; omega) hx hp)
  rw [binCount_eq_distinct_of_no_squares _
    (fun p hp => ((mem_primeBin_iff (by linarith) _ _ _).mp hp).1) hn hs]
  rfl

open Classical in
theorem state_count_difference_bound {G : Type*} (S B : Finset ℕ)
    (u v : ℕ → G) (r : G) (heq : ∀ n ∈ S, n ∉ B → u n = v n) :
    |(((S.filter (fun n => u n = r)).card : ℝ) -
      ((S.filter (fun n => v n = r)).card : ℝ))| ≤ (B.card : ℝ) := by
  classical
  have hc (f : ℕ → G) : ((S.filter (fun n => f n = r)).card : ℝ) =
      ∑ n ∈ S, if f n = r then (1 : ℝ) else 0 := by simp
  rw [hc u,hc v,← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ S, |(if u n = r then (1 : ℝ) else 0) -
        (if v n = r then 1 else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, if n ∈ B then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases hB : n ∈ B
      · simp only [hB,ite_true]
        split_ifs <;> norm_num
      · rw [heq n hn hB]
        simp [hB]
    _ = ((S ∩ B).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast card_le_card inter_subset_right

noncomputable def distinctBinStateDensity (J : ℕ) (A x : ℝ) (r : BinCountState J) : ℝ :=
  (((Ioc 0 ⌊A*x⌋₊).filter (fun n => distinctBinVector J x n = r)).card : ℝ)/(A*x)

theorem binStateDensity_sub_distinct_tendsto {J : ℕ} (hJ : 0 < J)
    {A : ℝ} (hA : 0 < A) (r : BinCountState J) :
    Tendsto (fun x : ℝ => binStateDensity J A x r - distinctBinStateDensity J A x r)
      atTop (𝓝 0) := by
  classical
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (repeatedLargeBinPrimes_tendsto_zero hJ hA)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hden : 0 < A*x := mul_pos hA (by linarith)
  have hc := state_count_difference_bound (Ioc 0 ⌊A*x⌋₊)
    (repeatedPrimeExceptions (allLargeBinPrimes J x) ⌊A*x⌋₊)
    (canonicalBinVector J x) (distinctBinVector J x) r (by
      intro n hn hnot
      apply canonical_eq_distinctBinVector hJ hx (by have := (mem_Ioc.mp hn).1; omega)
      intro p hp hd
      exact hnot (mem_filter.mpr ⟨hn,⟨p,hp,hd⟩⟩))
  simp only [binStateDensity,distinctBinStateDensity,← sub_div,Real.norm_eq_abs,
    abs_div,abs_of_pos hden]
  convert div_le_div_of_nonneg_right hc hden.le using 1
  congr 6

end JointDickman

end OAI
