import OAI.NumberTheory.TwoPoint.Fourier.MinorArcRamareError
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcBilinearWindow

namespace OAI

/-! Exact change of variables from the Ramaré coefficient to the finite
bilinear short-window sum. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def minorArcRamareCofactor (P : Finset ℕ) (B : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else B m / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)

lemma minor_arc_ramare_cofactor_bound (P : Finset ℕ) (B : ℕ → ℂ)
    (hB : OneBounded B) (m : ℕ) : ‖minorArcRamareCofactor P B m‖ ≤ 1 := by
  unfold minorArcRamareCofactor
  split_ifs with hm
  · simp
  · rw [norm_div, Complex.norm_natCast]
    apply (div_le_self (norm_nonneg _) (by norm_num)).trans
    exact hB m (Nat.pos_of_ne_zero hm)

lemma minor_arc_bilinear_zero_cofactor (P : Finset ℕ) (M H d : ℕ)
    (a c : ℕ → ℂ) (α : ℝ) (k : ℕ) :
    minorArcBilinearWindow P M H d (fun m => if m = 0 then 0 else a m) c α k =
      minorArcBilinearWindow P M H d a c α k := by
  unfold minorArcBilinearWindow
  apply sum_congr rfl
  intro m _
  by_cases hm : m = 0
  · subst m
    simp [minorArcWindowTerm, minorArcWindowInterval]
  · simp only [ite_eq_right hm]

lemma minor_arc_divisibility_window (p M k H : ℕ) (hp : 0 < p)
    (hM : (k + H) / p < M) (F : ℕ → ℂ) :
    (∑ n ∈ Icc (k + 1) (k + H), if p ∣ n then F n else 0) =
      ∑ m ∈ minorArcWindowInterval M p k H, F (p * m) := by
  rw [← sum_filter]
  symm
  apply sum_bij (fun m _ => p * m)
  · intro m hm
    have hh := (mem_minorArcWindowInterval M p k H m hp).mp hm
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hh.2.2⟩, dvd_mul_right p m⟩
  · intro m _ n _ hmn
    exact Nat.eq_of_mul_eq_mul_left hp hmn
  · intro n hn
    obtain ⟨hnI, hpn⟩ := mem_filter.mp hn
    have hnI' := mem_Icc.mp hnI
    refine ⟨n / p, (mem_minorArcWindowInterval M p k H (n / p) hp).mpr ?_,
      Nat.mul_div_cancel' hpn⟩
    have hdiv : n / p ≤ (k + H) / p := Nat.div_le_div_right hnI'.2
    refine ⟨hdiv.trans_lt hM, ?_, ?_⟩
    · rw [Nat.mul_div_cancel' hpn]
      omega
    · simpa only [Nat.mul_div_cancel' hpn] using hnI'.2
  · intro m _
    rfl

lemma minor_arc_window_weighted_sum (M p k H : ℕ) (a : ℕ → ℂ) (c : ℂ) (β : ℝ) :
    (∑ m ∈ range M, a m * minorArcWindowTerm M p k H c β m) =
      ∑ m ∈ minorArcWindowInterval M p k H, a m * (c * additiveCharacter β m) := by
  let W := minorArcWindowInterval M p k H
  have hsub : W ⊆ range M := by
    intro m hm
    exact mem_range.mpr ((mem_Ico.mp hm).2.trans_le (min_le_left _ _))
  have hf : (range M).filter (fun m => m ∈ W) = W := by
    ext m
    simp only [mem_filter]
    exact ⟨And.right, fun hm => ⟨hsub hm, hm⟩⟩
  change (∑ m ∈ range M, a m * minorArcWindowTerm M p k H c β m) =
    ∑ m ∈ W, a m * (c * additiveCharacter β m)
  rw [← hf, sum_filter]
  apply sum_congr rfl
  intro m _
  change a m * (if m ∈ W then c * additiveCharacter β m else 0) =
    if m ∈ W then a m * (c * additiveCharacter β m) else 0
  split_ifs <;> simp

lemma minor_arc_window_interval_eq_of_cutoff (M A k H : ℕ)
    (hM : (k + H) / A < M) :
    minorArcWindowInterval M A k H = Ico (k / A + 1) ((k + H) / A + 1) := by
  unfold minorArcWindowInterval
  rw [min_eq_right (by omega : (k + H) / A + 1 ≤ M)]

lemma minor_arc_bilinear_cutoff_eq (P : Finset ℕ) (M N H d k : ℕ)
    (hM : ∀ p ∈ P, (k + H) / (d * p) < M)
    (hN : ∀ p ∈ P, (k + H) / (d * p) < N)
    (a c : ℕ → ℂ) (α : ℝ) :
    minorArcBilinearWindow P M H d a c α k =
      minorArcBilinearWindow P N H d a c α k := by
  unfold minorArcBilinearWindow
  simp only [mul_sum]
  rw [sum_comm, sum_comm (s := range N) (t := P)]
  apply sum_congr rfl
  intro p hp
  rw [minor_arc_window_weighted_sum, minor_arc_window_weighted_sum,
    minor_arc_window_interval_eq_of_cutoff M (d * p) k H (hM p hp),
    minor_arc_window_interval_eq_of_cutoff N (d * p) k H (hN p hp)]

lemma minor_arc_ramare_short_eq (P : Finset ℕ) (M H k : ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hM : ∀ p ∈ P, (k + H) / p < M)
    (A B : ℕ → ℂ) (α : ℝ) :
    shortExponentialSum (minorArcRamareApprox P A B) H α k =
      minorArcBilinearWindow P M H 1
        (fun m => B m / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)) A α k := by
  rw [shortExponentialSum_at_nat]
  unfold minorArcRamareApprox minorArcBilinearWindow
  simp only [sum_mul, mul_sum, one_mul]
  rw [sum_comm, sum_comm (s := range M) (t := P)]
  apply sum_congr rfl
  intro p hp
  have he : (∑ n ∈ Icc (k + 1) (k + H),
      (if p ∣ n then A p * B (n / p) /
        ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) * additiveCharacter α n) =
      ∑ m ∈ minorArcWindowInterval M p k H,
        (A p * B m / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)) *
          additiveCharacter α (p * m) := by
    simp only [ite_mul, zero_mul]
    rw [minor_arc_divisibility_window p M k H (hP p hp) (hM p hp)]
    simp only [Nat.mul_div_cancel_left _ (hP p hp)]
  rw [he, minor_arc_window_weighted_sum]
  apply sum_congr rfl
  intro m _
  have hphase : additiveCharacter α (p * m) = additiveCharacter (α * p) m := by
    unfold additiveCharacter
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

lemma minor_arc_ramare_short_eq_bounded (P : Finset ℕ) (M H k : ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hM : ∀ p ∈ P, (k + H) / p < M)
    (A B : ℕ → ℂ) (α : ℝ) :
    shortExponentialSum (minorArcRamareApprox P A B) H α k =
      minorArcBilinearWindow P M H 1 (minorArcRamareCofactor P B) A α k := by
  rw [minor_arc_ramare_short_eq P M H k hP hM]
  exact (minor_arc_bilinear_zero_cofactor P M H 1
    (fun m => B m / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)) A α k).symm

end TwoPointCorrelations

end OAI
