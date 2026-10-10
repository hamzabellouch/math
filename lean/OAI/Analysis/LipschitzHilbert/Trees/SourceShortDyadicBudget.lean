import OAI.Analysis.LipschitzHilbert.Estimates.GeometricScaleWeights
import OAI.Analysis.LipschitzHilbert.Trees.DyadicLineGrid
import Mathlib.Data.Finset.Max

namespace OAI

/-! The short-tree estimates are summed over dyadic lengths with constants
independent of the number of retained scales. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney

/-- Any finite selection of dyadic lengths below `R` has sum at most `2R`. -/
theorem finite_dyadic_length_sum (L R : ℝ) (hR : 0≤R)
    (S : Finset ℕ) (hbound : ∀ j∈S, L/(2:ℝ)^j≤R) :
    (∑ j∈S, L/(2:ℝ)^j) ≤ 2*R := by
  classical
  by_cases hs : S.Nonempty
  · let m := S.min' hs
    have hm : m∈S := S.min'_mem hs
    have hmin (j) (hj : j∈S) : m≤j := S.min'_le j hj
    have hpow (j) (hj : j∈S) :
        L/(2:ℝ)^j = (L/(2:ℝ)^m)*(1/2:ℝ)^(j-m) := by
      have hp : (2:ℝ)^j = 2^m*2^(j-m) := by
        rw [←pow_add,Nat.add_sub_of_le (hmin j hj)]
      rw [hp,one_div_pow]
      ring
    have hinj : Set.InjOn (fun j : ℕ => j-m) (S:Set ℕ) := by
      intro j hj k hk heq
      change j-m=k-m at heq
      have hj' := hmin j hj
      have hk' := hmin k hk
      omega
    have hmap : S.image (fun j => j-m) ⊆ Finset.range (S.max' hs+1) := by
      intro n hn
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
      have hj' := S.le_max' j hj
      simp only [Finset.mem_range]
      omega
    have hsum := Finset.sum_le_sum_of_injOn (fun j : ℕ => j-m) hinj hmap
      (s:=S) (t:=Finset.range (S.max' hs+1))
      (f:=fun j => L/(2:ℝ)^j) (g:=fun n => R*(1/2:ℝ)^n)
      (fun j hj => by
        rw [hpow j hj]
        exact mul_le_mul_of_nonneg_right (hbound m hm) (by positivity))
      (fun _ _ _ => mul_nonneg hR (by positivity))
    calc
      _ ≤ ∑ n∈Finset.range (S.max' hs+1), R*(1/2:ℝ)^n := hsum
      _ = R*∑ n∈Finset.range (S.max' hs+1), (1/2:ℝ)^n := (Finset.mul_sum _ _ _).symm
      _ ≤ R*2 := mul_le_mul_of_nonneg_left (sum_half_powers_le_two _) hR
      _ = _ := mul_comm _ _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.sum_empty]
    positivity

/-- The far-strip gain survives summation of every selected length. -/
theorem finite_dyadic_decay_sum (L R r : ℝ) (hL : 0<L) (hR : 0≤R) (hr : 0<r)
    (S : Finset ℕ) (hbound : ∀ j∈S, L/(2:ℝ)^j≤R) :
    (∑ j∈S, (L/(2:ℝ)^j)*((L/(2:ℝ)^j)/r)^2) ≤ 2*R*(R/r)^2 := by
  have hratio (j) (hj : j∈S) : ((L/(2:ℝ)^j)/r)^2≤(R/r)^2 :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (hbound j hj) hr.le) 2
  calc
    _ ≤ ∑ j∈S, (L/(2:ℝ)^j)*(R/r)^2 :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hratio j hj) (by positivity))
    _ = (∑ j∈S, L/(2:ℝ)^j)*(R/r)^2 := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (finite_dyadic_length_sum L R hR S hbound) (sq_nonneg _)

/-- The same short-length sum in the finite scale indexing used by packets. -/
theorem fin_short_dyadic_length_sum (N : ℕ) (L R : ℝ) (hR : 0≤R) :
    (∑ j : Fin N, if L/(2:ℝ)^j.val≤R then L/(2:ℝ)^j.val else 0) ≤ 2*R := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if L/(2:ℝ)^j≤R then L/(2:ℝ)^j else 0) N,
    ←Finset.sum_filter]
  exact finite_dyadic_length_sum L R hR
    ((Finset.range N).filter (fun j => L/(2:ℝ)^j≤R))
    (fun _ hj => (Finset.mem_filter.mp hj).2)

/-- All packet lengths together retain a quadratic far-strip gain. -/
theorem fin_dyadic_decay_sum (N : ℕ) (L r : ℝ) (hL : 0<L) (hr : 0<r) :
    (∑ j : Fin N, (L/(2:ℝ)^j.val)*((L/(2:ℝ)^j.val)/r)^2) ≤ 2*L*(L/r)^2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (L/(2:ℝ)^j)*((L/(2:ℝ)^j)/r)^2) N]
  apply finite_dyadic_decay_sum L L r hL hL.le hr
  intro j _
  exact div_le_self hL.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))

/-- The squared ratios from a fixed length to larger dyadic lengths have
a uniformly bounded sum, also when the dyadic levels are negative. -/
theorem finite_large_scale_square_sum (L : ℝ) (hL : 0<L)
    (S : Finset ℤ) (hscale : ∀ k∈S, L≤DyadicLineGrid.scale k) :
    (∑ k∈S, (L/DyadicLineGrid.scale k)^2) ≤ 2 := by
  classical
  by_cases hs : S.Nonempty
  · let m := S.min' hs
    have hm : m∈S := S.min'_mem hs
    have hmin (k) (hk : k∈S) : m≤k := S.min'_le k hk
    have hp (k) (hk : k∈S) :
        DyadicLineGrid.scale k = DyadicLineGrid.scale m*(2:ℝ)^((k-m).toNat) := by
      unfold DyadicLineGrid.scale
      rw [←zpow_natCast,←zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      congr 1
      have hk' := hmin k hk
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have hc : 0≤L/DyadicLineGrid.scale m := div_nonneg hL.le (DyadicLineGrid.scale_pos m).le
    have hc1 : L/DyadicLineGrid.scale m≤1 :=
      (div_le_one (DyadicLineGrid.scale_pos m)).mpr (hscale m hm)
    have hpoint (k) (hk : k∈S) :
        (L/DyadicLineGrid.scale k)^2≤(1/2:ℝ)^((k-m).toNat) := by
      have he : L/DyadicLineGrid.scale k =
          (L/DyadicLineGrid.scale m)*(1/2:ℝ)^((k-m).toNat) := by
        rw [hp k hk,one_div_pow]
        ring
      rw [he]
      have ht0 : 0≤(1/2:ℝ)^((k-m).toNat) := by positivity
      have ht1 : (1/2:ℝ)^((k-m).toNat)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hmul := mul_le_mul_of_nonneg_right hc1 ht0
      have hmul0 : 0≤(L/DyadicLineGrid.scale m)*(1/2:ℝ)^((k-m).toNat) := mul_nonneg hc ht0
      have hsq := pow_le_pow_left₀ hmul0 (by simpa only [one_mul] using hmul) 2
      nlinarith only [hsq,ht0,ht1]
    have hinj : Set.InjOn (fun k : ℤ => (k-m).toNat) (S:Set ℤ) := by
      intro j hj k hk heq
      change (j-m).toNat=(k-m).toNat at heq
      have hj' := hmin j hj
      have hk' := hmin k hk
      omega
    have hmap : S.image (fun k => (k-m).toNat) ⊆ Finset.range ((S.max' hs-m).toNat+1) := by
      intro n hn
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
      have hk' := S.le_max' k hk
      have hk'' := hmin k hk
      simp only [Finset.mem_range]
      omega
    exact (Finset.sum_le_sum_of_injOn (fun k : ℤ => (k-m).toNat) hinj hmap
      (s:=S) (t:=Finset.range ((S.max' hs-m).toNat+1))
      (f:=fun k => (L/DyadicLineGrid.scale k)^2) (g:=fun n => (1/2:ℝ)^n)
      hpoint (fun _ _ _ => by positivity)).trans (sum_half_powers_le_two _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.sum_empty]
    norm_num

end LipschitzHilbert.SourceWhitney

end

end OAI
