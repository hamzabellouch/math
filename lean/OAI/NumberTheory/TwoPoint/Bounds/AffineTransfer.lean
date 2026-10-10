import OAI.NumberTheory.TwoPoint.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-!
# Exact progression and affine endpoint identities

These finite identities implement the endpoint step of §8 of the manuscript.
They include nonunit residue classes and do not assume any cancellation theorem.
-/

open scoped BigOperators

namespace TwoPointCorrelations

/-- A prefix sum on any residue class, without a coprimality assumption. -/
def residuePrefix (u : ℕ → ℂ) (l b N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ioc 0 N, if m % l = b % l then u m else 0

lemma progression_interval_image (l b N : ℕ) (hl : 0 < l) :
    (Finset.Icc 1 N).image (fun n => l * n + b) =
      (Finset.Ioc b (l * N + b)).filter (fun m => m % l = b % l) := by
  ext m
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨n, ⟨hn, hnN⟩, rfl⟩
    constructor
    · constructor
      · have : 0 < l * n := Nat.mul_pos hl hn
        omega
      · exact Nat.add_le_add_right (Nat.mul_le_mul_left l hnN) b
    · simp
  · rintro ⟨⟨hbm, hmN⟩, hmod⟩
    have hdvd : l ∣ m - b := Nat.ModEq.dvd' hmod.symm
    obtain ⟨n, hn⟩ := hdvd
    have heq : l * n + b = m := by omega
    refine ⟨n, ⟨?_, ?_⟩, heq⟩
    · by_contra h
      have hn0 : n = 0 := by omega
      subst n
      simp only [Nat.mul_zero, zero_add] at heq
      omega
    · exact Nat.le_of_mul_le_mul_left (by omega : l * n ≤ l * N) hl

/-- Exact extraction of an affine subsequence from two progression prefixes. -/
theorem affine_sum_eq_residue_prefix (u : ℕ → ℂ) (l b N : ℕ) (hl : 0 < l) :
    (∑ n ∈ Finset.Icc 1 N, u (l * n + b)) =
      residuePrefix u l b (l * N + b) - residuePrefix u l b b := by
  have hinj : Set.InjOn (fun n : ℕ => l * n + b) (Finset.Icc 1 N) := by
    intro n hn m hm hnm
    exact Nat.eq_of_mul_eq_mul_left hl (Nat.add_right_cancel hnm)
  have hsum : (∑ n ∈ Finset.Icc 1 N, u (l * n + b)) =
      ∑ m ∈ (Finset.Ioc b (l * N + b)).filter (fun m => m % l = b % l), u m := by
    rw [← progression_interval_image l b N hl, Finset.sum_image hinj]
  have hsplit := Finset.sum_Ioc_consecutive
    (fun m => if m % l = b % l then u m else 0)
    (Nat.zero_le b) (Nat.le_add_left b (l * N))
  unfold residuePrefix
  rw [hsum, Finset.sum_filter]
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hsplit)

/-- The ordered Liouville affine sum has exactly the progression endpoints
specified in the manuscript, with no condition on the residue class. -/
theorem liouville_affine_sum_endpoints (a₁ a₂ b₁ b₂ N : ℕ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (horder : a₂ * b₁ ≤ a₁ * b₂) :
    affineSum liouville liouville a₁ a₂ b₁ b₂ N =
      liouville (a₁ * a₂) *
        (residuePrefix (fun m => liouville m * liouville (m + (a₁ * b₂ - a₂ * b₁)))
            (a₁ * a₂) (a₂ * b₁) (a₁ * a₂ * N + a₂ * b₁) -
          residuePrefix (fun m => liouville m * liouville (m + (a₁ * b₂ - a₂ * b₁)))
            (a₁ * a₂) (a₂ * b₁) (a₂ * b₁)) := by
  unfold affineSum
  simp_rw [liouville_affine_ordered a₁ a₂ b₁ b₂ _ ha₁.ne' ha₂.ne' horder]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [mul_assoc] using affine_sum_eq_residue_prefix
    (fun m => liouville m * liouville (m + (a₁ * b₂ - a₂ * b₁)))
    (a₁ * a₂) (a₂ * b₁) N (Nat.mul_pos ha₁ ha₂)

/-- Swapping the two factors does not alter an affine correlation. -/
theorem affineSum_swap (f g : ℕ → ℂ) (a₁ a₂ b₁ b₂ N : ℕ) :
    affineSum f g a₁ a₂ b₁ b₂ N = affineSum g f a₂ a₁ b₂ b₁ N := by
  unfold affineSum
  apply Finset.sum_congr rfl
  intro n hn
  exact mul_comm _ _

/-- The exact endpoint formula with either determinant sign. -/
theorem liouville_affine_sum_endpoints_all (a₁ a₂ b₁ b₂ N : ℕ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    let l := a₁ * a₂
    let b := min (a₂ * b₁) (a₁ * b₂)
    let h := Nat.dist (a₁ * b₂) (a₂ * b₁)
    affineSum liouville liouville a₁ a₂ b₁ b₂ N =
      liouville l *
        (residuePrefix (fun m => liouville m * liouville (m + h)) l b (l * N + b) -
          residuePrefix (fun m => liouville m * liouville (m + h)) l b b) := by
  dsimp
  rcases le_total (a₂ * b₁) (a₁ * b₂) with hle | hle
  · rw [min_eq_left hle, Nat.dist_eq_sub_of_le_right hle]
    exact liouville_affine_sum_endpoints a₁ a₂ b₁ b₂ N ha₁ ha₂ hle
  · rw [affineSum_swap, min_eq_right hle, Nat.dist_eq_sub_of_le hle]
    simpa only [Nat.mul_comm a₁ a₂] using
      liouville_affine_sum_endpoints a₂ a₁ b₂ b₁ N ha₂ ha₁ hle

/-- Passage from a vanishing progression mean to its affine subsequence. -/
theorem affine_mean_tendsto_zero (u : ℕ → ℂ) (l b : ℕ) (hl : 0 < l)
    (hp : Filter.Tendsto (fun M : ℕ => residuePrefix u l b M / (M : ℂ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, u (l * n + b)) / (N : ℂ))
      Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun N : ℕ => l * N + b) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro k
    filter_upwards [Filter.eventually_ge_atTop k] with N hN
    have : N ≤ l * N := by nlinarith
    omega
  have hsample := hp.comp ht
  have hratio : Filter.Tendsto (fun N : ℕ => ((l * N + b : ℕ) : ℂ) / (N : ℂ))
      Filter.atTop (nhds (l : ℂ)) := by
    have h := Filter.Tendsto.add (tendsto_const_nhds (x := (l : ℂ)))
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℂ) (b : ℂ))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    push_cast
    field_simp
  have hboundary := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℂ) (residuePrefix u l b b)
  have hresult := (hratio.mul hsample).sub hboundary
  simp only [mul_zero, sub_zero] at hresult
  apply hresult.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmNat : 0 < l * N + b := by nlinarith
  have hm : ((l * N + b : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hmNat.ne'
  rw [affine_sum_eq_residue_prefix u l b N hl]
  dsimp only [Function.comp_apply]
  field_simp

end TwoPointCorrelations

end OAI
