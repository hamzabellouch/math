import Mathlib
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
namespace NearLattice
open scoped BigOperators
noncomputable section

 
theorem card_int_interval_le (a b : ℝ) (hab : a ≤ b) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ b - a + 1 := by
  by_cases h : ⌈a⌉ ≤ ⌊b⌋ + 1
  · have he : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) = (⌊b⌋ : ℝ) + 1 - (⌈a⌉ : ℝ) := by
      exact_mod_cast Int.card_Icc_of_le ⌈a⌉ ⌊b⌋ h
    rw [he]
    linarith [Int.floor_le b, Int.le_ceil a]
  · have he : Finset.Icc ⌈a⌉ ⌊b⌋ = ∅ := Finset.Icc_eq_empty (by omega)
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith

theorem card_int_subset_interval_le (S : Finset ℤ) (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) :
    (S.card : ℝ) ≤ b - a + 1 := by
  have hs : S ⊆ Finset.Icc ⌈a⌉ ⌊b⌋ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (hS n hn).1, Int.le_floor.mpr (hS n hn).2⟩
  exact (show (S.card : ℝ) ≤ (Finset.Icc ⌈a⌉ ⌊b⌋).card from
    Nat.cast_le.mpr (Finset.card_le_card hs)).trans (card_int_interval_le a b hab)

theorem card_nat_subset_interval_le (S : Finset ℕ) (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) :
    (S.card : ℝ) ≤ b - a + 1 := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := Int.ofNat_injective
  have hc : (S.image (fun n : ℕ => (n : ℤ))).card = S.card :=
    Finset.card_image_of_injective S hinj
  rw [← hc]
  apply card_int_subset_interval_le _ a b hab
  intro n hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  simpa only [Int.cast_natCast] using hS i hi

 

theorem card_affine_near_le (S : Finset ℕ) (L : ℕ) (γ β ε : ℝ)
    (hβ : 0 < β) (hε : 0 ≤ ε) (hSL : ∀ n ∈ S, n < L)
    (hgood : ∀ n ∈ S, ∃ m : ℤ, |γ + β * n - m| ≤ ε) :
    (S.card : ℝ) ≤ (β * L + 2 * ε + 1) * (2 * ε / β + 1) := by
  classical
  let m (n : ℕ) : ℤ := if hn : n ∈ S then (hgood n hn).choose else 0
  have hm (n : ℕ) (hn : n ∈ S) : |γ + β * n - m n| ≤ ε := by
    simp only [m, dite_eq_left hn]
    exact (hgood n hn).choose_spec
  let T := S.image m
  have hT : (T.card : ℝ) ≤ β * L + 2 * ε + 1 := by
    have he := card_int_subset_interval_le T (γ - ε) (γ + β * L + ε)
      (by have : 0 ≤ β * (L : ℝ) := mul_nonneg hβ.le (Nat.cast_nonneg _); linarith) ?_
    · linarith
    · intro z hz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
      have h := abs_le.mp (hm n hn)
      have hn₀ : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hn₁ : (n : ℝ) ≤ L := by exact_mod_cast (hSL n hn).le
      constructor <;> nlinarith
  have hfiber (z : ℤ) : ((S.filter (fun n => m n = z)).card : ℝ) ≤ 2 * ε / β + 1 := by
    have he := card_nat_subset_interval_le (S.filter (fun n => m n = z))
      (((z : ℝ) - ε - γ) / β) (((z : ℝ) + ε - γ) / β)
      (div_le_div_of_nonneg_right (by linarith) hβ.le) ?_
    · have hr : ((z : ℝ) + ε - γ) / β - ((z : ℝ) - ε - γ) / β = 2 * ε / β := by ring
      rwa [hr] at he
    · intro n hn
      obtain ⟨hn, he⟩ := Finset.mem_filter.mp hn
      have h := abs_le.mp (hm n hn)
      rw [he] at h
      constructor
      · apply (div_le_iff₀ hβ).mpr
        nlinarith
      · apply (le_div_iff₀ hβ).mpr
        nlinarith
  have hmT : Set.MapsTo m S T := by
    intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hc : (S.card : ℝ) = ∑ z ∈ T, ((S.filter (fun n => m n = z)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmT
  calc
    _ = ∑ z ∈ T, ((S.filter (fun n => m n = z)).card : ℝ) := hc
    _ ≤ ∑ _z ∈ T, (2 * ε / β + 1) := Finset.sum_le_sum (fun z _ => hfiber z)
    _ = (T.card : ℝ) * (2 * ε / β + 1) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hT (by positivity)

 
theorem card_affine_near_abs_le (S : Finset ℕ) (L : ℕ) (γ β ε : ℝ)
    (hβ : β ≠ 0) (hε : 0 ≤ ε) (hSL : ∀ n ∈ S, n < L)
    (hgood : ∀ n ∈ S, ∃ m : ℤ, |γ + β * n - m| ≤ ε) :
    (S.card : ℝ) ≤ (|β| * L + 2 * ε + 1) * (2 * ε / |β| + 1) := by
  rcases lt_or_gt_of_ne hβ with hβ | hβ
  · have hh : ∀ n ∈ S, ∃ m : ℤ, |-γ + (-β) * n - m| ≤ ε := by
      intro n hn
      obtain ⟨m, hm⟩ := hgood n hn
      refine ⟨-m, ?_⟩
      have he : -γ + (-β) * (n : ℝ) - ((-m : ℤ) : ℝ) = -(γ + β * n - m) := by
        push_cast
        ring
      rwa [he, abs_neg]
    simpa only [abs_of_neg hβ] using
      card_affine_near_le S L (-γ) (-β) ε (neg_pos.mpr hβ) hε hSL hh
  · simpa only [abs_of_pos hβ] using card_affine_near_le S L γ β ε hβ hε hSL hgood

 

theorem card_near_of_approx (S : Finset ℕ) (N q : ℕ) (hq : 0 < q)
    (α γ β ε : ℝ) (m : ℤ) (happrox : α * q = m + β)
    (hβ : β ≠ 0) (hβsmall : |β| ≤ 2 * ε) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hSN : ∀ n ∈ S, n < N)
    (hgood : ∀ n ∈ S, ∃ z : ℤ, |α * n + γ - z| ≤ ε) :
    (S.card : ℝ) ≤ 4 * ε * N + 3 * q + 4 * q * ε / |β| := by
  classical
  let L := N / q + 1
  let B := (|β| * L + 2 * ε + 1) * (2 * ε / |β| + 1)
  have hfiber (r : ℕ) : ((S.filter (fun n => n % q = r)).card : ℝ) ≤ B := by
    let Sᵣ := S.filter (fun n => n % q = r)
    let T := Sᵣ.image (fun n => n / q)
    have hc : T.card = Sᵣ.card := by
      apply Finset.card_image_iff.mpr
      intro x hx y hy he
      change x / q = y / q at he
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have h₁ := Nat.mod_add_div x q
      have h₂ := Nat.mod_add_div y q
      rw [hx', he] at h₁
      rw [hy'] at h₂
      omega
    have hTL : ∀ k ∈ T, k < L := by
      intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      have h := Nat.div_le_div_right (c := q) (hSN n (Finset.mem_filter.mp hn).1).le
      exact Nat.lt_succ_of_le h
    have hTgood : ∀ k ∈ T, ∃ z : ℤ, |(α * r + γ) + β * k - z| ≤ ε := by
      intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hn, hr⟩ := Finset.mem_filter.mp hn
      obtain ⟨z, hz⟩ := hgood n hn
      refine ⟨z - m * (n / q : ℕ), ?_⟩
      have he : (n : ℝ) = (r : ℝ) + (q : ℝ) * (n / q : ℕ) := by
        have ht := Nat.mod_add_div n q
        rw [hr] at ht
        exact_mod_cast ht.symm
      have heq : (α * r + γ) + β * (n / q : ℕ) - ((z - m * (n / q : ℕ) : ℤ) : ℝ) =
          α * n + γ - z := by
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        rw [he]
        linear_combination -(n / q : ℕ) * happrox
      rwa [heq]
    have h := card_affine_near_abs_le T L (α * r + γ) β ε hβ hε hTL hTgood
    rwa [hc] at h
  have hm : Set.MapsTo (fun n => n % q) S (Finset.range q) := by
    intro n _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
  have hc : (S.card : ℝ) =
      ∑ r ∈ Finset.range q, ((S.filter (fun n => n % q = r)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hm
  have hb : (S.card : ℝ) ≤ (q : ℝ) * B := by
    rw [hc]
    calc
      _ ≤ ∑ _r ∈ Finset.range q, B := Finset.sum_le_sum (fun r _ => hfiber r)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hbpos : 0 < |β| := abs_pos.mpr hβ
  have hL : (q : ℝ) * L ≤ N + q := by
    have h := Nat.div_mul_le_self N q
    dsimp [L]
    push_cast
    have h' : (q : ℝ) * (N / q : ℕ) ≤ N := by exact_mod_cast (by simpa [Nat.mul_comm] using h)
    nlinarith
  have hq₀ : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hqL₀ : 0 ≤ (q : ℝ) * L := by positivity
  have hB : (q : ℝ) * B ≤ 4 * ε * N + 3 * q + 4 * q * ε / |β| := by
    have hc₀ : 0 ≤ 2 * ε / |β| + 1 := by positivity
    have hc₁ : 2 * ε + 1 ≤ 2 := by linarith
    have hstep : (q : ℝ) * B ≤ q * ((|β| * L + 2) * (2 * ε / |β| + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hq₀
      exact mul_le_mul_of_nonneg_right (by linarith) hc₀
    have heq : (q : ℝ) * ((|β| * L + 2) * (2 * ε / |β| + 1)) =
        q * L * (2 * ε + |β|) + 4 * q * ε / |β| + 2 * q := by
      field_simp
      ring
    have hi₁ := mul_le_mul_of_nonneg_left hβsmall hqL₀
    have hi₂ := mul_le_mul_of_nonneg_left hL (show 0 ≤ 4 * ε by positivity)
    have hi₃ := mul_le_mul_of_nonneg_right hεsmall hq₀
    rw [heq] at hstep
    nlinarith
  exact hb.trans hB

 

theorem exists_small_denominator (S : Finset ℕ) (N Q : ℕ) (hQ : 0 < Q)
    (α γ ε : ℝ) (hSN : ∀ n ∈ S, n < N)
    (hcard : N / Q + 1 < S.card)
    (hgood : ∀ n ∈ S, ∃ z : ℤ, |α * n + γ - z| ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ q < Q ∧ ∃ m : ℤ, |α * q - m| ≤ 2 * ε := by
  classical
  have hh : Set.MapsTo (fun n => n / Q) S (Finset.range (N / Q + 1)) := by
    intro n hn
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (hSN n hn).le)
  have hcard' : (Finset.range (N / Q + 1)).card < S.card := by simpa using hcard
  obtain ⟨x, hx, y, hy, hxy, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard' hh
  change x / Q = y / Q at he
  have hp (x y : ℕ) (hx : x ∈ S) (hy : y ∈ S) (hlt : x < y) (he : x / Q = y / Q) :
      ∃ q : ℕ, 0 < q ∧ q < Q ∧ ∃ m : ℤ, |α * q - m| ≤ 2 * ε := by
    obtain ⟨a, ha⟩ := hgood x hx
    obtain ⟨b, hb⟩ := hgood y hy
    refine ⟨y - x, Nat.sub_pos_of_lt hlt, ?_, b - a, ?_⟩
    · have hx' := Nat.mod_add_div x Q
      have hy' := Nat.mod_add_div y Q
      have hymod := Nat.mod_lt y hQ
      rw [he] at hx'
      omega
    · have heq : α * (y - x : ℕ) - ((b - a : ℤ) : ℝ) =
          (α * y + γ - b) - (α * x + γ - a) := by
        rw [Nat.cast_sub hlt.le, Int.cast_sub]
        ring
      rw [heq]
      exact (abs_sub _ _).trans (by linarith)
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact hp x y hx hy hxy he
  · exact hp y x hy hx hxy he.symm

 

theorem vinogradov_inverse (S : Finset ℕ) (N K : ℕ)
    (hK : 0 < K) (hN : 32 * K ^ 2 ≤ N) (α γ ε : ℝ)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / (16 * (K : ℝ)))
    (hSN : ∀ n ∈ S, n < N)
    (hdensity : (N : ℝ) / K ≤ S.card)
    (hgood : ∀ n ∈ S, ∃ z : ℤ, |α * n + γ - z| ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2 * K ∧ ∃ m : ℤ,
      |α * q - m| ≤ 16 * (K : ℝ) ^ 2 * ε / N := by
  have hK₀ : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hK₁ : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hN₀ : 0 < (N : ℝ) := by
    have h : 32 * (K : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
    nlinarith
  have hN' : 32 * (K : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hcard : N / (2 * K) + 1 < S.card := by
    have hdiv : ((N / (2 * K) : ℕ) : ℝ) ≤ (N : ℝ) / (2 * K) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.cast_div_le (m := N) (n := 2 * K) (α := ℝ))
    have he : (N : ℝ) / (2 * K) + 1 < (N : ℝ) / K := by
      apply (lt_div_iff₀ hK₀).mpr
      have heq : ((N : ℝ) / (2 * K) + 1) * K = N / 2 + K := by
        field_simp
      rw [heq]
      nlinarith
    have : ((N / (2 * K) : ℕ) : ℝ) + 1 < S.card := lt_of_lt_of_le (by linarith) hdensity
    exact_mod_cast this
  obtain ⟨q, hq₀, hq₁, m, hm⟩ := exists_small_denominator S N (2 * K) (by omega)
    α γ ε hSN hcard hgood
  refine ⟨q, hq₀, hq₁.le, m, ?_⟩
  let β := α * q - m
  have heps : ε ≤ 1 / 4 := by
    have ht := (le_div_iff₀ (show 0 < 16 * (K : ℝ) by positivity)).mp hεsmall
    nlinarith
  by_cases hβ : β = 0
  · change |β| ≤ _
    rw [hβ, abs_zero]
    positivity
  · have hβpos : 0 < |β| := abs_pos.mpr hβ
    have hq : (q : ℝ) ≤ 2 * K := by exact_mod_cast hq₁.le
    have hq₀' : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
    have hc := card_near_of_approx S N q hq₀ α γ β ε m (by dsimp [β]; ring)
      hβ hm hε heps hSN hgood
    have hepsmul : 16 * (K : ℝ) * ε ≤ 1 := by
      have h := (le_div_iff₀ (show 0 < 16 * (K : ℝ) by positivity)).mp hεsmall
      nlinarith
    have hb₁ : 4 * ε * N ≤ (N : ℝ) / (4 * K) := by
      apply (le_div_iff₀ (show 0 < 4 * (K : ℝ) by positivity)).mpr
      have h := mul_le_mul_of_nonneg_right hepsmul hN₀.le
      nlinarith
    have hb₂ : 3 * (q : ℝ) ≤ (N : ℝ) / (4 * K) := by
      apply (le_div_iff₀ (show 0 < 4 * (K : ℝ) by positivity)).mpr
      have h := mul_le_mul_of_nonneg_right hq hK₀.le
      nlinarith
    have hr : (N : ℝ) / (2 * K) ≤ 4 * q * ε / |β| := by
      have he₁ : (N : ℝ) / K = 2 * ((N : ℝ) / (2 * K)) := by ring
      have he₂ : (N : ℝ) / (4 * K) = ((N : ℝ) / (2 * K)) / 2 := by ring
      rw [he₁] at hdensity
      rw [he₂] at hb₁ hb₂
      linarith
    have hr' := (le_div_iff₀ hβpos).mp hr
    have ht := mul_le_mul_of_nonneg_right hr' (show 0 ≤ 2 * (K : ℝ) by positivity)
    have heq : ((N : ℝ) / (2 * K) * |β|) * (2 * K) = N * |β| := by
      field_simp
    rw [heq] at ht
    have hqε := mul_le_mul_of_nonneg_right hq (show 0 ≤ 8 * (K : ℝ) * ε by positivity)
    change |β| ≤ _
    apply (le_div_iff₀ hN₀).mpr
    nlinarith

end
end NearLattice

 

end
end
end
end

end OAI
