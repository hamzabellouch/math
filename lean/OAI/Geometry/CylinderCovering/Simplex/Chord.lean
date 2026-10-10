import Mathlib

namespace OAI

open Set
open scoped BigOperators

namespace SimplexChord

variable {ι : Type*} [Fintype ι]

abbrev standardSimplex : Set (ι → ℝ) :=
  {weights | (∀ coordinate, 0 ≤ weights coordinate) ∧ ∑ coordinate, weights coordinate = 1}

theorem positive_mass_eq_negative_mass (b : ι → ℝ) (hb : ∑ i, b i = 0) :
    (∑ i, max 0 (b i)) = ∑ i, max 0 (-b i) := by
  have hpoint : ∀ i, max 0 (b i) - max 0 (-b i) = b i := by
    intro i
    rcases le_total 0 (b i) with hi | hi
    · rw [max_eq_right hi, max_eq_left (neg_nonpos.mpr hi)]
      ring
    · rw [max_eq_left hi, max_eq_right (neg_nonneg.mpr hi)]
      ring
  have h := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hpoint)
  simp only [Finset.sum_sub_distrib] at h
  linarith

theorem negative_mass_pos (b : ι → ℝ) (hb : ∑ i, b i = 0) (hne : b ≠ 0) :
    0 < ∑ i, max 0 (-b i) := by
  have hn : 0 ≤ ∑ i, max 0 (-b i) :=
    Finset.sum_nonneg (fun i _ => le_max_left _ _)
  by_contra hnot
  have hz : (∑ i, max 0 (-b i)) = 0 := le_antisymm (le_of_not_gt hnot) hn
  have hcoords : ∀ i, max 0 (-b i) = 0 := by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset ι)) => le_max_left 0 (-b i))).mp hz
  have hbpos : ∀ i, 0 ≤ b i := by
    intro i
    have h := le_max_right 0 (-b i)
    rw [hcoords i] at h
    linarith
  have hbzero : ∀ i, b i = 0 := by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hbpos i)).mp hb
  exact hne (funext hbzero)

theorem endpoints_iff (b x : ι → ℝ) (hb : ∑ i, b i = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    (x ∈ standardSimplex ∧ (fun i => x i + s * b i) ∈ standardSimplex) ↔
      (∀ i, s * max 0 (-b i) ≤ x i) ∧ ∑ i, x i = 1 := by
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨fun i => ?_, hx.2⟩
    rcases le_total 0 (-b i) with hi | hi
    · rw [max_eq_right hi]
      have h := hy.1 i
      linarith
    · rw [max_eq_left hi, mul_zero]
      exact hx.1 i
  · rintro ⟨hx, hsum⟩
    have hxnonneg : ∀ i, 0 ≤ x i := fun i =>
      (mul_nonneg hs (le_max_left _ _)).trans (hx i)
    refine ⟨⟨hxnonneg, hsum⟩, ⟨fun i => ?_, ?_⟩⟩
    · have hle := mul_le_mul_of_nonneg_left (le_max_right 0 (-b i)) hs
      have h := hx i
      nlinarith
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hb, mul_zero,
        add_zero]

theorem chord_bound (b x : ι → ℝ) (hb : ∑ i, b i = 0)
    {s : ℝ} (hs : 0 ≤ s) (hx : x ∈ standardSimplex)
    (hy : (fun i => x i + s * b i) ∈ standardSimplex) :
    s * (∑ i, max 0 (-b i)) ≤ 1 := by
  have h := (endpoints_iff b x hb hs).mp ⟨hx, hy⟩
  calc
    s * (∑ i, max 0 (-b i)) = ∑ i, s * max 0 (-b i) := Finset.mul_sum ..
    _ ≤ ∑ i, x i := Finset.sum_le_sum (fun i _ => h.1 i)
    _ = 1 := h.2

theorem endpoint_unique (b x : ι → ℝ) (hb : ∑ i, b i = 0)
    {s : ℝ} (hs : 0 ≤ s) (hsc : s * (∑ i, max 0 (-b i)) = 1)
    (hx : x ∈ standardSimplex)
    (hy : (fun i => x i + s * b i) ∈ standardSimplex) :
    x = fun i => s * max 0 (-b i) := by
  have h := (endpoints_iff b x hb hs).mp ⟨hx, hy⟩
  have hsum : (∑ i, (x i - s * max 0 (-b i))) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h.2, hsc]
    ring
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) => sub_nonneg.mpr (h.1 i))).mp hsum
  funext i
  exact sub_eq_zero.mp (hz i (Finset.mem_univ i))

theorem intersection_homothety (b : ι → ℝ) (hb : ∑ i, b i = 0)
    {s : ℝ} (hs : 0 ≤ s) (hsc : s * (∑ i, max 0 (-b i)) < 1) :
    {x | x ∈ standardSimplex ∧
      (fun i => x i + s * b i) ∈ standardSimplex} =
    (fun y i => s * max 0 (-b i) +
      (1 - s * (∑ j, max 0 (-b j))) * y i) '' standardSimplex := by
  let c := ∑ i, max 0 (-b i)
  have hden : 0 < 1 - s * c := sub_pos.mpr hsc
  ext x
  constructor
  · intro hx
    have h := (endpoints_iff b x hb hs).mp hx
    let y : ι → ℝ := fun i => (x i - s * max 0 (-b i)) / (1 - s * c)
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact div_nonneg (sub_nonneg.mpr (h.1 i)) hden.le
    · change (∑ i, (x i - s * max 0 (-b i)) / (1 - s * c)) = 1
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, h.2]
      exact div_self (ne_of_gt hden)
    · funext i
      change s * max 0 (-b i) + (1 - s * c) *
        ((x i - s * max 0 (-b i)) / (1 - s * c)) = x i
      rw [mul_div_cancel₀ _ (ne_of_gt hden)]
      ring
  · rintro ⟨y, hy, rfl⟩
    apply (endpoints_iff b _ hb hs).mpr
    refine ⟨fun i => ?_, ?_⟩
    · have hn := mul_nonneg hden.le (hy.1 i)
      dsimp [c] at hn
      linarith
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hy.2, mul_one]
      ring

theorem maximal_chord (b : ι → ℝ) (hb : ∑ i, b i = 0) (hne : b ≠ 0) :
    let c := ∑ i, max 0 (-b i)
    let x : ι → ℝ := fun i => max 0 (-b i) / c
    x ∈ standardSimplex ∧
      (fun i => x i + (1 / c) * b i) ∈ standardSimplex ∧
      ∀ (y : ι → ℝ) (s : ℝ), 0 ≤ s → y ∈ standardSimplex →
        (fun i => y i + s * b i) ∈ standardSimplex → s ≤ 1 / c := by
  dsimp only
  have hc := negative_mass_pos b hb hne
  have hmem := (endpoints_iff b (fun i => max 0 (-b i) / ∑ j, max 0 (-b j))
    hb (one_div_nonneg.mpr hc.le)).mpr
      (And.intro (fun i => by rw [one_div, div_eq_mul_inv]; ring_nf; rfl)
        (by rw [← Finset.sum_div]; exact div_self (ne_of_gt hc)))
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro y s hs hy hz
  exact (le_div_iff₀ hc).mpr (chord_bound b y hb hs hy hz)

theorem exists_chord_iff (b : ι → ℝ) (hb : ∑ i, b i = 0) (hne : b ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) :
    (∃ x : ι → ℝ, x ∈ standardSimplex ∧
      (fun i => x i + s * b i) ∈ standardSimplex) ↔
    s * (∑ i, max 0 (-b i)) ≤ 1 := by
  constructor
  · rintro ⟨x, hx, hy⟩
    exact chord_bound b x hb hs hx hy
  · intro hsc
    have hc := negative_mass_pos b hb hne
    refine ⟨fun i => max 0 (-b i) / ∑ j, max 0 (-b j),
      (endpoints_iff b _ hb hs).mpr ⟨?_, ?_⟩⟩
    · intro i
      apply (le_div_iff₀ hc).mpr
      have h := mul_le_mul_of_nonneg_right hsc (le_max_left 0 (-b i))
      nlinarith
    · rw [← Finset.sum_div]
      exact div_self (ne_of_gt hc)

theorem intersection_empty (b : ι → ℝ) (hb : ∑ i, b i = 0)
    {s : ℝ} (hs : 0 ≤ s) (hsc : 1 < s * (∑ i, max 0 (-b i))) :
    {x | x ∈ standardSimplex ∧
      (fun i => x i + s * b i) ∈ standardSimplex} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (not_le_of_gt hsc) (chord_bound b x hb hs hx.1 hx.2)

theorem intersection_singleton (b : ι → ℝ) (hb : ∑ i, b i = 0)
    {s : ℝ} (hs : 0 ≤ s) (hsc : s * (∑ i, max 0 (-b i)) = 1) :
    {x | x ∈ standardSimplex ∧
      (fun i => x i + s * b i) ∈ standardSimplex} =
    {fun i => s * max 0 (-b i)} := by
  ext x
  constructor
  · intro hx
    exact Set.mem_singleton_iff.mpr (endpoint_unique b x hb hs hsc hx.1 hx.2)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    apply (endpoints_iff b _ hb hs).mpr
    exact ⟨fun _ => le_rfl, by rw [← Finset.mul_sum, hsc]⟩

theorem abs_mass_eq_twice (b : ι → ℝ) (hb : ∑ i, b i = 0) :
    (∑ i, |b i|) = 2 * ∑ i, max 0 (-b i) := by
  have hpoint : ∀ i, |b i| = max 0 (b i) + max 0 (-b i) := by
    intro i
    rcases le_total 0 (b i) with hi | hi
    · rw [abs_of_nonneg hi, max_eq_right hi, max_eq_left (neg_nonpos.mpr hi)]
      ring
    · rw [abs_of_nonpos hi, max_eq_left hi, max_eq_right (neg_nonneg.mpr hi)]
      ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, positive_mass_eq_negative_mass b hb]
  ring

theorem sum_sq_le_twice_mass_sq (b : ι → ℝ) (hb : ∑ i, b i = 0) :
    (∑ i, (b i)^2) ≤ 2 * (∑ i, max 0 (-b i))^2 := by
  have hpoint : ∀ i, (b i)^2 = (max 0 (b i))^2 + (max 0 (-b i))^2 := by
    intro i
    rcases le_total 0 (b i) with hi | hi
    · rw [max_eq_right hi, max_eq_left (neg_nonpos.mpr hi)]
      ring
    · rw [max_eq_left hi, max_eq_right (neg_nonneg.mpr hi)]
      ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  have hp := Finset.sum_sq_le_sq_sum_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) => le_max_left 0 (b i))
  have hn := Finset.sum_sq_le_sq_sum_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) => le_max_left 0 (-b i))
  rw [positive_mass_eq_negative_mass b hb] at hp
  linarith

end SimplexChord

end OAI
