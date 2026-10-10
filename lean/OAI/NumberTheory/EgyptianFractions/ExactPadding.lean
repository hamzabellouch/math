import OAI.NumberTheory.EgyptianFractions.Defs
import OAI.NumberTheory.EgyptianFractions.SplitArithmetic
import OAI.NumberTheory.EgyptianFractions.PrimeObstruction
import OAI.NumberTheory.EgyptianFractions.FiniteExpansion

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A nontrivial distinct expansion of one cannot contain denominator one. -/
theorem one_finset_denominators_ge_two (s : Finset ℕ)
    (hcard : 2 ≤ s.card) (hpos : ∀ b ∈ s, 1 ≤ b)
    (hsum : (∑ b ∈ s, (1 : ℚ) / b) = 1) :
    ∀ b ∈ s, 2 ≤ b := by
  intro b hb
  have hbpos := hpos b hb
  by_contra h
  have hb1 : b = 1 := by omega
  have hother : ∃ c ∈ s, c ≠ b := by
    by_contra hnone
    push Not at hnone
    have hsmall : s.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx y hy
      exact (hnone x hx).trans (hnone y hy).symm)
    omega
  obtain ⟨c, hc, hcb⟩ := hother
  have hlt : (1 : ℚ) / b < ∑ x ∈ s, (1 : ℚ) / x := by
    apply Finset.single_lt_sum hcb hb hc
    · have : 0 < c := by have := hpos c hc; omega
      positivity
    · intro x hx _
      positivity
  rw [hb1, hsum] at hlt
  norm_num at hlt

/-- Algebraic interface needed to rule out the two exceptional splits at a prime. -/
def PrimePaddingObstruction : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 3 ≤ p → ∀ (t : Finset ℕ),
    (∀ x ∈ t, 1 ≤ x ∧ x < p) → ∀ v : ℕ,
    (∑ x ∈ t, (1 : ℚ) / x) + 1 / p + 1 / v = 1 →
    v ≠ p + 1 ∧ v ≠ p * (p + 1)

/-- Choose an unmarked denominator with a collision-free two-term split. -/
theorem exists_marker_split_of_obstruction (hprime : PrimePaddingObstruction)
    (s : Finset ℕ) (hcard : 3 ≤ s.card) (hpos : ∀ x ∈ s, 1 ≤ x)
    (hsum : (∑ x ∈ s, (1 : ℚ) / x) = 1) (m : ℕ) (hm : m ∈ s) :
    ∃ b u v : ℕ, b ∈ s ∧ b ≠ m ∧ 1 ≤ u ∧ 1 ≤ v ∧ u ≠ v ∧
      u ∉ s ∧ v ∉ s ∧
      (1 : ℚ) / b = 1 / u + 1 / v := by
  have htwo := one_finset_denominators_ge_two s (by omega) hpos hsum
  let t := s.erase m
  have htcard : 2 ≤ t.card := by
    dsimp [t]
    rw [Finset.card_erase_of_mem hm]
    omega
  have htne : t.Nonempty := Finset.card_pos.mp (by omega)
  let b := t.max' htne
  have hbt : b ∈ t := Finset.max'_mem t htne
  have hbs : b ∈ s := Finset.mem_of_mem_erase hbt
  have hbm : b ≠ m := (Finset.mem_erase.mp hbt).1
  have hbmax : ∀ x ∈ t, x ≤ b := by
    intro x hx
    exact Finset.le_max' t x hx
  have hb3 : 3 ≤ b := by
    obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_ne (by omega : 1 < t.card) b
    have hc2 := htwo c (Finset.mem_of_mem_erase hc)
    have hcb' := hbmax c hc
    omega
  have avoid : ∀ x : ℕ, b < x → x ≠ m → x ∉ s := by
    intro x hbx hxm hx
    have hxt : x ∈ t := Finset.mem_erase.mpr ⟨hxm, hx⟩
    have := hbmax x hxt
    omega
  have hbpos : 0 < b := by omega
  by_cases hex : m = b + 1 ∨ m = b * (b + 1)
  · have hnotprime : ¬ Nat.Prime b := by
      intro hbp
      have hsmall : ∀ x ∈ t.erase b, 1 ≤ x ∧ x < b := by
        intro x hx
        obtain ⟨hxb, hxt⟩ := Finset.mem_erase.mp hx
        have hxle := hbmax x hxt
        exact ⟨hpos x (Finset.mem_of_mem_erase hxt), by omega⟩
      have hsum' : (∑ x ∈ t.erase b, (1 : ℚ) / x) + 1 / b + 1 / m = 1 := by
        rw [Finset.sum_erase_add t (fun x => (1 : ℚ) / x) hbt]
        change (∑ x ∈ s.erase m, (1 : ℚ) / x) + 1 / m = 1
        rw [Finset.sum_erase_add s (fun x => (1 : ℚ) / x) hm, hsum]
      obtain ⟨h1, h2⟩ := hprime b hbp hb3 (t.erase b) hsmall m hsum'
      exact hex.elim h1 h2
    obtain ⟨u, v, hbu, huv, hvb, heq⟩ :=
      composite_unit_fraction_split b (by omega) hnotprime
    have hum : u ≠ m := by
      rcases hex with h | h
      · omega
      · omega
    have hvm : v ≠ m := by
      rcases hex with h | h
      · omega
      · omega
    exact ⟨b, u, v, hbs, hbm, by omega, by omega, by omega,
      avoid u (by omega) hum, avoid v (by omega) hvm, heq⟩
  · push Not at hex
    have hlt : b + 1 < b * (b + 1) := by nlinarith
    exact ⟨b, b + 1, b * (b + 1), hbs, hbm, by omega, by omega,
      by omega, avoid _ (by omega) (Ne.symm hex.1),
      avoid _ (by omega) (Ne.symm hex.2), unit_fraction_split b hbpos⟩

/-- The prime obstruction follows by clearing rational denominators. -/
theorem prime_padding_obstruction : PrimePaddingObstruction := by
  intro p hp hp3 t ht v hsum
  have ht' : ∀ x ∈ t, 0 < x ∧ x < p := by
    intro x hx
    obtain ⟨h1, h2⟩ := ht x hx
    exact ⟨by omega, h2⟩
  constructor
  · intro hv
    subst v
    exact prime_successor_prefix_obstruction t id p hp ht' hsum
  · intro hv
    subst v
    exact prime_product_prefix_obstruction t id p hp hp3 ht' hsum

/-- Exact marker padding, without analytic or counting hypotheses. -/
theorem exact_marker_padding_proof :
    ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
    ∀ m : ℕ, (∃ i : Fin r, n i = m) →
    ∃ n' : Fin (r + 1) → ℕ,
      IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m := by
  intro r hr n hn m hm
  classical
  let s := Finset.univ.image n
  have hcard : s.card = r := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hn.2.1.injective,
      Finset.card_univ, Fintype.card_fin]
  have hmem (x : ℕ) : x ∈ s ↔ ∃ i, n i = x := by simp [s]
  have hpos : ∀ x ∈ s, 1 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := (hmem x).mp hx
    exact hn.1 i
  have hsum : (∑ x ∈ s, (1 : ℚ) / x) = 1 := by
    dsimp [s]
    rw [Finset.sum_image (fun i _ j _ h => hn.2.1.injective h)]
    exact hn.2.2
  obtain ⟨b, u, v, hb, hbm, hu, hv, huv, hus, hvs, hsplit⟩ :=
    exists_marker_split_of_obstruction prime_padding_obstruction
      s (by omega) hpos hsum m ((hmem m).mpr hm)
  obtain ⟨t, htcard, htpos, htsum, htmem⟩ :=
    finset_replace_unit_fraction s b u v 1 hb hus hvs huv hpos hu hv hsplit.symm
  have htc : t.card = r + 1 := by omega
  obtain ⟨n', hn'pos, hn'mono, hn'sum, hn'mem⟩ :=
    finset_unit_fraction_representation t 1 1 htpos (htsum.trans hsum)
  have hex : ∃ n' : Fin t.card → ℕ, IsOneExpansion n' ∧ ∃ i, n' i = m := by
    refine ⟨n', ⟨hn'pos, hn'mono, hn'sum⟩, ?_⟩
    exact (hn'mem m).mpr (htmem m ((hmem m).mpr hm) hbm.symm)
  rwa [htc] at hex

end Problem337

end

end OAI
