import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A finite collection of denominators has a canonical increasing enumeration. -/
theorem finset_increasing_enumeration (s : Finset ℕ) :
    ∃ n : Fin s.card → ℕ, StrictMono n ∧
      (∀ m, (∃ i, n i = m) ↔ m ∈ s) ∧
      (∀ f : ℕ → ℚ, (∑ i, f (n i)) = ∑ m ∈ s, f m) := by
  refine ⟨s.orderEmbOfFin rfl, (s.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
  · intro m
    change m ∈ Set.range (s.orderEmbOfFin rfl) ↔ m ∈ s
    rw [Finset.range_orderEmbOfFin]
    rfl
  · intro f
    calc
      (∑ i, f ((s.orderEmbOfFin rfl) i)) =
          ∑ m ∈ Finset.univ.image (s.orderEmbOfFin rfl), f m := by
        rw [Finset.sum_image (fun a _ b _ h => (s.orderEmbOfFin rfl).injective h)]
      _ = ∑ m ∈ s, f m := by rw [Finset.image_orderEmbOfFin_univ]

/-- Enumeration preserves a lower bound and the sum of unit fractions. -/
theorem finset_unit_fraction_representation (s : Finset ℕ) (a : ℕ) (x : ℚ)
    (hpos : ∀ m ∈ s, a ≤ m) (hsum : (∑ m ∈ s, (1 : ℚ) / m) = x) :
    ∃ n : Fin s.card → ℕ, (∀ i, a ≤ n i) ∧ StrictMono n ∧
      (∑ i, (1 : ℚ) / n i) = x ∧
      (∀ m, (∃ i, n i = m) ↔ m ∈ s) := by
  obtain ⟨n, hmono, hmem, hsum'⟩ := finset_increasing_enumeration s
  refine ⟨n, ?_, hmono, ?_, hmem⟩
  · intro i
    exact hpos (n i) ((hmem _).mp ⟨i, rfl⟩)
  · exact (hsum' (fun m => (1 : ℚ) / m)).trans hsum

/-- Replacing one denominator by two fresh distinct denominators preserves the
unit-fraction total and all other markers, while increasing cardinality by one. -/
theorem finset_replace_unit_fraction (s : Finset ℕ) (d a b L : ℕ)
    (hd : d ∈ s) (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b)
    (hpos : ∀ m ∈ s, L ≤ m) (haL : L ≤ a) (hbL : L ≤ b)
    (hsplit : (1 : ℚ) / a + 1 / b = 1 / d) :
    ∃ t : Finset ℕ, t.card = s.card + 1 ∧
      (∀ m ∈ t, L ≤ m) ∧
      (∑ m ∈ t, (1 : ℚ) / m) = ∑ m ∈ s, (1 : ℚ) / m ∧
      (∀ m ∈ s, m ≠ d → m ∈ t) := by
  let t := insert a (insert b (s.erase d))
  have hae : a ∉ s.erase d := fun h => ha (Finset.mem_of_mem_erase h)
  have hbe : b ∉ s.erase d := fun h => hb (Finset.mem_of_mem_erase h)
  have hai : a ∉ insert b (s.erase d) := by simp [hab, hae]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · dsimp [t]
    rw [Finset.card_insert_of_notMem hai, Finset.card_insert_of_notMem hbe,
      Finset.card_erase_of_mem hd]
    have := Finset.card_pos.mpr ⟨d, hd⟩
    omega
  · intro m hm
    simp only [t, Finset.mem_insert, Finset.mem_erase] at hm
    rcases hm with rfl | rfl | ⟨_, hm⟩
    · exact haL
    · exact hbL
    · exact hpos m hm
  · dsimp [t]
    rw [Finset.sum_insert hai, Finset.sum_insert hbe]
    have hsum := Finset.sum_erase_add s (fun m => (1 : ℚ) / m) hd
    linarith
  · intro m hm hmd
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hmd, hm⟩))

/-- Sequence form of the collision-free splitting construction. -/
theorem increasing_unit_fraction_split {k : ℕ} (n : Fin k → ℕ)
    (hn : StrictMono n) (L : ℕ) (hpos : ∀ i, L ≤ n i)
    (d : Fin k) (a b : ℕ) (ha : ∀ i, n i ≠ a) (hb : ∀ i, n i ≠ b)
    (hab : a ≠ b) (haL : L ≤ a) (hbL : L ≤ b)
    (hsplit : (1 : ℚ) / a + 1 / b = 1 / n d) :
    ∃ n' : Fin (k + 1) → ℕ, (∀ i, L ≤ n' i) ∧ StrictMono n' ∧
      (∑ i, (1 : ℚ) / n' i) = ∑ i, (1 : ℚ) / n i ∧
      ∀ m, (∃ i, n i = m) → m ≠ n d → ∃ i, n' i = m := by
  classical
  let s := Finset.univ.image n
  have hcard : s.card = k := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hn.injective, Finset.card_univ,
      Fintype.card_fin]
  have hmem (m : ℕ) : m ∈ s ↔ ∃ i, n i = m := by simp [s]
  have hsum : (∑ m ∈ s, (1 : ℚ) / m) = ∑ i, (1 : ℚ) / n i := by
    dsimp [s]
    rw [Finset.sum_image (fun i _ j _ h => hn.injective h)]
  obtain ⟨t, htcard, htpos, htsum, htmem⟩ := finset_replace_unit_fraction
    s (n d) a b L ((hmem _).mpr ⟨d, rfl⟩)
    (by simpa [hmem] using not_exists.mpr ha)
    (by simpa [hmem] using not_exists.mpr hb) hab
    (fun m hm => by obtain ⟨i, rfl⟩ := (hmem m).mp hm; exact hpos i)
    haL hbL hsplit
  have htc : t.card = k + 1 := by omega
  obtain ⟨n', hn'pos, hn'mono, hn'sum, hn'mem⟩ :=
    finset_unit_fraction_representation t L (∑ i, (1 : ℚ) / n i)
      htpos (htsum.trans hsum)
  have hex : ∃ n' : Fin t.card → ℕ, (∀ i, L ≤ n' i) ∧ StrictMono n' ∧
      (∑ i, (1 : ℚ) / n' i) = ∑ i, (1 : ℚ) / n i ∧
      ∀ m, (∃ i, n i = m) → m ≠ n d → ∃ i, n' i = m := by
    refine ⟨n', hn'pos, hn'mono, hn'sum, ?_⟩
    intro m hm hmd
    exact (hn'mem m).mpr (htmem m ((hmem m).mpr hm) hmd)
  rw [htc] at hex
  exact hex

end Problem337

end

end OAI
