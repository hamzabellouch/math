import OAI.Combinatorics.EditApproximation.Binary.IntegerSymbols
import OAI.Combinatorics.EditApproximation.Geometry.OccurrenceLeaf
import OAI.Combinatorics.EditApproximation.Numerics.NumericalWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Uniform input preparation chooses dictionary widths from the actual
integer words. No alphabet size or polynomial exponent is an algorithm input. -/

namespace EditApproximation



theorem integerMagnitude_mem (zs : List ℤ) (z : ℤ) (hz : z ∈ zs) :
    z.natAbs ≤ integerMagnitude zs := by
  induction zs with
  | nil => simp at hz
  | cons a zs ih =>
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_max_left _ _
    · exact (ih hz).trans (le_max_right _ _)

theorem integerMagnitude_le (zs : List ℤ) (B : ℕ) (h : ∀ z ∈ zs, z.natAbs ≤ B) :
    integerMagnitude zs ≤ B := by
  induction zs with
  | nil => exact Nat.zero_le _
  | cons z zs ih =>
    exact max_le (h z List.mem_cons_self) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))





theorem integerInputSymbolBits_fits (source target : List ℤ) (z : ℤ)
    (hz : z ∈ source ++ target) :
    integerSymbolCode z < 2 ^ integerInputSymbolBits source target := by
  exact ((integerSymbolCode_bound z).trans
    (Nat.mul_le_mul_left 2 (integerMagnitude_mem _ z hz))).trans_lt (Nat.lt_size_self _)

theorem integerInputSymbolBits_le (source target : List ℤ) (B : ℕ)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ B) :
    integerInputSymbolBits source target ≤ Nat.size (2 * B) :=
  Nat.size_le_size (Nat.mul_le_mul_left 2 (integerMagnitude_le _ B h))



def integerOccurrenceQuery (source target : List ℤ) (z : ℤ) (lo hi : ℕ) : Bool :=
  occurrenceQuery (integerOccurrenceIndex source target)
    (integerInputSymbolBits source target) (integerInputPositionBits target)
    (integerSymbolCode z) lo hi

theorem integerOccurrenceQuery_correct (source target : List ℤ) (z : ℤ)
    (hz : z ∈ source ++ target) (lo hi : ℕ) (hlohi : lo ≤ hi) (hhi : hi ≤ target.length) :
    integerOccurrenceQuery source target z lo hi = true ↔ z ∈ substring target lo hi := by
  have hcodes : ∀ a ∈ target.map integerSymbolCode,
      a < 2 ^ integerInputSymbolBits source target := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_right _ hz)
  have h := occurrenceQuery_target
    (integerInputSymbolBits source target) (integerInputPositionBits target)
    (target.map integerSymbolCode) hcodes
    (by simpa [integerInputPositionBits] using (Nat.lt_size_self target.length).le)
    (integerSymbolCode z) lo hi (integerInputSymbolBits_fits source target z hz)
    hlohi (by simpa using hhi)
  change _ ↔ _ at h
  change occurrenceQuery _ _ _ _ _ _ = true ↔ _
  unfold integerOccurrenceIndex
  rw [h]
  have hmap : substring (target.map integerSymbolCode) lo hi =
      (substring target lo hi).map integerSymbolCode := by
    simp only [substring, List.map_drop, List.map_take]
  rw [hmap]
  constructor
  · intro hm
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
    exact (integerSymbolCode_injective heq) ▸ ha
  · intro hm
    exact List.mem_map.mpr ⟨z, hm, rfl⟩



theorem integerOccurrenceBuildWithWork_spec (source target : List ℤ) :
    integerOccurrenceBuildWithWork source target =
      (integerOccurrenceIndex source target,
        target.length * (3 * integerInputSymbolBits source target +
          2 * integerInputPositionBits target + 5)) := by
  rw [integerOccurrenceBuildWithWork, occurrenceBuildWithWork_spec]
  simp only [List.length_zipIdx, List.length_map, integerOccurrenceIndex]

/-- Polynomially bounded input words produce logarithmic dictionary keys;
the polynomial degree is only an analysis parameter. -/
theorem integerInputSymbolBits_polynomial (source target : List ℤ) (N C : ℕ)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    integerInputSymbolBits source target ≤ C * Nat.size (N + 2) + 3 := by
  have hbits := integerInputSymbolBits_le source target ((N + 2) ^ C) h
  have hmul := natural_product_bit_length 2 ((N + 2) ^ C)
  have hpow := natural_power_bit_length (N + 2) C
  have htwo : Nat.size 2 = 2 := by decide
  omega

theorem integerOccurrenceBuildWithWork_polynomial (source target : List ℤ) (N C : ℕ)
    (hsize : source.length + target.length ≤ N)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    (integerOccurrenceBuildWithWork source target).2 ≤
      N * ((3 * C + 2) * Nat.size (N + 2) + 14) := by
  rw [integerOccurrenceBuildWithWork_spec]
  dsimp only
  have hs := integerInputSymbolBits_polynomial source target N C h
  have hp : integerInputPositionBits target ≤ Nat.size (N + 2) :=
    Nat.size_le_size (by omega)
  apply Nat.mul_le_mul (by omega)
  nlinarith

end EditApproximation

end OAI
