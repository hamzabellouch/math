import OAI.Combinatorics.EditApproximation.Geometry.WideEarlierInputs
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! All wide-coordinate requests needed for one local query can be gathered
from bounded representative lists, including complete requested cells and
the rounded online center at every applicable scale. -/

namespace EditApproximation

open Finset



theorem queryEarlierRepresentatives_length {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (hP : ∃ e : ℕ, P = 2 ^ e)
    (hF : 1 ≤ F) (hw : 0 ≤ initial q) :
    (queryEarlierRepresentatives N P F exponent a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length *
        ((64 * F * P + 2) ^ 2 +
          ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1) := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hP; positivity
  have hlocal := localRefinementRepresentatives_length N P F a initial q hPpos hF
  have hcells := localGroupQueryKeys_length N F exponent a initial q hF hw
  have hmembers : ((localGroupQueryKeys N F exponent a initial q).flatMap fun key =>
      (cellRepresentativeStates n P F key.1 a initial ((2 : ℚ) ^ (-(exponent : ℤ))) key.2).map
        fun r => (key.1, r)).length ≤
      (localGroupQueryKeys N F exponent a initial q).length * (P + 1) ^ 2 := by
    apply list_flatMap_length_le
    intro key hkey
    have hscale := localGroupQueryKeys_scale hkey
    obtain ⟨e, _, heq⟩ := List.mem_map.mp hscale
    simpa only [List.length_map] using cellRepresentativeStates_length_le a initial
      ((2 : ℚ) ^ (-(exponent : ℤ))) key.2
      ⟨by positivity, zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega)⟩
      ⟨e, heq.symm⟩ hP
  unfold queryEarlierRepresentatives
  simp only [List.length_append, List.length_map]
  nlinarith only [hlocal, hmembers, Nat.mul_le_mul_right ((P + 1) ^ 2) hcells]

theorem queryEarlierRepresentatives_local {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (br : ℕ × TargetInterval n)
    (hbr : br ∈ localRefinementRepresentatives N P F a initial q) :
    br ∈ queryEarlierRepresentatives N P F exponent a initial q := by
  exact List.mem_append_left _ (List.mem_append_left _ hbr)

theorem queryEarlierRepresentatives_cell {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (key : ℕ × (ℕ × ℕ))
    (hkey : key ∈ localGroupQueryKeys N F exponent a initial q) (r : TargetInterval n)
    (hr : r ∈ cellRepresentativeStates n P F key.1 a initial ((2 : ℚ) ^ (-(exponent : ℤ))) key.2) :
    (key.1, r) ∈ queryEarlierRepresentatives N P F exponent a initial q := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨key, hkey, List.mem_map.mpr ⟨r, hr, rfl⟩⟩

theorem queryEarlierRepresentatives_online {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (b : ℕ)
    (hb : b ∈ dyadicQueryWindow N (initial q) a F) :
    (b, roundInterval (seedGridSpacing b P) q) ∈
      queryEarlierRepresentatives N P F exponent a initial q := by
  exact List.mem_append_right _ (List.mem_map.mpr ⟨b, hb, rfl⟩)



theorem queryEarlierInputCover_card {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (a : ℚ)
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny) (hP : ∃ e : ℕ, P = 2 ^ e)
    (hF : 1 ≤ F) (hw : 0 ≤ initial q) :
    (queryEarlierInputCover (M := M) parent N P F exponent history a initial q).card ≤
      (dyadicQueryWindow N (initial q) a F).length *
        ((64 * F * P + 2) ^ 2 +
          ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 * (P + 1) ^ 2 + 1) *
        M * history * (40 * P + 2) ^ 2 := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hP; positivity
  apply (wideEarlierInputCover_card parent P history _ hPpos).trans
  exact Nat.mul_le_mul_right ((40 * P + 2) ^ 2) (Nat.mul_le_mul_right history
    (Nat.mul_le_mul_right M (queryEarlierRepresentatives_length N P F exponent a initial q hP hF hw)))

end EditApproximation

end OAI
