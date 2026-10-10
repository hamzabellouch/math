import OAI.NumberTheory.TwoPoint.Halasz.HalaszRepeatedCoordinates
import OAI.NumberTheory.TwoPoint.Halasz.HalaszEnergyRestriction
import OAI.NumberTheory.TwoPoint.Halasz.HalaszCollisionAbsorption

namespace OAI

/-! The complete-system moment is controlled by the tuples whose
chosen long coordinates are pairwise distinct. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszGoodLongTuples {n N ℓ : ℕ} (L : Fin ℓ → Fin n) :
    Finset (Fin n → Fin N) := univ.filter (fun x => Function.Injective (x ∘ L))

noncomputable def halaszBadLongCount {n k N ℓ : ℕ} (L : Fin ℓ → Fin (n+2)) : ℕ :=
  (univ.filter (fun xy : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N) =>
    ¬Function.Injective (xy.1 ∘ L) ∧
    halaszVinogradovFrequency k xy.1=halaszVinogradovFrequency k xy.2)).card

theorem halasz_bad_long_count_bound {n k N ℓ : ℕ} (L : Fin ℓ → Fin (n+2))
    (hL : Function.Injective L) :
    halaszBadLongCount (k := k) (N := N) L ≤ ℓ^2*halaszRepeatedCount n k N := by
  let P := (univ : Finset (Fin ℓ × Fin ℓ)).filter (fun ij => ij.1≠ij.2)
  let S := fun ij : Fin ℓ × Fin ℓ => halaszPairCollision n k N (L ij.1) (L ij.2)
  have hsub : (univ.filter (fun xy : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N) =>
      ¬Function.Injective (xy.1 ∘ L) ∧
      halaszVinogradovFrequency k xy.1=halaszVinogradovFrequency k xy.2)) ⊆
      P.biUnion S := by
    intro xy hxy
    obtain ⟨hbad,hfreq⟩ := (mem_filter.mp hxy).2
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hbad
    apply mem_biUnion.mpr
    refine ⟨(i,j),mem_filter.mpr ⟨mem_univ _,hne⟩,?_⟩
    exact mem_filter.mpr ⟨mem_univ _,hij,hfreq⟩
  have hP : P.card≤ℓ^2 := by
    calc
      P.card ≤ (univ : Finset (Fin ℓ × Fin ℓ)).card := card_filter_le _ _
      _ = ℓ^2 := by simp [pow_two]
  calc
    halaszBadLongCount (k := k) (N := N) L ≤ (P.biUnion S).card := card_le_card hsub
    _ ≤ ∑ ij∈P, (S ij).card := card_biUnion_le
    _ ≤ ∑ _ij∈P, halaszRepeatedCount n k N := by
      apply sum_le_sum
      intro ij hij
      exact halasz_pair_collision_bound _ _ (fun h => (mem_filter.mp hij).2 (hL h))
    _ = P.card*halaszRepeatedCount n k N := by simp
    _ ≤ ℓ^2*halaszRepeatedCount n k N := Nat.mul_le_mul_right _ hP

lemma halasz_frequency_energy (n k N : ℕ) :
    halaszFiberEnergy (univ : Finset (Fin n → Fin N)) (halaszVinogradovFrequency k) =
      halaszVinogradovCount n k N := by
  rw [← halasz_nat_power_energy n k N]
  apply halasz_fiber_energy_congr
  intro x _ y _
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    simp only [halaszVinogradovFrequency,← Nat.cast_sum] at hj
    exact_mod_cast hj
  · intro h
    funext j
    simp only [halaszVinogradovFrequency,← Nat.cast_sum]
    exact_mod_cast congrFun h j

theorem halasz_long_collision_partition {n k N ℓ : ℕ} (L : Fin ℓ → Fin (n+2))
    (hL : Function.Injective L) :
    halaszVinogradovCount (n+2) k N ≤ 2*(ℓ^2*halaszRepeatedCount n k N) +
      halaszFiberEnergy (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k) := by
  have h := halasz_energy_restriction (univ : Finset (Fin (n+2) → Fin N))
    (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k)
  rw [halasz_frequency_energy] at h
  apply h.trans
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left 2
  convert halasz_bad_long_count_bound (k := k) (N := N) L hL using 1
  unfold halaszCrossCount halaszBadLongCount
  congr 1
  ext xy
  simp only [mem_filter,mem_product,mem_sdiff,mem_univ,true_and,
    halaszGoodLongTuples,and_true]

end TwoPointCorrelations

end OAI
