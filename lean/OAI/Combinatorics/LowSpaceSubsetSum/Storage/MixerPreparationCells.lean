import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MixerCountCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationMixerPreparation

namespace OAI

/-! # Counting the three already stored mixer domains

The domain lists are retained throughout all three counts. Each count constructs
only two half arrays and streams their sum tournament; the peak is independent
of the number of emitted pairs. Domain construction is a separate preceding
phase, whose returned lists are the explicit input here.
-/

namespace LowSpaceSubsetSum.MixerPreparationCells

open scoped BigOperators
variable {n : ℕ}

def source (a : Fin n → ℤ) (domains : Vector (List (Fin n)) 3) : Vector ℕ 3 × ℕ :=
  let counts := Vector.ofFn (fun i : Fin 3 => MixerHalfLists.count a domains[i.val])
  (counts.map Prod.fst, (∑ i : Fin 3, counts[i.val].2) + 12)

def run (a : Fin n → ℤ) (domains : Vector (List (Fin n)) 3) :
    (Vector ℕ 3 × ℕ) × ℕ :=
  let counts := Vector.ofFn (fun i : Fin 3 => MixerCountCells.count a domains[i.val])
  ((counts.map (fun c => c.1.1), (∑ i : Fin 3, counts[i.val].1.2) + 12),
    (∑ i : Fin 3, counts[i.val].2) + 6*n + 32)

theorem run_value (a : Fin n → ℤ) (domains : Vector (List (Fin n)) 3) :
    (run a domains).1 = source a domains := by
  simp only [run, source, Vector.getElem_ofFn, MixerCountCells.count_value]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, MixerCountCells.count_value]

private theorem scalar_bound (n u T : ℕ) (peaks : Fin 3 → ℕ)
    (hn : 10000 ≤ n) (hu : n+2 ≤ u) (hT : 1 ≤ T)
    (hc : ∀ i, peaks i ≤ u^5*T) :
    (∑ i : Fin 3, peaks i)+6*n+32 ≤ u^6*T := by
  have hu0 : 10000 ≤ u := by omega
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hc i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  have hu2 : 1 ≤ u^2 := Nat.one_le_pow _ _ (by omega)
  have hminor : 6*n+32 ≤ u^5 := by
    calc
      _ ≤ 8*u^2 := by nlinarith only [hu, hu0, hu2]
      _ ≤ u*u^2 := Nat.mul_le_mul_right _ (by omega)
      _ = u^3 := (pow_succ' _ _).symm
      _ ≤ u^5 := pow_le_pow_right' (by omega) (by decide)
  have hminor' := hminor.trans (Nat.le_mul_of_pos_right _ hT)
  have hmajor : 4*u^5 ≤ u^6 := by
    calc
      _ ≤ u*u^5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfinal := Nat.mul_le_mul_right T hmajor
  simp only [Nat.mul_assoc] at hfinal
  omega

theorem run_cells (I : Instance n) (a : Fin n → ℤ)
    (domains : Vector (List (Fin n)) 3) (m : ℕ) (hn : 10000 ≤ n) (hm : m ≤ n)
    (hlen : ∀ i : Fin 3, domains[i.val].length ≤ m) :
    (run a domains).2 ≤ inputScale I^6*2^((m+1)/2) := by
  have hc (i : Fin 3) : (MixerCountCells.count a domains[i.val]).2 ≤
      inputScale I^5*2^((m+1)/2) := by
    have h := MixerCountCells.count_cells I a domains[i.val] hn ((hlen i).trans hm)
    have hdiv : (domains[i.val].length+1)/2 ≤ (m+1)/2 := by
      have hi := hlen i
      omega
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hdiv
    exact h.trans (Nat.mul_le_mul_left _ hp)
  simp only [run, Vector.getElem_ofFn]
  exact scalar_bound n (inputScale I) (2^((m+1)/2))
    (fun i => (MixerCountCells.count a domains[i.val]).2) hn
    (by unfold inputScale; omega) Nat.one_le_two_pow hc

theorem counts_root (D : RepresentationData n) (v : Vector (Fin n) n) :
    (run (fun j => (D.input.values j : ℤ))
      (RepresentationMixerPreparation.run D v).1.domains).1.1 =
      (RepresentationMixerPreparation.run D v).1.counts := by
  apply Vector.ext
  intro i hi
  simp only [run, RepresentationMixerPreparation.run, Vector.getElem_map,
    Vector.getElem_ofFn, MixerCountCells.count_value]

end LowSpaceSubsetSum.MixerPreparationCells

end OAI
