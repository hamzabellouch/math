import Mathlib
import OAI.Combinatorics.MatchingPSD.AdmissibleTables
import OAI.Combinatorics.MatchingPSD.MatchingConversion
import OAI.Combinatorics.MatchingPSD.MatchingIncidence

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

lemma oddCut_has_tight_matching {n : ℕ} (he : Even n) (U : OddCut n) :
    ∃ M : PerfectMatching n, slack (Sum.inr U) M = 0 := by
  classical
  have hu := U.2
  obtain ⟨a, ha⟩ := hu
  have hcomp : Odd (n - U.1.card) := by
    have hle : U.1.card ≤ n := by simpa using Finset.card_le_univ U.1
    rw [Nat.odd_iff]
    obtain ⟨k, hk⟩ := he
    omega
  obtain ⟨b, hb⟩ := hcomp
  let z : Fin n → Fin 3 := fun v => if v ∈ U.1 then 0 else 1
  let E : Fin 6 → ℕ := ![a, 1, 0, b, 0, 0]
  have hh : histogram z = endpointSizes E := by
    ext c
    fin_cases c
    · simp [histogram, z, endpointSizes, E, ← ha]
    · have hc : U.1ᶜ.card = n - U.1.card := by simp [Finset.card_compl]
      simp only [histogram, z, endpointSizes, E, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      simp
      omega
    · simp [histogram, z, endpointSizes, E, ite_eq_iff]
  obtain ⟨M, hM⟩ := exists_pairing_of_endpoints z E hh
  refine ⟨fromPairing M, ?_⟩
  have hcross := hM 0
  have heq : (crossingCount U.1 (fromPairing M) : ℝ) = crossCoordinate z 0 M := by
    rw [crossingCount_fromPairing]
    simp [crossCoordinate, crossPair, tableCoordinate, z, Fintype.card_subtype,
      Finset.sum_boole]
  change (crossingCount U.1 (fromPairing M) : ℝ) - 1 = 0
  rw [heq, hcross]
  simp [E]

lemma edge_has_tight_matching {n : ℕ} (hn : 4 ≤ n) (he : Even n) (e : Edge n) :
    ∃ M : PerfectMatching n, slack (Sum.inl e) M = 0 := by
  classical
  obtain ⟨k, hk⟩ := he
  let f : (Fin k × Bool) ≃ Fin n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega)
  let P : Pairing (Fin n) := Pairing.transport f standardPairing
  by_cases hP : P.1 e.1.1 = e.1.2
  · have hcard : ({e.1.1, e.1.2} : Finset (Fin n)).card <
        (Finset.univ : Finset (Fin n)).card := by
      have hh := Finset.card_le_two (a := e.1.1) (b := e.1.2)
      simpa using lt_of_le_of_lt hh (show 2 < n by omega)
    obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hca : c ≠ e.1.1 := by simpa using (not_or.mp (by simpa using hc)).1
    have hcb : c ≠ e.1.2 := by simpa using (not_or.mp (by simpa using hc)).2
    let Q := Pairing.relabel (Equiv.swap e.1.2 c) P
    have hQ : Q.1 e.1.1 = c := by
      simp [Q, Equiv.swap_apply_of_ne_of_ne (ne_of_lt e.2) hca.symm, hP]
    refine ⟨fromPairing Q, ?_⟩
    simp [slack, mem_fromPairing, hQ, hcb]
  · refine ⟨fromPairing P, ?_⟩
    simp [slack, mem_fromPairing, hP]

lemma row_has_tight_matching {n : ℕ} (hn : 4 ≤ n) (he : Even n) (i : Row n) :
    ∃ M : PerfectMatching n, slack i M = 0 := by
  cases i with
  | inl e => exact edge_has_tight_matching hn he e
  | inr U => exact oddCut_has_tight_matching he U

end PerfectMatchingPSD

end OAI
