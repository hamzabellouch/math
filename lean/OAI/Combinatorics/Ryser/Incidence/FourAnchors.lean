import OAI.Combinatorics.Ryser.Incidence.FourAnchorsGeometry
import OAI.Combinatorics.Ryser.Incidence.FourAnchorsLocal
import OAI.Combinatorics.Ryser.Incidence.FourAnchorsNumerics
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Real.Sqrt

namespace OAI

noncomputable section

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [DecidableEq F]

theorem fourAnchors_of_pruned_r
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U) (hrlarge : 4096 * U ^ 7 ≤ r)
    (hPlo : r ^ 2 / (32 * U ^ 4) ≤ (P.card : ℝ))
    (hPup : (P.card : ℝ) ≤ U * r ^ 2)
    (hLup : (L.card : ℝ) ≤ U * r ^ 2)
    (hpoints : ∀ p ∈ P, r / (8 * U ^ 2) ≤
      ((L.filter fun l => ProjectiveIncidence p l).card : ℝ))
    (hlines : ∀ l ∈ L, r / (8 * U ^ 2) ≤
      ((P.filter fun p => ProjectiveIncidence p l).card : ℝ))
    (hcap : ∀ l ∈ L, ((P.filter fun p => ProjectiveIncidence p l).card : ℝ) ≤
      16 * U ^ 3 * r) :
    ∃ c ∈ anchorConfigurations ProjectiveIncidence P L,
      r ^ 2 / (9 * 2 ^ 57 * U ^ 39) ≤
        ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ) := by
  classical
  have hUpos : 0 < U := by linarith
  let d : ℝ := r / (8 * U ^ 2)
  let extra : ℝ := r ^ 2 / (256 * U ^ 4)
  let T0 : ℝ := r ^ 5 / (9 * 2 ^ 32 * U ^ 20)
  have hd : 1 ≤ d := by
    have := fourAnchors_degree_lower hr hU hrlarge
    dsimp [d]
    linarith
  have hextra : 0 ≤ extra := by dsimp [extra]; positivity
  have hlocal (x : ProjectivePoint F) (hx : x ∈ P) :
      extra * T0 ≤
        ((anchorConfigurations ProjectiveIncidence
          (joinedNeighbors ProjectiveIncidence P L x) L).card : ℝ) := by
    let N := joinedNeighbors ProjectiveIncidence P L x
    have hNP : N ⊆ P := by
      intro p hp
      simp only [N, joinedNeighbors, Finset.mem_filter] at hp
      exact hp.1
    have hN : r ^ 2 / (128 * U ^ 4) ≤ (N.card : ℝ) :=
      (fourAnchors_pair_lower hr hU hrlarge).trans
        (projective_joinedNeighbors_card_lower P L x hx hd (hpoints x hx) hlines)
    have hdegree : ∀ p ∈ N, d ≤
        ((L.filter fun l => ProjectiveIncidence p l).card : ℝ) :=
      fun p hp => hpoints p (hNP hp)
    have hsurplus : 0 ≤ d * (N.card : ℝ) - 2 * (U * r ^ 2) := by
      have h := fourAnchors_surplus_lower hr hU hrlarge hN
      have hnon : 0 ≤ r ^ 3 / (2048 * U ^ 6) := by positivity
      exact hnon.trans h
    have hbase : 0 ≤ d * (N.card : ℝ) - 2 * (L.card : ℝ) := by
      linarith
    have htriples : (2 / 9 : ℝ) * (d * (N.card : ℝ) - 2 * (L.card : ℝ)) ^ 3 ≤
        (L.card : ℝ) ^ 2 *
          ∑ l ∈ L, ((orderedTriples (N.filter fun p => ProjectiveIncidence p l)).card : ℝ) := by
      convert triple_sum_lower_bound ProjectiveIncidence N L d
        (by
          intro p hp
          convert hdegree p hp using 1; congr) hbase using 1; congr; funext l; congr
    have hcomparison : d * (N.card : ℝ) - 2 * (U * r ^ 2) ≤
        d * (N.card : ℝ) - 2 * (L.card : ℝ) := by linarith
    have hcount : (2 / 9 : ℝ) * (d * (N.card : ℝ) - 2 * (U * r ^ 2)) ^ 3 ≤
        (L.card : ℝ) ^ 2 *
          ∑ l ∈ L, ((orderedTriples (N.filter fun p => ProjectiveIncidence p l)).card : ℝ) := by
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hsurplus hcomparison 3) (by norm_num)).trans htriples
    have hT : T0 ≤
        ∑ l ∈ L, ((orderedTriples (N.filter fun p => ProjectiveIncidence p l)).card : ℝ) :=
      fourAnchors_count_lower hr hU hrlarge hN (Nat.cast_nonneg _) hLup
        (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hcount
    have hoff : ∀ l ∈ L,
        extra ≤ ((N.filter fun p => ¬ ProjectiveIncidence p l).card : ℝ) := by
      intro l hl
      have htrace : ((N.filter fun p => ProjectiveIncidence p l).card : ℝ) ≤
          16 * U ^ 3 * r := by
        apply le_trans _ (hcap l hl)
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter (fun p => ProjectiveIncidence p l) hNP)
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := N) (fun p => ProjectiveIncidence p l)
      have hpartition' : ((N.filter fun p => ProjectiveIncidence p l).card : ℝ) +
          ((N.filter fun p => ¬ ProjectiveIncidence p l).card : ℝ) = (N.card : ℝ) := by
        exact_mod_cast hpartition
      have hmargin := fourAnchors_margin_lower hr hU hrlarge
      dsimp [extra]
      linarith
    have hConfig : extra *
        (∑ l ∈ L, ((orderedTriples (N.filter fun p => ProjectiveIncidence p l)).card : ℝ)) ≤
        ((anchorConfigurations ProjectiveIncidence N L).card : ℝ) := by
      convert anchorConfigurations_card_lower ProjectiveIncidence N L extra hextra
        (by
          intro l hl
          convert hoff l hl using 1; congr) using 1; congr; funext l; congr
    exact (mul_le_mul_of_nonneg_left hT hextra).trans hConfig
  let total : ℝ := ∑ x ∈ P,
    ((anchorConfigurations ProjectiveIncidence
      (joinedNeighbors ProjectiveIncidence P L x) L).card : ℝ)
  have hTotal : r ^ 9 / (9 * 2 ^ 45 * U ^ 28) ≤ total := by
    apply fourAnchors_total_lower hr hU hPlo (le_refl extra) (le_refl T0)
    calc
      (P.card : ℝ) * extra * T0 = ∑ _x ∈ P, (extra * T0) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ total := Finset.sum_le_sum hlocal
  let C := anchorConfigurations ProjectiveIncidence P L
  have hExchange : total =
      ∑ c ∈ C, ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ) := by
    dsimp [total, C]
    exact_mod_cast sum_card_anchorConfigurations_neighbors ProjectiveIncidence P L
  have hC : C.Nonempty := by
    by_contra h
    have hEmpty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hEmpty] at hExchange
    simp only [Finset.sum_empty] at hExchange
    have hpos : 0 < r ^ 9 / (9 * 2 ^ 45 * U ^ 28) := by positivity
    linarith
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image C
    (fun c => ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ)) hC
  refine ⟨c, hc, ?_⟩
  apply fourAnchors_average_lower hr hU hTotal
  · exact (anchorConfigurations_card_upper ProjectiveIncidence P L
      (16 * U ^ 3 * r) (by positivity)
      (by
        intro l hl
        convert hcap l hl using 1; congr)).trans
        (fourAnchors_candidate_upper hr hU (Nat.cast_nonneg _) hLup
          (Nat.cast_nonneg _) hPup)
  · exact Nat.cast_nonneg _
  · rw [hExchange]
    calc
      (∑ c' ∈ C, ((anchorWitnesses ProjectiveIncidence P L c').card : ℝ)) ≤
          ∑ _c' ∈ C, ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ) :=
        Finset.sum_le_sum fun c' hc' => hmax c' hc'
      _ = (C.card : ℝ) * ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]

theorem fourAnchors_of_pruned
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    {q U : ℝ} (hq : 0 < q) (hU : 2 ≤ U)
    (hlarge : 4096 * U ^ 7 ≤ Real.sqrt q)
    (hPlo : q / (32 * U ^ 4) ≤ (P.card : ℝ))
    (hPup : (P.card : ℝ) ≤ U * q)
    (hLup : (L.card : ℝ) ≤ U * q)
    (hpoints : ∀ p ∈ P, Real.sqrt q / (8 * U ^ 2) ≤
      ((L.filter fun l => ProjectiveIncidence p l).card : ℝ))
    (hlines : ∀ l ∈ L, Real.sqrt q / (8 * U ^ 2) ≤
      ((P.filter fun p => ProjectiveIncidence p l).card : ℝ))
    (hcap : ∀ l ∈ L, ((P.filter fun p => ProjectiveIncidence p l).card : ℝ) ≤
      16 * U ^ 3 * Real.sqrt q) :
    ∃ c ∈ anchorConfigurations ProjectiveIncidence P L,
      q / (9 * 2 ^ 57 * U ^ 39) ≤
        ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ) := by
  have hsqrt : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  simpa only [hsqrt] using fourAnchors_of_pruned_r P L
    (Real.sqrt_pos.2 hq) hU hlarge
    (by simpa only [hsqrt] using hPlo)
    (by simpa only [hsqrt] using hPup)
    (by simpa only [hsqrt] using hLup) hpoints hlines hcap

end RyserCoveringCounterexample.Incidence

end

end OAI
