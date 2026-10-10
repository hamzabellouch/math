import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial
open scoped Classical

lemma coeff_comp_neg (P : ℝ[X]) (k : ℕ) :
    (P.comp (-X)).coeff k = P.coeff k * (-1)^k := by
  simpa using (comp_C_mul_X_coeff (p := P) (r := (-1:ℝ)) (n := k))

lemma natDegree_comp_neg (P : ℝ[X]) : (P.comp (-X)).natDegree = P.natDegree := by
  simp [natDegree_comp]

lemma eraseLead_comp_neg (P : ℝ[X]) :
    (P.comp (-X)).eraseLead = P.eraseLead.comp (-X) := by
  ext k
  simp only [eraseLead_coeff,coeff_comp_neg,natDegree_comp_neg]
  split_ifs <;> simp

lemma sign_pair_indicator (a b t : SignType) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    (if a = -b then 1 else 0 : ℕ) +
      (if -(t*a) = -(t*b) then 1 else 0) = 1 := by
  cases a <;> cases b <;> cases t <;> simp_all

lemma signVariations_pair_le (P : ℝ[X]) :
    P.signVariations + (P.comp (-X)).signVariations ≤ P.natDegree := by
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hp : P = 0
    · simp [hp]
    by_cases he : P.eraseLead = 0
    · rw [signVariations_eq_eraseLead_add_ite hp,
        signVariations_eq_eraseLead_add_ite (P := P.comp (-X)) (by simpa using hp),eraseLead_comp_neg,he]
      simp [hp]
    have hlt : P.eraseLead.natDegree < P.natDegree :=
      P.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right he
    have hi := ih P.eraseLead.natDegree (hd ▸ hlt) P.eraseLead rfl
    rw [signVariations_eq_eraseLead_add_ite hp,
      signVariations_eq_eraseLead_add_ite (P := P.comp (-X)) (by simpa using hp),eraseLead_comp_neg,
      comp_neg_X_leadingCoeff_eq,comp_neg_X_leadingCoeff_eq]
    by_cases hgap : P.natDegree = P.eraseLead.natDegree + 1
    · have hs := sign_pair_indicator (SignType.sign P.leadingCoeff)
        (SignType.sign P.eraseLead.leadingCoeff)
        (SignType.sign ((-1:ℝ)^P.eraseLead.natDegree))
        (by simpa using hp) (by simpa using he) (by simp)
      simp only [hgap,pow_succ,mul_neg_one,sign_mul,Left.sign_neg,neg_mul]
      omega
    · have hgap' : P.eraseLead.natDegree + 2 ≤ P.natDegree := by omega
      split_ifs <;> omega

lemma coeffList_mul_X (P : ℝ[X]) (hP : P ≠ 0) :
    (P*X).coeffList = P.coeffList ++ [0] := by
  rw [coeffList,coeffList,withBotSucc_degree_eq_natDegree_add_one (mul_ne_zero hP X_ne_zero),
    withBotSucc_degree_eq_natDegree_add_one hP,natDegree_mul_X hP,List.range_succ_eq_map]
  simp only [List.reverse_cons,← List.map_reverse,List.map_append,List.map_map,
    List.map_singleton,coeff_mul_X_zero]
  congr 1
  exact List.map_congr_left (fun k _ => coeff_mul_X P k)

lemma signVariations_mul_X (P : ℝ[X]) : (P*X).signVariations = P.signVariations := by
  by_cases hp : P = 0
  · simp [hp]
  simp [signVariations,coeffList_mul_X P hp,List.signVariations,List.filter_append]

lemma positive_negative_roots_card {P : ℝ[X]} (hP : P ≠ 0) (h0 : P.eval 0 ≠ 0) :
    P.roots.countP (0 < ·) + P.roots.countP (· < 0) = P.roots.card := by
  have hz : ∀ x ∈ P.roots, x ≠ 0 := by
    intro x hx h
    subst x
    exact h0 ((mem_roots hP).mp hx)
  rw [Multiset.card_eq_countP_add_countP (0 < ·)]
  congr 1
  apply Multiset.countP_congr rfl
  intro x hx
  have hn := hz x hx
  apply propext
  rcases lt_trichotomy x 0 with hx | hx | hx <;> simp_all <;> linarith

theorem signVariations_eq_positive_roots {P : ℝ[X]} (hP : P.Splits) :
    P.signVariations = P.roots.countP (0 < ·) := by
  induction hd : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hp : P = 0
    · simp [hp]
    by_cases h0 : P.eval 0 = 0
    · obtain ⟨Q,hQ⟩ := X_dvd_iff.mpr (by simpa only [coeff_zero_eq_eval_zero] using h0)
      have hqn : Q ≠ 0 := by intro h; simp [h] at hQ; exact hp hQ
      have he : P = Q*X := by simpa [mul_comm] using hQ
      have hdeg : Q.natDegree < P.natDegree := by rw [he,natDegree_mul_X hqn]; omega
      have hs : Q.Splits := hP.of_dvd hp ⟨X,he⟩
      have hi := ih Q.natDegree (hd ▸ hdeg) hs rfl
      rw [he,signVariations_mul_X,hi,roots_mul (mul_ne_zero hqn X_ne_zero)]
      have hz : Multiset.countP (fun x : ℝ => 0 < x) ({0} : Multiset ℝ) = 0 := by
        change Multiset.countP (fun x : ℝ => 0 < x) (0 ::ₘ 0) = 0
        rw [Multiset.countP_cons_of_neg _ (lt_irrefl _), Multiset.countP_zero]
      simp [hz]
    · have hpc := P.roots_countP_pos_le_signVariations
      have hnc := (P.comp (-X)).roots_countP_pos_le_signVariations
      have hsum := positive_negative_roots_card hp h0
      rw [splits_iff_card_roots.mp hP] at hsum
      simp only [roots_comp_neg_X,Multiset.countP_map,neg_pos,← Multiset.countP_eq_card_filter] at hnc
      have hv := signVariations_pair_le P
      omega

end Release061.SignElimination

end

end OAI
