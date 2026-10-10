import Mathlib
import OAI.Combinatorics.KMedian.Hardness.Lists
import OAI.Combinatorics.KMedian.Hardness.SamplingCounts

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.ProjectionSystem
open Finset

variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

def sample (J : Type) : ProjectionSystem U (V × (J → I)) J A B where
  neighbor p j := G.neighbor p.1 (p.2 j)
  project p j a := G.project p.1 (p.2 j) a

variable (J : Type) [Fintype J] [DecidableEq J]

omit [Fintype U] [Fintype V] [Fintype I] [Fintype A] [Fintype B]
  [DecidableEq U] [DecidableEq V] [DecidableEq I] [DecidableEq A] [DecidableEq B]
  [Fintype J] [DecidableEq J] in
theorem sample_consistent (hdup : G.DuplicateConsistent) :
    (G.sample J).DuplicateConsistent := by
  intro p j k h a
  exact hdup p.1 (p.2 j) (p.2 k) h a

omit [Fintype U] [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] [DecidableEq A] [DecidableEq B] in
theorem sample_sum (f : U → ℕ) :
    (∑ p, ∑ j, f ((G.sample J).neighbor p j)) =
      Fintype.card J * Fintype.card I ^ (Fintype.card J-1) *
        ∑ v, ∑ i, f (G.neighbor v i) := by
  change (∑ p : V × (J → I), ∑ j, f (G.neighbor p.1 (p.2 j))) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ v, ∑ j : J, ∑ s : J → I, f (G.neighbor v (s j)) := by
      apply sum_congr rfl
      intro v _
      rw [sum_comm]
    _ = ∑ v, ∑ _ : J, Fintype.card I ^ (Fintype.card J-1) * ∑ i, f (G.neighbor v i) := by
      apply sum_congr rfl
      intro v _
      apply sum_congr rfl
      intro j _
      exact coordinate_sum j (fun i => f (G.neighbor v i))
    _ = _ := by
      simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,← mul_assoc]
      rw [mul_sum]

omit [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B] in
theorem sample_regular {d : ℕ} (hreg : G.LeftRegular d) :
    (G.sample J).LeftRegular (Fintype.card J * Fintype.card I ^ (Fintype.card J-1) * d) := by
  intro u
  rw [card_filter,Fintype.sum_prod_type]
  rw [G.sample_sum J (fun x => if x = u then 1 else 0)]
  rw [G.regular_sum hreg (fun x => if x = u then 1 else 0)]
  simp

def satisfied (left : U → A) (right : V → B) : Finset (V × I) :=
  univ.filter (fun p => G.project p.1 p.2 (left (G.neighbor p.1 p.2)) = right p.1)

omit [Fintype U] [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] [DecidableEq A] in
theorem satisfied_card (left : U → A) (right : V → B) :
    (G.satisfied left right).card =
      ∑ v, (univ.filter (fun i => G.project v i (left (G.neighbor v i)) = right v)).card := by
  simp only [satisfied,card_filter,Fintype.sum_prod_type]

omit [Fintype U] [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] [DecidableEq A] in
theorem sample_agreement_card (left : U → A) :
    ((G.sample J).agreement left).card =
      ∑ v, (univ.filter (fun s : J → I => ∃ j k, j ≠ k ∧
        G.project v (s j) (left (G.neighbor v (s j))) =
        G.project v (s k) (left (G.neighbor v (s k))))).card := by
  change (univ.filter (fun p : V × (J → I) => ∃ j k, j ≠ k ∧
    G.project p.1 (p.2 j) (left (G.neighbor p.1 (p.2 j))) =
    G.project p.1 (p.2 k) (left (G.neighbor p.1 (p.2 k))))).card = _
  rw [card_filter,Fintype.sum_prod_type]
  simp only [card_filter]

omit [Fintype U] [Fintype A] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] [DecidableEq A] in
theorem sample_agreement_bound [Nonempty B] (hJ : 0 < Fintype.card J) (ε : ℝ)
    (hsound : ∀ left right, ((G.satisfied left right).card:ℝ) ≤
      ε * Fintype.card V * Fintype.card I) (left : U → A) :
    (((G.sample J).agreement left).card:ℝ) ≤
      ((Fintype.card J:ℝ)^2 * ε) * Fintype.card (V × (J → I)) := by
  classical
  let color (v : V) (i : I) := G.project v i (left (G.neighbor v i))
  let count (v : V) (b : B) := (univ.filter (fun i => color v i = b)).card
  have hmax (v : V) : ∃ b : B, ∀ b', count v b' ≤ count v b := by
    obtain ⟨b,_,hb⟩ := exists_max_image univ (count v) univ_nonempty
    exact ⟨b,fun b' => hb b' (mem_univ b')⟩
  choose right hr using hmax
  have hs : (∑ v, (count v (right v):ℝ)) ≤ ε * Fintype.card V * Fintype.card I := by
    simpa only [G.satisfied_card left right,Nat.cast_sum] using hsound left right
  have hp (v : V) :
      ((univ.filter (fun s : J → I => ∃ j k, j ≠ k ∧ color v (s j) = color v (s k))).card:ℝ) ≤
        (Fintype.card J:ℝ)^2 * (Fintype.card I:ℝ)^(Fintype.card J-1) * count v (right v) := by
    exact_mod_cast sampled_agreement_count (J := J) (color v) (count v (right v)) (hr v)
  have hpow : (Fintype.card I:ℝ)^Fintype.card J =
      (Fintype.card I:ℝ)^(Fintype.card J-1) * Fintype.card I := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ Fintype.card J)]
  rw [G.sample_agreement_card J left,Nat.cast_sum]
  calc
    _ ≤ ∑ v, (Fintype.card J:ℝ)^2 * (Fintype.card I:ℝ)^(Fintype.card J-1) * count v (right v) :=
      sum_le_sum (fun v _ => hp v)
    _ = (Fintype.card J:ℝ)^2 * (Fintype.card I:ℝ)^(Fintype.card J-1) *
        ∑ v, (count v (right v):ℝ) := by rw [mul_sum]
    _ ≤ (Fintype.card J:ℝ)^2 * (Fintype.card I:ℝ)^(Fintype.card J-1) *
        (ε * Fintype.card V * Fintype.card I) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [Fintype.card_prod,Fintype.card_fun,Nat.cast_mul,Nat.cast_pow,hpow]
      ring

omit [DecidableEq V] [DecidableEq I] in
theorem sample_perfect (left : U → A) (right : V → B)
    (h : ∀ v i, G.project v i (left (G.neighbor v i)) = right v) :
    ∃ S : Finset (U × A), S.card ≤ Fintype.card U ∧ (G.sample J).covered S = univ := by
  exact (G.sample J).perfect_cover left (fun p => right p.1) (fun p j => h p.1 (p.2 j))

theorem sampled_coverage_bound [Nonempty B] {d : ℕ} (hreg : G.LeftRegular d)
    (hdup : G.DuplicateConsistent) (hJ : 1 < Fintype.card J)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U)
    {t : ℕ} (ht : 1 ≤ t) (default : A) (ε : ℝ)
    (hsound : ∀ left right, ((G.satisfied left right).card:ℝ) ≤
      ε * Fintype.card V * Fintype.card I) :
    (((G.sample J).covered S).card:ℝ) ≤
      (1-(1-1/(Fintype.card J:ℝ))^Fintype.card J+
        (Fintype.card J:ℝ)/t+(t:ℝ)^2*(Fintype.card J:ℝ)^2*ε) *
        ((Fintype.card (V × (J → I)):ℝ)*(Fintype.card J:ℝ)^Fintype.card B) := by
  have hc := (G.sample J).coverage_agreement_bound (G.sample_regular J hreg) hJ
    (G.sample_consistent J hdup) S hS ht default ((Fintype.card J:ℝ)^2*ε)
    (G.sample_agreement_bound J (by omega) ε hsound)
  convert hc using 1; ring

end MetricKMedian.Coverage.ProjectionSystem

end Inline_PCPInherited

end OAI
