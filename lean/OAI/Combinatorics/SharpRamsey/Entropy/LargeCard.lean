import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.SinglesUnique

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.AmbientEnumeration
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]
omit [Fintype D] in
lemma large_card (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) :
    Fintype.card (Components weight s t) - (simpleSet weight s t).card =
      (largeLabels (componentMap (strongGraph weight s t))).card := by
  rw [← large_image, Finset.card_image_of_injective _ (vertex_injective weight s t),
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]

end SharpRamseyFive.AmbientEnumeration

namespace SharpRamseyFive.AmbientEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
open SharpRamseyFive.WeightedPrograms
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def vertexExpansion (weight : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (E : Finset V) (f : V → H) : ℝ :=
  badExpansion
    (fun u f => independentWeight weight (fun d => L * weight d) lines R J base (f u) +
      alpha weight (lines ∘ f) t u ^ K)
    (fun A f => vertexBadMass weight (fun d => L * weight d) (lines ∘ f) t R J A) E f
omit [Fintype H] [DecidableEq H] in

lemma vertexExpansion_nonneg (weight : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (E : Finset V) (f : V → H) :
    0 ≤ vertexExpansion weight lines t R J K L base E f := by
  apply Finset.sum_nonneg
  intro U _
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro u _
    exact add_nonneg (independentWeight_nonneg _ _ _ _ _ _ _) (pow_nonneg (alpha_nonneg _ _ _ _) _)
  · exact vertexBadMass_nonneg _ _ _ _ _ _ _
omit [Fintype H] [DecidableEq H] in

lemma designated_le_partition (weight : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (f : V → H) :
    designatedBound weight (lines ∘ f) t R J K L base ≤
      Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) ^
        (largeLabels (componentMap (strongGraph weight (lines ∘ f) t))).card *
      (Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) ^
        (singles (componentMap (strongGraph weight (lines ∘ f) t))).card *
        vertexExpansion weight lines t R J K L base
          (singles (componentMap (strongGraph weight (lines ∘ f) t))) f) := by
  have ht := mul_le_mul_of_nonneg_left
    (designation_sum_le_vertex weight lines f t R J K L base)
    (show 0 ≤ Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) ^ (simpleSet weight (lines ∘ f) t).card *
      Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) ^
        (Fintype.card (Components weight (lines ∘ f) t) - (simpleSet weight (lines ∘ f) t).card) by positivity)
  change designatedBound weight (lines ∘ f) t R J K L base ≤ _ at ht
  rw [large_card, simple_card, simple_image] at ht
  exact ht.trans_eq (by unfold vertexExpansion; ring)

theorem designation_sum_enumerated (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (R : ℕ) (L : ℝ≥0) (denom rootB mass C D₀ base A : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ rootB) (hm : 0 ≤ mass) (hC : 0 ≤ C)
    (hD : 0 ≤ D₀) (hA : 0 ≤ A)
    (hmass : ∀ u, ∑ d ∈ lines u, ((L * weight d : ℝ≥0) : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := V) (B := Fin R)
      (fun z : H × V => lines z.1) (fun d => L * weight d) denom rootB mass K
      (N₁ * Fintype.card V) (N₂ * Fintype.card V) low) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, independentWeight weight (fun d => L * weight d) lines R J base x) ≤ D₀)
    (hsingle : Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) *
      (D₀ + 2 * ((Fintype.card V + 1 : ℝ) * C)) ≤ A)
    (Δ : ℕ) (hΔ : ∀ k, Fintype.card {k' : H // overlapRelation weight lines (1 / (100 * p)) k k'} ≤ Δ)
    (hnum : ∀ m : ℕ, 2 ≤ m → m ≤ Fintype.card V →
      Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) *
        ((m : ℝ) ^ 2 * Fintype.card (RelatedPair (overlapRelation weight lines (1 / (100 * p)))) *
          ((m : ℝ) ^ 2 * Δ) ^ (m - 2)) ≤ A ^ m) :
    (∑ f : V → H, designatedBound weight (lines ∘ f) (1 / (100 * p)) R J K L base) ≤
      (Fintype.card V : ℝ) ^ Fintype.card V * A ^ Fintype.card V := by
  let t : ℝ := 1 / (100 * p)
  let a := Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R))
  let b := Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R))
  let F (E : Finset V) (f : V → H) := a ^ E.card * vertexExpansion weight lines t R J K L base E f
  have hres (r : V → V) (g : V → H) :
      completionSum (singles r) g (F (singles r)) ≤ A ^ (singles r).card := by
    change completionSum (singles r) g (fun f => a ^ (singles r).card *
      vertexExpansion weight lines t R J K L base (singles r) f) ≤ _
    rw [completionSum_mul]
    apply (mul_le_mul_of_nonneg_left (actual_all_singleton_enumeration weight
      (fun d => L * weight d) lines hp hc R denom rootB mass C D₀ base hd hb hm hC hD
      hmass K J h N₁ N₂ hK hh low hsize herr hN₁ hN₂ hBC hrow hpair hDsum (singles r) g)
        (show 0 ≤ a ^ (singles r).card by dsimp [a]; positivity)).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hsingle _
  apply (Finset.sum_le_sum (fun f _ => designated_le_partition weight lines t R J K L base f)).trans
  have ht := graph_partition_sum (V := V) (overlapRelation weight lines t)
    (overlapRelation_symm weight lines t) b A (Real.exp_pos _).le hA Δ hΔ hnum F
    (fun E f => mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (vertexExpansion_nonneg _ _ _ _ _ _ _ _ _ _)) hres
  simpa only [relation_graph_eq] using ht

end SharpRamseyFive.AmbientEnumeration

namespace SharpRamseyFive.MomentBudgets
open scoped BigOperators

lemma block_cost (P B E Δ : ℝ) (p m : ℕ) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hE : 0 ≤ E) (hΔ : 0 ≤ Δ) (hm : 2 ≤ m) (hmp : m ≤ p)
    (hp : (p : ℝ) ^ 2 ≤ Real.exp (P / 10))
    (hpair : E ≤ B ^ 2 * Real.exp (P / 10))
    (hdeg : Δ ≤ B * Real.exp (-P)) :
    Real.exp (-(7 / 10 : ℝ) * P) *
      ((m : ℝ) ^ 2 * E * ((m : ℝ) ^ 2 * Δ) ^ (m - 2)) ≤
      (B * Real.exp (-(1 / 5 : ℝ) * P)) ^ m := by
  let A := B * Real.exp (-(1 / 5 : ℝ) * P)
  have hA : 0 ≤ A := mul_nonneg hB (Real.exp_pos _).le
  have hm2 : (m : ℝ) ^ 2 ≤ Real.exp (P / 10) := by
    apply (pow_le_pow_left₀ (by positivity) (show (m : ℝ) ≤ p by exact_mod_cast hmp) 2).trans hp
  have hfirst : Real.exp (-(7 / 10 : ℝ) * P) * ((m : ℝ) ^ 2 * E) ≤ A ^ 2 := by
    calc
      _ ≤ Real.exp (-(7 / 10 : ℝ) * P) * (Real.exp (P / 10) * (B ^ 2 * Real.exp (P / 10))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hm2 hpair hE (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = B ^ 2 * Real.exp (-(1 / 2 : ℝ) * P) := by
        rw [show Real.exp (-(7 / 10 : ℝ) * P) * (Real.exp (P / 10) * (B ^ 2 * Real.exp (P / 10))) =
          B ^ 2 * (Real.exp (-(7 / 10 : ℝ) * P) * Real.exp (P / 10) * Real.exp (P / 10)) by ring]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ B ^ 2 * Real.exp (-(2 / 5 : ℝ) * P) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg B)
      _ = A ^ 2 := by
        dsimp [A]
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  have hstep : (m : ℝ) ^ 2 * Δ ≤ A := by
    calc
      _ ≤ Real.exp (P / 10) * (B * Real.exp (-P)) :=
        mul_le_mul hm2 hdeg hΔ (Real.exp_pos _).le
      _ = B * Real.exp (-(9 / 10 : ℝ) * P) := by
        rw [show Real.exp (P / 10) * (B * Real.exp (-P)) = B * (Real.exp (P / 10) * Real.exp (-P)) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ A := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hB
  calc
    _ = (Real.exp (-(7 / 10 : ℝ) * P) * ((m : ℝ) ^ 2 * E)) *
      ((m : ℝ) ^ 2 * Δ) ^ (m - 2) := by ring
    _ ≤ A ^ 2 * A ^ (m - 2) := mul_le_mul hfirst
      (pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) hΔ) hstep _) (by positivity) (pow_nonneg hA _)
    _ = A ^ m := by rw [← pow_add, Nat.add_sub_of_le hm]

lemma singleton_cost (P B M : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hM : M ≤ B * Real.exp (P / 5)) :
    Real.exp (-(17 / 25 : ℝ) * P) * M ≤ B * Real.exp (-(1 / 5 : ℝ) * P) := by
  calc
    _ ≤ Real.exp (-(17 / 25 : ℝ) * P) * (B * Real.exp (P / 5)) :=
      mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = B * Real.exp (-(12 / 25 : ℝ) * P) := by
      rw [show Real.exp (-(17 / 25 : ℝ) * P) * (B * Real.exp (P / 5)) =
        B * (Real.exp (-(17 / 25 : ℝ) * P) * Real.exp (P / 5)) by ring, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hB

lemma partition_cost (P B : ℝ) (p : ℕ) (hB : 0 ≤ B)
    (hp : (p : ℝ) ≤ Real.exp (P / 10)) :
    (p : ℝ) ^ p * (B * Real.exp (-(1 / 5 : ℝ) * P)) ^ p ≤
      B ^ p * Real.exp (-(1 / 10 : ℝ) * (p * P)) := by
  calc
    _ ≤ Real.exp (P / 10) ^ p * (B * Real.exp (-(1 / 5 : ℝ) * P)) ^ p :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hp _) (by positivity)
    _ = _ := by
      rw [← mul_pow, show Real.exp (P / 10) * (B * Real.exp (-(1 / 5 : ℝ) * P)) =
        B * (Real.exp (P / 10) * Real.exp (-(1 / 5 : ℝ) * P)) by ring, ← Real.exp_add,
        mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

end SharpRamseyFive.MomentBudgets

namespace SharpRamseyFive.AmbientEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
open SharpRamseyFive.WeightedPrograms
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]

theorem ambient_refined_truncated_moment (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (R : ℕ) (own : H → Fin R → Bool)
    (L : ℝ≥0) (denom rootB mass C D₀ base B : ℝ)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ k, (3 / 4 : ℝ) ≤ PoissonScore.mass weight (lines k))
    (hdelta : ∀ k, |PoissonScore.mass weight (lines k) - base| ≤ (17 / 100 : ℝ))
    (hd : 0 < denom) (hb : 1 ≤ rootB) (hm : 0 ≤ mass) (hC : 0 ≤ C)
    (hD : 0 ≤ D₀) (hB : 0 ≤ B)
    (hmass : ∀ u, ∑ d ∈ lines u, ((L * weight d : ℝ≥0) : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hKR : K ≤ R / 2) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (p : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L * weight d) denom rootB mass K
      (N₁ * p) (N₂ * p) low) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, independentWeight weight (fun d => L * weight d) lines R J base x) ≤ D₀)
    (hcost : D₀ + 2 * ((p + 1 : ℝ) * C) ≤ B * Real.exp (((L : ℝ) * R) / 5))
    (hp2 : (p : ℝ) ^ 2 ≤ Real.exp (((L : ℝ) * R) / 10))
    (Δ : ℕ) (hΔ : ∀ k, Fintype.card {k' : H // overlapRelation weight lines (1 / (100 * p)) k k'} ≤ Δ)
    (hdeg : (Δ : ℝ) ≤ B * Real.exp (-((L : ℝ) * R)))
    (hRelPairs : (Fintype.card (RelatedPair (overlapRelation weight lines (1 / (100 * p)))) : ℝ) ≤
      B ^ 2 * Real.exp (((L : ℝ) * R) / 10)) :
    (∫ ω, HighMoment.allTrunc R J ω *
      (∑ k : H, scoreTerm (lines k) (Real.exp (-(L : ℝ) * base)) (own k)
        (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => L * weight i.2)) ≤
        B ^ p * Real.exp (-(1 / 10 : ℝ) * (p * ((L : ℝ) * R))) := by
  have hP : 0 ≤ (L : ℝ) * R := by positivity
  apply (truncated_power_designated weight R J K L base lines own hp hL hbase hlower hdelta hKR).trans
  have hs := designation_sum_enumerated (V := Fin p) weight lines hp (by simp)
    R L denom rootB mass C D₀ base (B * Real.exp (-(1 / 5 : ℝ) * ((L : ℝ) * R))) hd hb hm hC hD
    (by positivity) hmass K J h N₁ N₂ hK hh low hsize
    (by simpa only [Fintype.card_fin] using herr) hN₁ hN₂
    (by simpa only [Fintype.card_fin] using hBC) hrow hpair hDsum
    (by simpa only [Fintype.card_fin] using MomentBudgets.singleton_cost _ B _ hP hB hcost)
    Δ hΔ (fun m hm hmp => MomentBudgets.block_cost _ B _ _ p m hP hB
      (by positivity) (by positivity) hm (by simpa only [Fintype.card_fin] using hmp) hp2 hRelPairs hdeg)
  apply hs.trans
  simp only [Fintype.card_fin]
  apply MomentBudgets.partition_cost _ B p hB
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact (show (p : ℝ) ≤ (p : ℝ) ^ 2 by nlinarith).trans hp2

omit [DecidableEq D] in

lemma allTrunc_eq_one {R J : ℕ} (h : R < J) (ω : Fin R × D → ℕ) :
    HighMoment.allTrunc R J ω = 1 := by
  apply Finset.prod_eq_one
  intro d _
  unfold lineTrunc
  apply ite_eq_left
  exact (show (Finset.univ.filter (fun r => ω (r,d) ≠ 0)).card ≤ R by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun r : Fin R => ω (r,d) ≠ 0) Finset.univ)).trans_lt h

theorem ambient_untruncated_moment (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (R : ℕ) (own : H → Fin R → Bool)
    (L : ℝ≥0) (denom rootB mass C D₀ base B : ℝ)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ k, (3 / 4 : ℝ) ≤ PoissonScore.mass weight (lines k))
    (hdelta : ∀ k, |PoissonScore.mass weight (lines k) - base| ≤ (17 / 100 : ℝ))
    (hd : 0 < denom) (hb : 1 ≤ rootB) (hm : 0 ≤ mass) (hC : 0 ≤ C)
    (hD : 0 ≤ D₀) (hB : 0 ≤ B)
    (hmass : ∀ u, ∑ d ∈ lines u, ((L * weight d : ℝ≥0) : ℝ) ≤ mass)
    (K h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hKR : K ≤ R / 2) (hh : 0 < h)
    (hsize : h ≤ (R / 2) / (2 * K))
    (herr : (p : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L * weight d) denom rootB mass K
      (N₁ * p) (N₂ * p) true) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, |PoissonScore.mass weight (lines x) - base| ^ (R / 2)) ≤ D₀)
    (hcost : D₀ + 2 * ((p + 1 : ℝ) * C) ≤ B * Real.exp (((L : ℝ) * R) / 5))
    (hp2 : (p : ℝ) ^ 2 ≤ Real.exp (((L : ℝ) * R) / 10))
    (Δ : ℕ) (hΔ : ∀ k, Fintype.card {k' : H // overlapRelation weight lines (1 / (100 * p)) k k'} ≤ Δ)
    (hdeg : (Δ : ℝ) ≤ B * Real.exp (-((L : ℝ) * R)))
    (hRelPairs : (Fintype.card (RelatedPair (overlapRelation weight lines (1 / (100 * p)))) : ℝ) ≤
      B ^ 2 * Real.exp (((L : ℝ) * R) / 10)) :
    (∫ ω, (∑ k : H, scoreTerm (lines k) (Real.exp (-(L : ℝ) * base)) (own k)
        (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => L * weight i.2)) ≤
        B ^ p * Real.exp (-(1 / 10 : ℝ) * (p * ((L : ℝ) * R))) := by
  have hs := ambient_refined_truncated_moment weight lines hp R own L denom rootB mass C D₀ base B
    hL hbase hlower hdelta hd hb hm hC hD hB hmass K (R+1) h N₁ N₂ hK hKR hh true
    (by simpa using hsize) herr hN₁ hN₂ hBC hrow hpair
    (by simpa only [independentWeight, Nat.lt_succ_self, ite_true, add_zero] using hDsum)
    hcost hp2 Δ hΔ hdeg hRelPairs
  simpa only [allTrunc_eq_one (Nat.lt_succ_self R), one_mul] using hs

end SharpRamseyFive.AmbientEnumeration

namespace SharpLogRamsey.MomentBudgetBridge

def anchorBudget (p : ℕ) (P : ℝ) : ℝ := 200 * (p : ℝ) + 2 * P

def certificateOverhead (p D : ℕ) (P : ℝ) : ℝ :=
  1 + 4 * (p : ℝ)^2 + 4 * (p : ℝ)^3 * anchorBudget p P +
    (p : ℝ)^4 * (anchorBudget p P)^2 +
    (p : ℝ)^4 * ((D : ℝ)+4) * (2*P)^200

lemma anchorBudget_nonneg (p : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ anchorBudget p P := by
  unfold anchorBudget
  positivity

lemma certificateOverhead_nonneg (p D : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ certificateOverhead p D P := by
  have hA := anchorBudget_nonneg p hP
  unfold certificateOverhead
  positivity

theorem labelled_branching_bound (p D : ℕ) (P B H N M : ℝ)
    (hP : 0 ≤ P) (hB : 1 ≤ B) (hH : H ≤ 4*B^2) (hN : N ≤ 4*B)
    (hM : M ≤ (p : ℝ)^2 * (B^2 * Real.exp (P/50) * ((D : ℝ)+4) * (2*P)^200)) :
    1 + (((p : ℝ)*(H*p)/B)/B^8 +
      (p : ℝ)^2*(N*p)*anchorBudget p P/B +
      ((p : ℝ)^3*p*(anchorBudget p P)^2/B)*B +
      (p : ℝ)^2*M/B^2) ≤ Real.exp (P/50)*certificateOverhead p D P := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hA := anchorBudget_nonneg p hP
  have he : 1 ≤ Real.exp (P/50) := Real.one_le_exp_iff.mpr (by positivity)
  have hroot : ((p : ℝ)*(H*p)/B)/B^8 ≤ 4*(p : ℝ)^2 := by
    apply (div_le_iff₀ (pow_pos hB0 8)).mpr
    apply (div_le_iff₀ hB0).mpr
    have hpow : B^2 ≤ B^9 := pow_le_pow_right₀ hB (by decide)
    calc
      (p : ℝ)*(H*p) ≤ (p : ℝ)*(4*B^2*p) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hH hp) hp
      _ = 4*(p : ℝ)^2*B^2 := by ring
      _ ≤ 4*(p : ℝ)^2*B^9 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 4*(p : ℝ)^2*B^8*B := by ring
  have hanchor : (p : ℝ)^2*(N*p)*anchorBudget p P/B ≤
      4*(p : ℝ)^3*anchorBudget p P := by
    apply (div_le_iff₀ hB0).mpr
    calc
      _ ≤ (p : ℝ)^2*(4*B*p)*anchorBudget p P := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN hp) (by positivity)) hA
      _ = _ := by ring
  have htwo : ((p : ℝ)^3*p*(anchorBudget p P)^2/B)*B =
      (p : ℝ)^4*(anchorBudget p P)^2 := by
    rw [div_mul_cancel₀ _ hB0.ne']
    ring
  have hpair : (p : ℝ)^2*M/B^2 ≤
      Real.exp (P/50)*((p : ℝ)^4*((D : ℝ)+4)*(2*P)^200) := by
    apply (div_le_iff₀ (pow_pos hB0 2)).mpr
    calc
      _ ≤ (p : ℝ)^2*((p : ℝ)^2*(B^2*Real.exp (P/50)*((D : ℝ)+4)*(2*P)^200)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by ring
  have hplain : 1 + 4*(p : ℝ)^2 + 4*(p : ℝ)^3*anchorBudget p P +
      (p : ℝ)^4*(anchorBudget p P)^2 ≤
      Real.exp (P/50)*(1 + 4*(p : ℝ)^2 + 4*(p : ℝ)^3*anchorBudget p P +
      (p : ℝ)^4*(anchorBudget p P)^2) := by
    exact le_mul_of_one_le_left (by positivity) he
  unfold certificateOverhead
  rw [htwo]
  nlinarith only [hroot, hanchor, hpair, hplain]

theorem absorb_certificate (p D : ℕ) (P : ℝ)
    (h : certificateOverhead p D P ≤ Real.exp (2*P/25)) :
    Real.exp (P/50)*certificateOverhead p D P ≤ Real.exp (P/10) := by
  calc
    _ ≤ Real.exp (P/50)*Real.exp (2*P/25) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem singleton_budget (p : ℕ) (B P : ℝ) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hp : 2*(p : ℝ)+3 ≤ Real.exp (P/10)) :
    B*Real.exp (P/100) + 2*((p+1 : ℝ)*(B*Real.exp (P/10))) ≤
      B*Real.exp (P/5) := by
  have he : Real.exp (P/100) ≤ Real.exp (P/10) := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ B*Real.exp (P/10)+2*((p+1 : ℝ)*(B*Real.exp (P/10))) := by
      linarith only [mul_le_mul_of_nonneg_left he hB]
    _ = (B*Real.exp (P/10))*(2*(p : ℝ)+3) := by ring
    _ ≤ (B*Real.exp (P/10))*Real.exp (P/10) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hB (Real.exp_pos _).le)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

def shiftOverhead (p D : ℕ) : ℝ := 4+(D : ℝ)*(200*(p : ℝ))^200

lemma shifted_dyadic_budget (p D : ℕ) (P C : ℝ) (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hpoly : shiftOverhead p D ≤ Real.exp (2*P/25)) :
    4*C+(D : ℝ)*C*Real.exp (P/50)*(2*(p : ℝ))^200 ≤ C*Real.exp (P/10) := by
  have he : 1 ≤ Real.exp (P/50) := Real.one_le_exp_iff.mpr (by positivity)
  have hp : (2*(p : ℝ))^200 ≤ (200*(p : ℝ))^200 :=
    pow_le_pow_left₀ (by positivity) (by have := (Nat.cast_nonneg p : (0 : ℝ) ≤ p); linarith) _
  have heC : 4*C ≤ 4*C*Real.exp (P/50) := le_mul_of_one_le_right (by positivity) he
  have hpow := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (D : ℝ)*C*Real.exp (P/50) by positivity)
  calc
    _ ≤ C*Real.exp (P/50)*shiftOverhead p D := by
      unfold shiftOverhead
      nlinarith only [heC, hpow]
    _ ≤ C*Real.exp (P/50)*Real.exp (2*P/25) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma strong_dyadic_budget (p D : ℕ) (P C : ℝ) (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hpoly : shiftOverhead p D ≤ Real.exp (2*P/25)) :
    4*C+(D : ℝ)*C*Real.exp (P/50)*(200*(p : ℝ))^200 ≤ C*Real.exp (P/10) := by
  have he : 1 ≤ Real.exp (P/50) := Real.one_le_exp_iff.mpr (by positivity)
  have heC : 4*C ≤ 4*C*Real.exp (P/50) := le_mul_of_one_le_right (by positivity) he
  calc
    _ ≤ C*Real.exp (P/50)*shiftOverhead p D := by
      unfold shiftOverhead
      nlinarith only [heC]
    _ ≤ C*Real.exp (P/50)*Real.exp (2*P/25) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end SharpLogRamsey.MomentBudgetBridge
end

end OAI
