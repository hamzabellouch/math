import Mathlib
import OAI.Computability.MaxCut.Machines.MachineBinaryParsing
import OAI.Computability.MaxCut.PCP.Folding
import OAI.Computability.MaxCut.Estimates.Vec
import OAI.Computability.MaxCut.Encoding.BitPairWeightQ

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

 theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

 theorem corrAverage_coordinate (t : ℝ) {n : ℕ} (i : Fin n) :
    corrAverage t n (fun x y => bitSign (x i) * bitSign (y i)) = t := by
  classical
  let s : Cube (Fin n) := fun j => decide (j = i)
  have hw (x : Cube (Fin n)) : walsh s x = bitSign (x i) := by
    have he (j : Fin n) : bitSign (s j && x j) = if j = i then bitSign (x i) else 1 := by
      by_cases h : j = i <;> simp [s, h, bitSign]
    simp only [walsh, he]
    simp
  have hd : Analytic.degree s = 1 := by
    have hs : univ.filter (fun j => s j = true) = {i} := by ext j; simp [s]
    rw [Analytic.degree, hs, card_singleton]
  simpa [hw, hd] using corrAverage_walsh t n s s

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

/-- The honest assignment is an actual Boolean cut (coordinate dictators). -/
def dictator (lx : X → Fin q) (x : X) (z : Cube (Fin q)) : ℝ := bitSign (z (lx x))

 theorem testCut_complete (G : Game X Y E q) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (lx : X → Fin q) (ly : Y → Fin q) :
    (1 + t) / 2 - 2 * (1 - G.satisfied lx ly) ≤ G.testCut t (dictator lx) := by
  classical
  let P (e e' : E) := corrAverage t q (fun z z' =>
      (1 - dictator lx (G.source e) (cubePerm (G.permutation e) z) *
        dictator lx (G.source e') (cubePerm (G.permutation e') (antipode z'))) / 2)
  let bad (y : Y) (e : E) : ℝ := if G.permutation e (lx (G.source e)) = ly y then 0 else 1
  have hP (e e' : E) : 0 ≤ P e e' := by
    have h := corrAverage_mono ht q (F := fun _ _ => 0)
      (G := fun z z' => (1 - dictator lx (G.source e) (cubePerm (G.permutation e) z) *
        dictator lx (G.source e') (cubePerm (G.permutation e') (antipode z'))) / 2)
      (fun z z' => by
        dsimp [dictator, cubePerm, antipode, bitSign]
        split_ifs <;> norm_num)
    simpa only [corrAverage_fst, Fintype.expect_const] using h
  have hgood (y : Y) (e e' : E)
      (he : G.permutation e (lx (G.source e)) = ly y)
      (he' : G.permutation e' (lx (G.source e')) = ly y) : P e e' = (1 + t) / 2 := by
    dsimp [P, dictator, cubePerm, antipode]
    simp only [he, he', bitSign_not, mul_neg, sub_neg_eq_add, div_eq_mul_inv,
      corrAverage_mul_const, corrAverage_add, corrAverage_fst, Fintype.expect_const,
      corrAverage_coordinate]
  have hp (y : Y) (e e' : E) : (1 + t) / 2 - bad y e - bad y e' ≤ P e e' := by
    by_cases he : G.permutation e (lx (G.source e)) = ly y
    · by_cases he' : G.permutation e' (lx (G.source e')) = ly y
      · simp only [bad, ite_eq_left he, ite_eq_left he', sub_zero, hgood y e e' he he', le_refl]
      · simp only [bad, ite_eq_left he, ite_eq_right he', sub_zero]
        linarith [hP e e', ht.2]
    · by_cases he' : G.permutation e' (lx (G.source e')) = ly y
      · simp only [bad, ite_eq_right he, ite_eq_left he', sub_zero]
        linarith [hP e e', ht.2]
      · simp only [bad, ite_eq_right he, ite_eq_right he']
        linarith [hP e e', ht.2]
  have hbad : G.rightLaw.avg (fun y => (G.edgeLaw y).avg (bad y)) = 1 - G.satisfied lx ly := by
    have hh (y : Y) (e : E) : bad y e = 1 -
      (if G.permutation e (lx (G.source e)) = ly y then (1 : ℝ) else 0) := by
      dsimp [bad]; split_ifs <;> norm_num
    change G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e => bad y e)) = _
    simp only [hh, Law.avg_sub, Law.avg_const, satisfied]
  rw [testCut_expanded]
  have h := G.rightLaw.avg_mono (fun y => (G.edgeLaw y).avg_mono (fun e =>
    (G.edgeLaw y).avg_mono (fun e' => hp y e e')))
  simp only [Law.avg_sub, Law.avg_const, hbad] at h
  dsimp only [P] at h
  linarith

end Game
end OptimalMaxCut.LongCode
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

/-- Exact aggregation of rational masses; all collisions are added, not
silently treated as different edges. -/
def push (p : Law I) (f : I → J) : Law J where
  weight j := ∑ i, if f i = j then p.weight i else 0
  nonneg j := sum_nonneg (fun i _ => by split_ifs; exact p.nonneg i; exact le_refl 0)
  total := by
    rw [sum_comm]
    simpa using p.total

 theorem push_average (p : Law I) (f : I → J) (g : J → ℝ) :
    (p.push f).avg g = p.avg (fun i => g (f i)) := by
  simp only [avg, push, Rat.cast_sum, apply_ite Rat.cast, Rat.cast_zero, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul]

end Law

/-- A general finite rational law of ordered test endpoints becomes an ordinary
symmetric rational graph by adding both orientations and deleting loops. -/
def aggregate {N : ℕ} (p : Law (Fin N × Fin N)) (u v : Fin N) : ℚ :=
  if u = v then 0 else p.weight (u,v) + p.weight (v,u)

 theorem aggregate_symm {N : ℕ} (p : Law (Fin N × Fin N)) (u v : Fin N) :
    aggregate p u v = aggregate p v u := by
  simp only [aggregate]
  by_cases h : u = v <;> simp [h, eq_comm, add_comm]

 theorem aggregate_nonneg {N : ℕ} (p : Law (Fin N × Fin N)) (u v : Fin N) :
    0 ≤ aggregate p u v := by
  unfold aggregate
  split_ifs
  · exact le_refl 0
  · exact add_nonneg (p.nonneg _) (p.nonneg _)

 theorem upper_triangle_symmetrize {N : ℕ} (a : Fin N → Fin N → ℝ) :
    (∑ u, ∑ v, if u < v then a u v + a v u else 0) =
      ∑ u, ∑ v, if u ≠ v then a u v else 0 := by
  have he (u v : Fin N) : (if u ≠ v then a u v else 0) =
      (if u < v then a u v else 0) + (if v < u then a u v else 0) := by
    rcases lt_trichotomy u v with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hs (u v : Fin N) : (if u < v then a u v + a v u else 0) =
      (if u < v then a u v else 0) + (if u < v then a v u else 0) := by
    split_ifs <;> ring
  conv_lhs => simp only [hs, sum_add_distrib]
  conv_rhs => simp only [he, sum_add_distrib]
  congr 1
  rw [sum_comm]

 theorem aggregate_cut {N : ℕ} (p : Law (Fin N × Fin N)) (σ : Fin N → Bool) :
    weightedCut (fun u v => (aggregate p u v : ℝ)) σ =
      p.avg (fun e => if σ e.1 ≠ σ e.2 then 1 else 0) := by
  have h (u v : Fin N) :
      (if u < v ∧ σ u ≠ σ v then (aggregate p u v : ℝ) else 0) =
      (if u < v then (if σ u ≠ σ v then (p.weight (u,v) : ℝ) else 0) +
        (if σ v ≠ σ u then (p.weight (v,u) : ℝ) else 0) else 0) := by
    by_cases hlt : u < v <;> by_cases hs : σ u = σ v <;>
      simp [aggregate, hlt, hs, eq_comm, ne_of_lt, Rat.cast_add]
  simp only [weightedCut, h, upper_triangle_symmetrize, Law.avg, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases huv : u = v <;> by_cases hs : σ u = σ v <;> simp [huv, hs]

 theorem aggregate_total {N : ℕ} (p : Law (Fin N × Fin N)) : totalWeight (aggregate p) ≤ 1 := by
  have he : ((totalWeight (aggregate p) : ℚ) : ℝ) =
      ∑ u, ∑ v, if u ≠ v then (p.weight (u,v) : ℝ) else 0 := by
    simp only [totalWeight, Rat.cast_sum, apply_ite Rat.cast, Rat.cast_zero]
    have hh (u v : Fin N) : (if u < v then (aggregate p u v : ℝ) else 0) =
        if u < v then (p.weight (u,v) : ℝ) + (p.weight (v,u) : ℝ) else 0 := by
      by_cases h : u < v
      · simp [h, aggregate, ne_of_lt h]
      · simp [h]
    simp only [hh, upper_triangle_symmetrize]
  have hle : (∑ u, ∑ v, if u ≠ v then (p.weight (u,v) : ℝ) else 0) ≤ 1 := by
    calc
      _ ≤ ∑ u, ∑ v, (p.weight (u,v) : ℝ) := by
        apply sum_le_sum; intro u _
        apply sum_le_sum; intro v _
        split_ifs
        · exact le_refl _
        · exact p.weight_nonneg _
      _ = 1 := by simpa only [Fintype.sum_prod_type] using p.total_real
  rw [← he] at hle
  exact_mod_cast hle

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}

/-- Fixed explicit vertex enumeration, supplied as a finite equivalence. The
semantic theorem does not hide an unweighted conversion or an edge multiset. -/
def edgeDistribution (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) : Law (Fin N × Fin N) :=
  (G.sampleLaw t ht).push (fun a => (enum (G.queries a).1, enum (G.queries a).2))

def weights (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) : Fin N → Fin N → ℚ :=
  aggregate (G.edgeDistribution t ht enum)

 theorem weightedCut_testCut (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (σ : Fin N → Bool) :
    weightedCut (fun u v => (G.weights t ht enum u v : ℝ)) σ =
      G.testCut t (fun x z => bitSign (σ (enum (x,z)))) := by
  rw [weights, aggregate_cut, edgeDistribution, Law.push_average, G.testCut_sampleLaw t ht]
  congr 1
  funext a
  cases h : σ (enum (G.queries a).1) <;> cases h' : σ (enum (G.queries a).2) <;>
    norm_num [bitSign, h, h']

 theorem weightedMax_complete (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (lx : X → Fin q) (ly : Y → Fin q) :
    (1 + (t : ℝ)) / 2 - 2 * (1 - G.satisfied lx ly) ≤
      weightedMax (fun u v => (G.weights t ht enum u v : ℝ)) := by
  let σ : Fin N → Bool := fun u => (enum.symm u).2 (lx (enum.symm u).1)
  have ht' : (t : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
  have h := G.testCut_complete (t : ℝ) ht' lx ly
  have he : (fun x z => bitSign (σ (enum (x,z)))) = dictator lx := by
    funext x z; simp [σ, dictator]
  rw [← he, ← G.weightedCut_testCut t ht enum σ] at h
  exact h.trans (weightedCut_le_max _ _)

 theorem exists_weighted_soundness (t : ℚ) (ht : 0 < t) (ht1 : t < 1) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]
      {q N : ℕ} (_hq : 0 < q) (G : Game X Y E q)
      (enum : X × Cube (Fin q) ≃ Fin N), G.Sound δ →
      weightedMax (fun u v => (G.weights t ⟨by linarith, ht1.le⟩ enum u v : ℝ)) ≤
        (1 + 2 / Real.pi * Real.arcsin t) / 2 + ξ := by
  obtain ⟨δ, hδ, hbound⟩ := exists_test_soundness (t : ℝ) ξ
    (by exact_mod_cast ht) (by exact_mod_cast ht1) hξ
  refine ⟨δ, hδ, ?_⟩
  intro X Y E _ _ _ q N hq G enum hsound
  obtain ⟨σ, hσ⟩ := weightedMax_attained (fun u v => (G.weights t ⟨by linarith, ht1.le⟩ enum u v : ℝ))
  have hm : t ∈ Set.Icc (-1 : ℚ) 1 := ⟨by linarith, ht1.le⟩
  have hb := hbound q hq G hsound (fun x z => bitSign (σ (enum (x,z)))) (by
    intro x z
    cases σ (enum (x,z)) <;> norm_num [bitSign])
  exact hσ.symm.trans_le ((G.weightedCut_testCut t hm enum σ).trans_le hb)

end Game
end OptimalMaxCut.LongCode
namespace OptimalMaxCut.LongCode.Game
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted
variable {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}

/-- The actual simple, unweighted output. Its common integer scale is printed;
loops and both orientations have already been handled by exact aggregation. -/
def output (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (K : ℕ) : ScaledGraph :=
  deterministicOutput K (G.weights t ht enum) (aggregate_symm _)

 theorem output_error (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (K : ℕ) (hK : 0 < K) :
    |((G.output t ht enum K).graph.maxCut : ℝ) / (G.output t ht enum K).scale -
      weightedMax (fun u v => (G.weights t ht enum u v : ℝ))| ≤ 2 / K :=
  deterministicOutput_error K hK _ (aggregate_symm _)
    (fun u v _ => aggregate_nonneg _ u v) (aggregate_total _)

 theorem output_complete (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (K : ℕ) (hK : 0 < K)
    (lx : X → Fin q) (ly : Y → Fin q) :
    (1 + (t : ℝ)) / 2 - 2 * (1 - G.satisfied lx ly) - 2 / K ≤
      ((G.output t ht enum K).graph.maxCut : ℝ) / (G.output t ht enum K).scale := by
  have h := abs_le.mp (G.output_error t ht enum K hK)
  have hc := G.weightedMax_complete t ht enum lx ly
  linarith

 theorem output_vertex_bound (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (K : ℕ) :
    (G.output t ht enum K).graph.vertices ≤ N * (2 * (K * (N + 1) ^ 2 + 1)) ^ 6 :=
  deterministicOutput_vertex_bound _ _ _

/-- All constants for the Max-Cut gap, and the fixed deterministic graph
transformation, are selected before the input game. This is the semantic
component, not the still-required machine-level reduction certificate. -/
 theorem exists_unweighted_gap_parameters (α : ℝ) (hα : alphaGW < α) (hα1 : α ≤ 1) :
    ∃ (t ε y n : ℚ) (δ : ℝ) (K : ℕ) (ht : t ∈ Set.Icc (-1 : ℚ) 1),
      0 < t ∧ t < 1 ∧ 0 < ε ∧ (ε : ℝ) < 1 / 2 ∧ 0 < δ ∧ δ < 1 / 2 ∧
      0 < K ∧ 0 < y ∧ 0 ≤ n ∧ (n : ℝ) < α * (y : ℝ) ∧
      (∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]
        {q N : ℕ} (G : Game X Y E q) (enum : X × Cube (Fin q) ≃ Fin N),
        (∃ lx ly, 1 - (ε : ℝ) ≤ G.satisfied lx ly) →
          (y : ℝ) ≤ ((G.output t ht enum K).graph.maxCut : ℝ) / (G.output t ht enum K).scale) ∧
      (∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]
        {q N : ℕ} (_hq : 0 < q) (G : Game X Y E q) (enum : X × Cube (Fin q) ≃ Fin N),
        G.Sound δ → ((G.output t ht enum K).graph.maxCut : ℝ) / (G.output t ht enum K).scale ≤ (n : ℝ)) := by
  obtain ⟨t, η, y, n, ht0, ht1, hη, hηb, hy, hypos, hn, hnlo, hgap⟩ :=
    exists_main_gap_parameters α hα hα1
  have hηr : 0 < (η : ℝ) := by exact_mod_cast hη
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht0
  have htR1 : (t : ℝ) < 1 := by exact_mod_cast ht1
  have hb : 0 ≤ borellCurve t := by
    exact mul_nonneg (by positivity) (Real.arcsin_nonneg.mpr htR.le)
  have hηsmall : (η : ℝ) < 1 / 4 := by linarith
  obtain ⟨δ, hδ, hsound⟩ := exists_weighted_soundness t ht0 ht1 (η : ℝ) hηr
  obtain ⟨K, hlarge⟩ := exists_nat_gt (max (2 / (η : ℝ)) 0)
  have hKr : (0 : ℝ) < K := (le_max_right _ _).trans_lt hlarge
  have hK : 0 < K := by exact_mod_cast hKr
  have hsmall : 2 / (K : ℝ) ≤ (η : ℝ) := by
    have hh : 2 / (η : ℝ) < (K : ℝ) := (le_max_left _ _).trans_lt hlarge
    have hm := (div_lt_iff₀ hηr).mp hh
    apply (div_le_iff₀ hKr).mpr
    nlinarith
  let ht : t ∈ Set.Icc (-1 : ℚ) 1 := ⟨by linarith, ht1.le⟩
  refine ⟨t, η / 4, y, n, min δ (1 / 4), K, ht, ht0, ht1,
    by positivity, ?_, lt_min hδ (by norm_num), ?_, hK, hypos, hn, hgap, ?_, ?_⟩
  · push_cast; linarith
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · intro X Y E _ _ _ q N G enum hyes
    obtain ⟨lx, ly, hsat⟩ := hyes
    have hc := G.output_complete t ht enum K hK lx ly
    have hyR : (y : ℝ) = (1 + (t : ℝ)) / 2 - 2 * (η : ℝ) := by exact_mod_cast hy
    push_cast at hsat
    linarith
  · intro X Y E _ _ _ q N hq G enum hs
    have hs' : G.Sound δ := fun lx ly => (hs lx ly).trans (min_le_left _ _)
    have h := hsound hq G enum hs'
    have he := abs_le.mp (G.output_error t ht enum K hK)
    change (1 + 2 / Real.pi * Real.arcsin (t : ℝ)) / 2 + 2 * (η : ℝ) < (n : ℝ) at hnlo
    linarith

end OptimalMaxCut.LongCode.Game

namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset
namespace Law
attribute [local instance] Classical.propDecidable
variable {E Y : Type} [Fintype E] [Fintype Y] [Nonempty E]
noncomputable def fiberSize (r : E → Y) (y : Y) : ℕ := by
  classical
  exact (univ.filter (fun e => r e = y)).card

omit [Fintype Y] [Nonempty E] in
 theorem fiberSize_eq_sum (r : E → Y) (y : Y) :
    fiberSize r y = ∑ e, if r e = y then 1 else 0 := by
  classical
  simp only [fiberSize, Finset.card_filter]

omit [Nonempty E] in
 theorem sum_fiberSize (r : E → Y) : ∑ y, fiberSize r y = Fintype.card E := by
  classical
  simp_rw [fiberSize_eq_sum]
  rw [sum_comm]
  simp

omit [Fintype Y] [Nonempty E] in
 theorem fiberSize_pos (r : E → Y) (e : E) : 0 < fiberSize r (r e) := by
  classical
  exact card_pos.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩

noncomputable def fiberMarginal (r : E → Y) : Law Y where
  weight y := fiberSize r y / (Fintype.card E : ℚ)
  nonneg y := by positivity
  total := by
    rw [← sum_div, ← Nat.cast_sum, sum_fiberSize]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero)

noncomputable def fiberConditional (r : E → Y) (y : Y) : Law E := by
  classical
  exact {
    weight e := if fiberSize r y = 0 then 1 / (Fintype.card E : ℚ)
      else if r e = y then 1 / (fiberSize r y : ℚ) else 0
    nonneg e := by split_ifs <;> positivity
    total := by
      by_cases h : fiberSize r y = 0
      · simp [h, div_eq_mul_inv]
      · simp only [h, ↓reduceIte]
        rw [← sum_filter]
        simp only [sum_const, nsmul_eq_mul]
        change (fiberSize r y : ℚ) * (1 / (fiberSize r y : ℚ)) = 1
        exact mul_one_div_cancel (by exact_mod_cast h) }

 theorem fiber_joint (r : E → Y) (y : Y) (e : E) :
    (fiberMarginal r).weight y * (fiberConditional r y).weight e =
      if r e = y then 1 / (Fintype.card E : ℚ) else 0 := by
  classical
  dsimp [fiberMarginal, fiberConditional]
  by_cases h : fiberSize r y = 0
  · have hx : r e ≠ y := by
      intro he
      have hp := fiberSize_pos r e
      rw [he, h] at hp
      omega
    simp [h, hx]
  · have hr : (fiberSize r y : ℚ) ≠ 0 := by exact_mod_cast h
    split_ifs <;> field_simp ; simp_all

 theorem fiber_average (r : E → Y) (f : Y → E → ℝ) :
    (fiberMarginal r).avg (fun y => (fiberConditional r y).avg (f y)) =
      (∑ e, f (r e) e) / Fintype.card E := by
  classical
  simp only [avg, mul_sum, ← mul_assoc, ← Rat.cast_mul, fiber_joint]
  rw [sum_comm]
  simp only [apply_ite (fun z : ℚ => (z : ℝ)), Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast, Rat.cast_zero, ite_mul, zero_mul]
  simp only [sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← mul_sum]
  ring
end Law
end OptimalMaxCut.LongCode

namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target
open MaxCutGames.Explicit.MachineOutputContract
attribute [local instance] Classical.propDecidable

variable {q : ℕ}
noncomputable def ofInstance (g : Instance q) :
    Game (Fin g.vertices) (Fin g.vertices) (Fin g.constraints.length) q := by
  letI : Nonempty (Fin g.constraints.length) := Fin.pos_iff_nonempty.mp g.constraintCount_positive
  exact {
    rightLaw := Law.fiberMarginal (fun e : Fin g.constraints.length => g.constraints[e].target)
    edgeLaw := Law.fiberConditional (fun e : Fin g.constraints.length => g.constraints[e].target)
    source e := g.constraints[e].source
    permutation e := permutationEquiv g.constraints[e].permutation }

 theorem satisfaction_formula (g : Instance q) (lx ly : Fin g.vertices → Fin q) :
    (ofInstance g).satisfied lx ly =
      (∑ e : Fin g.constraints.length,
        if g.constraints[e].permutation.images[lx g.constraints[e].source] =
          ly g.constraints[e].target then (1 : ℝ) else 0) / g.constraints.length := by
  let : Nonempty (Fin g.constraints.length) := Fin.pos_iff_nonempty.mp g.constraintCount_positive
  unfold Game.satisfied ofInstance
  rw [Law.fiber_average]
  simp only [Fintype.card_fin, permutationEquiv, Equiv.coe_fn_mk]
  congr 1

/-- Occurrences retain their list identity: no parallel edge or denominator is
silently discarded in the adapter. -/
 theorem count_as_sum {n : ℕ} (cs : List (Constraint n q)) (l : Fin n → Fin q) :
    (countSatisfied l cs : ℝ) =
      ∑ e : Fin cs.length, if cs[e].permutation.images[l cs[e].source] =
        l cs[e].target then (1 : ℝ) else 0 := by
  induction cs with
  | nil => simp [countSatisfied]
  | cons c cs ih =>
    simp only [List.length_cons, Fin.sum_univ_succ]
    simp only [countSatisfied, Nat.cast_add, ih, Constraint.satisfied,

      ]
    congr 1
    split_ifs <;> simp_all

 theorem satisfaction_diagonal (g : Instance q) (l : Fin g.vertices → Fin q) :
    (ofInstance g).satisfied l l = (countSatisfied l g.constraints : ℝ) / g.constraints.length := by
  rw [satisfaction_formula, count_as_sum]

noncomputable def merge (g : Instance q) (b : SimpleBipartite g)
    (lx ly : Fin g.vertices → Fin q) : Fin g.vertices → Fin q :=
  fun v => if b.side v then ly v else lx v

 theorem satisfaction_merge (g : Instance q) (b : SimpleBipartite g)
    (lx ly : Fin g.vertices → Fin q) :
    (ofInstance g).satisfied lx ly =
      (countSatisfied (merge g b lx ly) g.constraints : ℝ) / g.constraints.length := by
  rw [satisfaction_formula, count_as_sum]
  congr 1
  apply sum_congr rfl
  intro e _
  simp only [merge, b.sourceSide, b.targetSide, Bool.false_eq_true, ↓reduceIte]

 theorem complete (g : Instance q) (ε : ℝ)
    (h : ∃ l, 1 - ε ≤ (countSatisfied l g.constraints : ℝ) / g.constraints.length) :
    ∃ lx ly, 1 - ε ≤ (ofInstance g).satisfied lx ly := by
  obtain ⟨l, hl⟩ := h
  exact ⟨l, l, (satisfaction_diagonal g l).symm ▸ hl⟩

 theorem sound (g : Instance q) (b : SimpleBipartite g) (δ : ℝ)
    (h : ∀ l, (countSatisfied l g.constraints : ℝ) / g.constraints.length ≤ δ) :
    (ofInstance g).Sound δ := by
  intro lx ly
  rw [satisfaction_merge g b lx ly]
  exact h _
end OptimalMaxCut.LongCode.InstanceAdapter

end

end OAI
