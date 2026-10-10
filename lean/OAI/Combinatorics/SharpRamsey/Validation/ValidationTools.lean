import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestLearningIncidence
import OAI.Combinatorics.SharpRamsey.Learning.PreparedProposals

namespace OAI

section
namespace SharpLogRamsey.FiniteSamplingBounds
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Ω : Type*} [Fintype Ω]

noncomputable def rowWeight (w : Ω → ℝ) {h : ℕ} (z : Fin h → Ω) : ℝ := ∏ i, w (z i)
noncomputable def hitCount (E : Finset Ω) {h : ℕ} (z : Fin h → Ω) : ℕ :=
  (univ.filter (fun i => z i ∈ E)).card
omit [Fintype Ω] in
lemma rowWeight_nonneg (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) {h : ℕ} (z : Fin h → Ω) :
    0 ≤ rowWeight w z := Finset.prod_nonneg (fun i _ => hw (z i))

lemma rowWeight_total (w : Ω → ℝ) (hw : ∑ x, w x = 1) (h : ℕ) :
    ∑ z : Fin h → Ω, rowWeight w z = 1 := by
  unfold rowWeight
  rw [← Fintype.prod_sum]
  simp [hw]

lemma rowMoment (w : Ω → ℝ) (ht : ∑ x, w x = 1) (E : Finset Ω) (h : ℕ) (b : ℝ) :
    (∑ z : Fin h → Ω, rowWeight w z*b^(hitCount E z)) =
      (1+(b-1)*(∑ x ∈ E, w x))^h := by
  classical
  have hi (z : Fin h → Ω) : b^(hitCount E z) = ∏ i, if z i ∈ E then b else 1 := by
    simp [hitCount, ← Finset.prod_filter]
  simp_rw [hi, rowWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin h) (x : Ω) => w x*(if x ∈ E then b else 1))]
  have he : (∑ x : Ω, w x*(if x ∈ E then b else 1)) = 1+(b-1)*(∑ x ∈ E, w x) := by
    have hi (x : Ω) : w x*(if x ∈ E then b else 1) = w x+(b-1)*(if x ∈ E then w x else 0) := by
      split_ifs <;> ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ht]
    simp
  rw [he]
  simp

noncomputable def rowLower (w : Ω → ℝ) (E : Finset Ω) (h T : ℕ) : ℝ :=
  ∑ z : Fin h → Ω, if hitCount E z < T then rowWeight w z else 0

lemma rowLower_moment (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (E : Finset Ω) (h T : ℕ) :
    (1/2:ℝ)^T*rowLower w E h T ≤ (1-(∑ x ∈ E, w x)/2)^h := by
  have he : 1-(∑ x ∈ E, w x)/2 = 1+((1/2:ℝ)-1)*(∑ x ∈ E, w x) := by ring
  rw [he, ← rowMoment w ht E h (1/2), rowLower, mul_sum]
  apply sum_le_sum
  intro z _
  split_ifs with hz
  · rw [mul_comm ((1/2:ℝ)^T)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) hz.le)
      (rowWeight_nonneg w hw z)
  · simp only [mul_zero]
    exact mul_nonneg (rowWeight_nonneg w hw z) (by positivity)

theorem rowLower_exp (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (E : Finset Ω) (h T : ℕ) :
    rowLower w E h T ≤ Real.exp ((T:ℝ)-(h:ℝ)*(∑ x ∈ E, w x)/2) := by
  have hs : (∑ x ∈ E, w x) ≤ 1 := by
    rw [← ht]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ E) (by intros; exact hw _)
  have hpow : (1-(∑ x ∈ E, w x)/2)^h ≤ Real.exp (-(h:ℝ)*(∑ x ∈ E, w x)/2) := by
    rw [show -(h:ℝ)*(∑ x ∈ E, w x)/2 = (h:ℝ)*(-(∑ x ∈ E, w x)/2) by ring,
      Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by linarith)
    simpa only [neg_div] using Real.one_sub_le_exp_neg ((∑ x ∈ E, w x)/2)
  have hmult := mul_le_mul_of_nonneg_left ((rowLower_moment w hw ht E h T).trans hpow)
    (show (0:ℝ) ≤ 2^T by positivity)
  have hcancel : (2:ℝ)^T*((1/2:ℝ)^T*rowLower w E h T) = rowLower w E h T := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [hcancel] at hmult
  have htwo : (2:ℝ)^T ≤ Real.exp (T:ℝ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
      (show (2:ℝ) ≤ Real.exp 1 by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1) T
    simpa [← Real.exp_nat_mul] using hh
  calc
    _ ≤ (2:ℝ)^T*Real.exp (-(h:ℝ)*(∑ x ∈ E, w x)/2) := hmult
    _ ≤ Real.exp (T:ℝ)*Real.exp (-(h:ℝ)*(∑ x ∈ E, w x)/2) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem rowLower_highRank (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (ht : ∑ x, w x = 1)
    (E : Finset Ω) (h T : ℕ) (q : ℝ) (hq : 0 < q)
    (hE : 2/(5*q) ≤ ∑ x ∈ E, w x) (hT : (T:ℝ) ≤ (h:ℝ)/(10*q)+1) :
    rowLower w E h T ≤ Real.exp (1-(h:ℝ)/(10*q)) := by
  apply (rowLower_exp w hw ht E h T).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ (h:ℝ)/2 by positivity)
  have he : ((h:ℝ)/2)*(2/(5*q)) = 2*((h:ℝ)/(10*q)) := by field_simp; ring
  rw [he] at hh
  nlinarith

end
end SharpLogRamsey.FiniteSamplingBounds

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

def uniformMass (X : Finset Ω) (x : Ω) : ℝ := if x ∈ X then (X.card : ℝ)⁻¹ else 0

omit [Fintype Ω] in
lemma uniform_nonneg (X : Finset Ω) (x : Ω) : 0 ≤ uniformMass X x := by
  unfold uniformMass
  split_ifs <;> positivity

lemma uniform_total {X : Finset Ω} (hX : X.Nonempty) : ∑ x, uniformMass X x = 1 := by
  have hx : (X.card:ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hX).ne'
  simp [uniformMass,hx]

omit [Fintype Ω] in
lemma uniform_sum (X E : Finset Ω) :
    (∑ x ∈ E, uniformMass X x) = ((E ∩ X).card : ℝ)/(X.card:ℝ) := by
  simp [uniformMass, div_eq_mul_inv, ← filter_mem_eq_inter]

lemma coordinate_mean (w : Ω → ℝ) (ht : ∑ x, w x=1)
    {h : ℕ} (i : Fin h) (f : Ω → ℝ) :
    (∑ z : Fin h → Ω, rowWeight w z*f (z i)) = ∑ x, w x*f x := by
  have hi (z : Fin h → Ω) : rowWeight w z*f (z i) =
      ∏ j, w (z j)*(if j=i then f (z j) else 1) := by
    rw [prod_mul_distrib]
    simp [rowWeight]
  simp_rw [hi]
  rw [← Fintype.prod_sum (fun j x => w x*(if j=i then f x else 1))]
  have he (j : Fin h) : (∑ x, w x*(if j=i then f x else 1)) =
      if j=i then ∑ x, w x*f x else 1 := by
    split_ifs <;> simp_all
  simp_rw [he]
  simp

omit [Fintype Ω] in
lemma hitCount_real {h : ℕ} (E : Finset Ω) (z : Fin h → Ω) :
    (hitCount E z:ℝ) = ∑ i, if z i ∈ E then (1:ℝ) else 0 := by
  simp [hitCount, ← sum_boole]

lemma hitCount_mean (w : Ω → ℝ) (ht : ∑ x, w x=1) (E : Finset Ω) (h : ℕ) :
    (∑ z : Fin h → Ω, rowWeight w z*(hitCount E z:ℝ)) = (h:ℝ)*(∑ x ∈ E, w x) := by
  simp_rw [hitCount_real, mul_sum]
  rw [sum_comm]
  have hi (i : Fin h) : (∑ z : Fin h → Ω,
      if z i∈E then rowWeight w z else 0) = ∑ x∈E,w x := by
    simpa only [mul_ite, mul_one, mul_zero, ← sum_filter, filter_mem_eq_inter,
      univ_inter] using coordinate_mean w ht i (fun x => if x∈E then (1:ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero]
  simp_rw [hi]
  simp [mul_sum]

def pass (R : Ω → Y → Prop) (q : ℝ) {h : ℕ} (z : Fin h → Ω) (y : Y) : Prop :=
  (hitCount (univ.filter (fun x => R x y)) z:ℝ) < (h:ℝ)/(5*q)

def cap (R : Ω → Y → Prop) (q : ℝ) (U : Finset Y) {h : ℕ} (z : Fin h → Ω) : Finset Y :=
  U.filter (pass R q z)

omit [Fintype Y] in

theorem pointwise_exclusion (w : Ω → ℝ) (hw : ∀ x, 0≤w x) (ht : ∑ x, w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (h : ℕ) (hh : 0<h) (y : Y) :
    (∑ z : Fin h → Ω, if ¬pass R q z y then rowWeight w z else 0) ≤
      5*q*(∑ x ∈ univ.filter (fun x => R x y), w x) := by
  let E := univ.filter (fun x => R x y)
  have hm : (h:ℝ)/(5*q)*(∑ z : Fin h → Ω,
      if ¬pass R q z y then rowWeight w z else 0) ≤ (h:ℝ)*(∑ x ∈ E, w x) := by
    rw [←hitCount_mean w ht E h, mul_sum]
    apply sum_le_sum
    intro z _
    by_cases hz : pass R q z y
    · simp only [hz, not_true_eq_false, ite_false, mul_zero]
      exact mul_nonneg (rowWeight_nonneg w hw z) (Nat.cast_nonneg _)
    · simp only [hz, not_false_eq_true, ite_true]
      have hz' : (h:ℝ)/(5*q) ≤ (hitCount E z:ℝ) := le_of_not_gt hz
      nlinarith [mul_le_mul_of_nonneg_right hz' (rowWeight_nonneg w hw z)]
  have hc : 0<(h:ℝ) := by exact_mod_cast hh
  apply (mul_le_mul_iff_right₀ hc).mp
  have hm' := mul_le_mul_of_nonneg_right hm (show 0≤5*q by positivity)
  dsimp [E] at hm'
  convert hm' using 1 <;> field_simp

omit [Fintype Y] in

theorem pointwise_pass (w : Ω → ℝ) (hw : ∀ x, 0≤w x) (ht : ∑ x, w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (h : ℕ) (y : Y)
    (hy : 1/(2*q) ≤ ∑ x ∈ univ.filter (fun x => R x y), w x) :
    (∑ z : Fin h → Ω, if pass R q z y then rowWeight w z else 0) ≤
      Real.exp (1-(h:ℝ)/(20*q)) := by
  let E := univ.filter (fun x => R x y)
  let T := ⌈(h:ℝ)/(5*q)⌉₊
  have ht' : (T:ℝ) ≤ (h:ℝ)/(5*q)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hpt : (∑ z : Fin h → Ω, if pass R q z y then rowWeight w z else 0) ≤
      rowLower w E h T := by
    apply sum_le_sum
    intro z _
    by_cases hz : pass R q z y
    · have hc : hitCount E z < T := by
        apply Nat.lt_ceil.mpr
        exact hz
      simp only [hz, ite_true, hc, le_refl]
    · simp only [hz, ite_false]
      split_ifs <;> simp [rowWeight_nonneg w hw z]
  apply hpt.trans ((rowLower_exp w hw ht E h T).trans ?_)
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hy (show 0≤(h:ℝ)/2 by positivity)
  have he : (h:ℝ)/2*(1/(2*q)) = (h:ℝ)/(4*q) := by ring
  rw [he] at hm
  have hm' : (h:ℝ)/(4*q) ≤ ((h:ℝ)*(∑ x∈E,w x))/2 := by
    exact hm.trans_eq (by dsimp [E]; ring)
  calc
    _ ≤ (h:ℝ)/(5*q)+1-(h:ℝ)/(4*q) := sub_le_sub ht' hm'
    _ = _ := by ring

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

def prob (w : Ω → ℝ) (h : ℕ) (P : (Fin h → Ω) → Prop) : ℝ :=
  ∑ z : Fin h → Ω, if P z then rowWeight w z else 0

lemma prob_nonneg (w : Ω → ℝ) (hw : ∀ x, 0≤w x) {h : ℕ}
    (P : (Fin h → Ω) → Prop) : 0 ≤ prob w h P := by
  apply sum_nonneg
  intro z _
  split_ifs <;> simp [rowWeight_nonneg w hw z]

lemma prob_le_one (w : Ω → ℝ) (hw : ∀ x, 0≤w x) (ht : ∑ x,w x=1) {h : ℕ}
    (P : (Fin h → Ω) → Prop) : prob w h P ≤ 1 := by
  rw [←rowWeight_total w ht h]
  apply sum_le_sum
  intro z _
  split_ifs <;> simp [rowWeight_nonneg w hw z]

omit [Fintype Y] in
lemma cardinal_mean (w : Ω → ℝ) {h : ℕ} (U : Finset Y)
    (P : (Fin h → Ω) → Y → Prop) :
    (∑ z : Fin h → Ω, rowWeight w z*((U.filter (P z)).card:ℝ)) =
      ∑ y∈U, prob w h (fun z => P z y) := by
  have he (z : Fin h → Ω) : ((U.filter (P z)).card:ℝ) =
      ∑ y∈U, if P z y then (1:ℝ) else 0 := by simp
  simp_rw [he,mul_sum,mul_ite,mul_one,mul_zero]
  rw [sum_comm]
  rfl

lemma markov (w : Ω → ℝ) (hw : ∀ x,0≤w x) {h : ℕ}
    (f : (Fin h → Ω) → ℝ) (hf : ∀ z,0≤f z) (M : ℝ) (hM : 0<M) :
    prob w h (fun z => M<f z) ≤ (∑ z, rowWeight w z*f z)/M := by
  apply (le_div_iff₀ hM).mpr
  rw [prob,sum_mul]
  apply sum_le_sum
  intro z _
  split_ifs with hz
  · exact mul_le_mul_of_nonneg_left hz.le (rowWeight_nonneg w hw z)
  · simpa using mul_nonneg (rowWeight_nonneg w hw z) (hf z)

omit [Fintype Y] in

theorem cap_mean_le (w : Ω → ℝ) (hw : ∀ x,0≤w x) (ht : ∑ x,w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (h : ℕ) (U : Finset Y) :
    (∑ z : Fin h → Ω, rowWeight w z*((cap R q U z).card:ℝ)) ≤
      ((U.filter (fun y => (∑ x∈univ.filter (fun x => R x y),w x)<1/(2*q))).card:ℝ)
        +(U.card:ℝ)*Real.exp (1-(h:ℝ)/(20*q)) := by
  simp only [cap]
  rw [cardinal_mean w U (fun z y => pass R q z y)]
  let B := U.filter (fun y => (∑ x∈univ.filter (fun x => R x y),w x)<1/(2*q))
  calc
    _ ≤ ∑ y∈U, ((if y∈B then (1:ℝ) else 0)+Real.exp (1-(h:ℝ)/(20*q))) := by
      apply sum_le_sum
      intro y hy
      by_cases hb : y∈B
      · simp only [hb,ite_true]
        exact (prob_le_one w hw ht _).trans (by linarith [Real.exp_pos (1-(h:ℝ)/(20*q))])
      · simp only [hb,ite_false,zero_add]
        apply pointwise_pass w hw ht R q hq h y
        exact le_of_not_gt (fun hh => hb (mem_filter.mpr ⟨hy,hh⟩))
    _ = _ := by
      rw [sum_add_distrib]
      simp only [sum_boole, sum_const, nsmul_eq_mul]
      congr 2
      have he : U.filter (fun y => y∈B) = B := filter_mem_eq_inter.trans (inter_eq_right.mpr (filter_subset _ _))
      rw [he]

omit [Fintype Y] in

theorem loss_mean_le (w : Ω → ℝ) (hw : ∀ x,0≤w x) (ht : ∑ x,w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (hq : 0<q) (h : ℕ) (hh : 0<h) (T : Finset Y) :
    (∑ z : Fin h → Ω, rowWeight w z*((T.filter (fun y => ¬pass R q z y)).card:ℝ)) ≤
      5*q*(∑ y∈T,∑ x∈univ.filter (fun x => R x y),w x) := by
  calc
    _ = ∑ y∈T,prob w h (fun z => ¬pass R q z y) := by
      have he (z : Fin h → Ω) : ((T.filter (fun y => ¬pass R q z y)).card:ℝ) =
          ∑ y∈T, if ¬pass R q z y then (1:ℝ) else 0 := by simp only [sum_boole]
      simp_rw [he,mul_sum,mul_ite,mul_one,mul_zero]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      unfold prob
      apply sum_congr rfl
      intro z _
      split_ifs <;> simp_all
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro y _
      have he := pointwise_exclusion w hw ht R q hq h hh y
      apply le_trans (le_of_eq ?_) he
      unfold prob
      apply sum_congr rfl
      intro z _
      split_ifs <;> simp_all

omit [Fintype Y] in

theorem acceptance_mass (w : Ω → ℝ) (hw : ∀ x,0≤w x) (ht : ∑ x,w x=1)
    (R : Ω → Y → Prop) (q : ℝ) (h : ℕ) (U T : Finset Y)
    (M : ℝ) (hM : 0<M) (hT : T.Nonempty)
    (hs : (∑ z : Fin h → Ω,rowWeight w z*((cap R q U z).card:ℝ)) ≤ M/20)
    (hl : (∑ z : Fin h → Ω,rowWeight w z*
      ((T.filter (fun y => ¬pass R q z y)).card:ℝ)) ≤ (T.card:ℝ)/2000) :
    (9/10:ℝ) ≤ prob w h (fun z => ((cap R q U z).card:ℝ)≤M ∧
      ((T.filter (fun y => ¬pass R q z y)).card:ℝ)≤(T.card:ℝ)/100) := by
  let sz (z : Fin h → Ω) : ℝ := (cap R q U z).card
  let ls (z : Fin h → Ω) : ℝ := (T.filter (fun y => ¬pass R q z y)).card
  let A (z : Fin h → Ω) : Prop := sz z≤M ∧ ls z≤(T.card:ℝ)/100
  have htpos : 0<(T.card:ℝ) := by exact_mod_cast card_pos.mpr hT
  have hbS : prob w h (fun z => M<sz z) ≤ (1/20:ℝ) := by
    apply (markov w hw sz (fun z => Nat.cast_nonneg _) M hM).trans
    exact (div_le_iff₀ hM).mpr (by simpa [sz,div_eq_mul_inv,mul_comm] using hs)
  have hbL : prob w h (fun z => (T.card:ℝ)/100<ls z) ≤ (1/20:ℝ) := by
    apply (markov w hw ls (fun z => Nat.cast_nonneg _) _ (by positivity)).trans
    apply (div_le_iff₀ (show 0<(T.card:ℝ)/100 by positivity)).mpr
    exact hl.trans_eq (by ring)
  have hc : 1≤prob w h A+prob w h (fun z => M<sz z)+
      prob w h (fun z => (T.card:ℝ)/100<ls z) := by
    rw [←rowWeight_total w ht h,prob,prob,prob,←sum_add_distrib,←sum_add_distrib]
    apply sum_le_sum
    intro z _
    have hz := rowWeight_nonneg w hw z
    simp only [←not_le]
    by_cases hs' : sz z≤M <;> by_cases hl' : ls z≤(T.card:ℝ)/100 <;>
      simp_all [A]
    all_goals positivity
  change (9/10:ℝ) ≤ prob w h A
  linarith

end
end SharpLogRamsey.Validation

namespace SharpLogRamsey.Validation
open Finset
open scoped BigOperators Classical
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {Ω Y : Type*} [Fintype Ω]

def rowLaw (X : Finset Ω) (hX : X.Nonempty) (h : ℕ) : PublicTables.Law (Fin h → Ω) where
  mass := rowWeight (uniformMass X)
  nonneg := rowWeight_nonneg (uniformMass X) (uniform_nonneg X)
  total := rowWeight_total (uniformMass X) (uniform_total hX) h

def allIn (X : Finset Ω) {h : ℕ} (z : Fin h → Ω) : Prop := ∀ i,z i∈X

omit [Fintype Ω] in

theorem contained_row_scaling (X W : Finset Ω) (hX : X.Nonempty) (hsub : X⊆W)
    {h : ℕ} (z : Fin h → Ω) :
    (if allIn X z then rowWeight (uniformMass W) z else 0) =
      ((X.card:ℝ)/(W.card:ℝ))^h * rowWeight (uniformMass X) z := by
  have hx : (X.card:ℝ)≠0 := by exact_mod_cast (card_pos.mpr hX).ne'
  by_cases hz : allIn X z
  · simp only [hz,ite_true]
    have hi (i : Fin h) : uniformMass W (z i)=(W.card:ℝ)⁻¹ := by
      simp [uniformMass,hsub (hz i)]
    have hj (i : Fin h) : uniformMass X (z i)=(X.card:ℝ)⁻¹ := by
      simp [uniformMass,hz i]
    simp only [rowWeight,hi,hj,prod_const,card_univ,Fintype.card_fin]
    rw [←mul_pow]
    congr 1
    field_simp
  · simp only [hz,ite_false]
    have hn : ∃ i,z i∉X := by simpa only [allIn,not_forall] using hz
    obtain ⟨i,hi⟩ := hn
    have he : rowWeight (uniformMass X) z=0 := by
      apply prod_eq_zero (mem_univ i)
      simp [uniformMass,hi]
    rw [he,mul_zero]

def implementAccept (X : Finset Ω) {h : ℕ}
    (Good : (Fin h → Ω) → Prop) (z : Fin h → Ω) : Prop := allIn X z ∧ Good z

theorem accepted_scaling (X W : Finset Ω) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (h : ℕ) (Good : (Fin h → Ω) → Prop) (f : (Fin h → Ω) → ℝ) :
    PublicTables.accepted (rowLaw W hW h) (implementAccept X Good) f =
      ((X.card:ℝ)/(W.card:ℝ))^h *
        (∑ z : Fin h → Ω, if Good z then rowWeight (uniformMass X) z*f z else 0) := by
  rw [PublicTables.accepted,mul_sum]
  apply sum_congr rfl
  intro z _
  simp only [implementAccept,rowLaw]
  by_cases hg : Good z
  · simp only [hg,and_true,ite_true]
    rw [show (if allIn X z then rowWeight (uniformMass W) z*f z else 0) =
      (if allIn X z then rowWeight (uniformMass W) z else 0)*f z by
        split_ifs <;> ring,contained_row_scaling X W hX hsub]
    ring
  · simp [hg]

theorem proposal_acceptance (X W : Finset Ω) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (h : ℕ) (Good : (Fin h → Ω) → Prop) :
    PublicTables.acceptProb (rowLaw W hW h) (implementAccept X Good) =
      ((X.card:ℝ)/(W.card:ℝ))^h * prob (uniformMass X) h Good := by
  simpa only [PublicTables.acceptProb,mul_one,prob] using
    accepted_scaling X W hX hW hsub h Good (fun _ => 1)

theorem public_iid_domination (X W : Finset Ω) (hX : X.Nonempty) (hW : W.Nonempty)
    (hsub : X⊆W) (h : ℕ) (Good : (Fin h → Ω) → Prop)
    (hGood : (9/10:ℝ) ≤ prob (uniformMass X) h Good)
    (f : (Fin h → Ω) → ℝ) (hf : ∀ z,0≤f z) (m : ℕ) :
    PublicTables.integral (rowLaw W hW h) (implementAccept X Good) f m ≤
      (10/9:ℝ) * (∑ z : Fin h → Ω,rowWeight (uniformMass X) z*f z) := by
  let r : ℝ := ((X.card:ℝ)/(W.card:ℝ))^h
  let I : ℝ := ∑ z : Fin h → Ω,rowWeight (uniformMass X) z*f z
  have hr : 0<r := by
    have hx : 0<(X.card:ℝ) := by exact_mod_cast card_pos.mpr hX
    have hw : 0<(W.card:ℝ) := by exact_mod_cast card_pos.mpr hW
    exact pow_pos (div_pos hx hw) h
  have hI : 0≤I := sum_nonneg (fun z _ => mul_nonneg (rowWeight_nonneg _ (uniform_nonneg X) z) (hf z))
  have ha : r*(9/10) ≤ PublicTables.acceptProb (rowLaw W hW h) (implementAccept X Good) := by
    rw [proposal_acceptance X W hX hW hsub h Good]
    exact mul_le_mul_of_nonneg_left hGood hr.le
  have ha0 : 0<PublicTables.acceptProb (rowLaw W hW h) (implementAccept X Good) :=
    lt_of_lt_of_le (mul_pos hr (by norm_num)) ha
  apply (PublicTables.produced_domination (rowLaw W hW h) (implementAccept X Good) f hf m ha0).trans
  have hn : PublicTables.accepted (rowLaw W hW h) (implementAccept X Good) f ≤ r*I := by
    rw [accepted_scaling X W hX hW hsub h Good f]
    apply mul_le_mul_of_nonneg_left _ hr.le
    apply sum_le_sum
    intro z _
    split_ifs <;> simp [mul_nonneg (rowWeight_nonneg _ (uniform_nonneg X) z) (hf z)]
  calc
    _ ≤ (r*I)/PublicTables.acceptProb (rowLaw W hW h) (implementAccept X Good) :=
      div_le_div_of_nonneg_right hn ha0.le
    _ ≤ (r*I)/(r*(9/10)) :=
      div_le_div_of_nonneg_left (mul_nonneg hr.le hI) (by positivity) ha
    _ = _ := by field_simp; ring

end
end SharpLogRamsey.Validation
end

end OAI
