import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard

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
namespace SharpLogRamsey.MomentBudgetBridge
lemma strong_degree_budget (B P : ℝ) (hP : 1 ≤ P) (hB : Real.exp (3*P) ≤ B) :
    1+B*Real.exp (-3*P) ≤ B*Real.exp (-P) := by
  have he := mul_le_mul_of_nonneg_right hB (Real.exp_pos (-3*P)).le
  have h1 : 1 ≤ B*Real.exp (-3*P) := by
    simpa only [← Real.exp_add, show 3*P + -3*P = 0 by ring, Real.exp_zero] using he
  have hexp : 2*Real.exp (-3*P) ≤ Real.exp (-P) := by
    have h2 : 2 ≤ Real.exp (2*P) := by
      have ht := Real.add_one_le_exp (2*P)
      linarith
    have hm := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-3*P)).le
    calc
      _ ≤ Real.exp (2*P)*Real.exp (-3*P) := hm
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hm := mul_le_mul_of_nonneg_left hexp (le_trans (Real.exp_pos _).le hB)
  nlinarith only [h1, hm]

end SharpLogRamsey.MomentBudgetBridge

namespace SharpLogRamsey.HighMoment
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive WeightedPrograms SingletonEnumeration
open PoissonScore AmbientEnumeration ComponentEnumeration
open SharpLogRamsey.MomentBudgetBridge

variable {D H I : Type} [Fintype D] [DecidableEq D]
  [Fintype H] [DecidableEq H] [DecidableEq I]

omit [Fintype D] [DecidableEq I] in

theorem labelled_pair_bound (weight : D → ℝ≥0) (lines : H → Finset D)
    (p R : ℕ) (L : ℝ≥0) (B : ℝ)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2)
    (hmass : ∀ x, mass weight (lines x) ≤ 2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ) *
        a i ^ 200 ≤ B^2*Real.exp (((L : ℝ)*R)/50)) :
    pairMoment (B := Fin R) (fun z : H × Fin p => lines z.1) (fun d => L*weight d) 200 ≤
      (p : ℝ)^2 * (B^2*Real.exp (((L : ℝ)*R)/50)*((T.card : ℝ)+4)*(2*((L : ℝ)*R))^200) := by
  have he : 1 ≤ Real.exp (((L : ℝ)*R)/50) := Real.one_le_exp_iff.mpr (by positivity)
  have hmass' x : ∑ d ∈ lines x, ((L*weight d : ℝ≥0) : ℝ) ≤ 2*(L : ℝ) := by
    simp only [NNReal.coe_mul, ← Finset.mul_sum]
    have ht := mul_le_mul_of_nonneg_left (hmass x) L.coe_nonneg
    simpa only [mass, mul_comm] using ht
  have hlabel := pairMoment_labelled_le (V := Fin p) (B := Fin R) lines
    (fun d => L*weight d) 200 (2*(L : ℝ)) (by positivity) hmass'
  have hpair := pairMoment_dyadic (B := Fin R) lines weight L 200 (by decide) T a ha hcover
    (B^2*Real.exp (((L : ℝ)*R)/50)) (by positivity) hcount
  have hH' : (Fintype.card H : ℝ) ≤ 4*B^2*Real.exp (((L : ℝ)*R)/50) :=
    hH.trans (le_mul_of_one_le_right (by positivity) he)
  simp only [Fintype.card_fin] at hlabel hpair
  apply hlabel.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hdiag := mul_le_mul_of_nonneg_right hH' (pow_nonneg (show 0 ≤ (R : ℝ)*(2*(L : ℝ)) by positivity) 200)
  calc
    _ ≤ (T.card : ℝ)*(B^2*Real.exp (((L : ℝ)*R)/50))*(2*R*(L : ℝ))^200 +
        4*B^2*Real.exp (((L : ℝ)*R)/50)*((R : ℝ)*(2*(L : ℝ)))^200 := add_le_add hpair hdiag
    _ = _ := by ring

omit [Fintype D] [DecidableEq I] in

theorem full_branching_bound (weight : D → ℝ≥0) (lines : H → Finset D)
    (p R N : ℕ) (L : ℝ≥0) (B : ℝ) (hB : 1 ≤ B)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2) (hN : (N : ℝ) ≤ 4*B)
    (hmass : ∀ x, mass weight (lines x) ≤ 2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ) *
        a i ^ 200 ≤ B^2*Real.exp (((L : ℝ)*R)/50))
    (hpoly : certificateOverhead p T.card ((L : ℝ)*R) ≤ Real.exp (2*((L : ℝ)*R)/25)) :
    B*(1+branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L*weight d) B B (2*(L : ℝ)) 200
      (N*p) (1*p) true) ≤ B*Real.exp (((L : ℝ)*R)/10) := by
  have hM := labelled_pair_bound weight lines p R L B hH hmass T a ha hcover hcount
  have hn := labelled_branching_bound p T.card ((L : ℝ)*R) B (Fintype.card H) N
    (pairMoment (B := Fin R) (fun z : H × Fin p => lines z.1) (fun d => L*weight d) 200)
    (by positivity) hB hH hN hM
  have hid : uniformAnchorBudget (V := Fin p) (B := Fin R) 200 (2*(L : ℝ)) =
      anchorBudget p ((L : ℝ)*R) := by
    simp only [uniformAnchorBudget, MomentBudgetBridge.anchorBudget, Fintype.card_fin, Nat.cast_ofNat]
    ring
  have hnorm : 1+branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L*weight d) B B (2*(L : ℝ)) 200
      (N*p) (1*p) true ≤ Real.exp (((L : ℝ)*R)/10) := by
    unfold branchingBound
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, ite_true, one_mul, hid]
    exact hn.trans (absorb_certificate p T.card ((L : ℝ)*R) hpoly)
  exact mul_le_mul_of_nonneg_left hnorm (by linarith)

lemma relation_row_card (rel : H → H → Prop) (y : H) :
    (Fintype.card {x : H // rel y x} : ℝ) ≤
      1+((Finset.univ.filter (fun x : {x : H // x ≠ y} => rel y x)).card : ℝ) := by
  classical
  have he : (Fintype.card {x : H // rel y x} : ℝ) =
      ∑ x : H, if rel y x then (1 : ℝ) else 0 := by
    simp only [Fintype.card_subtype, Finset.sum_boole]
  rw [he, sum_split_diagonal _ y]
  simp only [Finset.sum_boole]
  split_ifs <;> linarith

lemma relation_pairs_card (rel : H → H → Prop) :
    (Fintype.card (RelatedPair rel) : ℝ) ≤ Fintype.card H+
      ((Finset.univ.filter (fun z : DistinctPairs H => rel z.1 z.2)).card : ℝ) := by
  classical
  have he : (Fintype.card (RelatedPair rel) : ℝ) =
      ∑ x : H, ∑ y : H, if rel x y then (1 : ℝ) else 0 := by
    simp only [RelatedPair, Fintype.card_sigma, Nat.cast_sum, Fintype.card_subtype,
      Finset.sum_boole]
  rw [he, sum_pairs_split_diagonal]
  simp only [Finset.sum_boole]
  gcongr
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

lemma strong_pairs_markov (θ : DistinctPairs H → ℝ) (hθ : ∀ z, 0 ≤ θ z)
    (t : ℝ) (ht : 0 ≤ t) (K : ℕ) :
    ((Finset.univ.filter (fun z => t < θ z)).card : ℝ)*t^K ≤ ∑ z, θ z ^ K := by
  classical
  have he : ((Finset.univ.filter (fun z => t < θ z)).card : ℝ) =
      ∑ z, if t < θ z then (1 : ℝ) else 0 := by simp only [Finset.sum_boole]
  rw [he, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  by_cases htz : t < θ z
  · simpa only [ite_eq_left htz, one_mul] using pow_le_pow_left₀ ht htz.le K
  · simp only [ite_eq_right htz, zero_mul]
    exact pow_nonneg (hθ z) K

omit [Fintype D] [DecidableEq D] [DecidableEq H] in

lemma deviation_sum (weight : D → ℝ≥0) (lines : H → Finset D)
    (base : ℝ) (R : ℕ) (hR : 4 ≤ R)
    (hdelta : ∀ x, |mass weight (lines x)-base| ≤ (17/100 : ℝ))
    (C : ℝ) (hsq : (∑ x, (mass weight (lines x)-base)^2) ≤ C) :
    (∑ x, |mass weight (lines x)-base|^(R/2)) ≤ C := by
  apply le_trans _ hsq
  apply Finset.sum_le_sum
  intro x _
  calc
    _ ≤ |mass weight (lines x)-base|^2 :=
      pow_le_pow_of_le_one (abs_nonneg _) ((hdelta x).trans (by norm_num)) (by omega)
    _ = _ := sq_abs _

omit [DecidableEq I] in
omit [Fintype D] in

theorem dyadic_shift_bounds (weight : D → ℝ≥0) (lines : H → Finset D)
    (p : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ)*
        a i^200 ≤ B^2*Real.exp (P/50))
    (hrow : ∀ y i, i ∈ T →
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        a i ≤ mass weight (lines x ∩ lines y))).card : ℝ)*a i^200 ≤ B*Real.exp (P/50))
    (hpoly : shiftOverhead p T.card ≤ Real.exp (2*P/25)) :
    (∀ y, (∑ x : H, shiftKernel weight lines p 200 x y) ≤ B*Real.exp (P/10)) ∧
    (∑ x : H, ∑ y : H, shiftKernel weight lines p 200 x y) ≤ (B*Real.exp (P/10))^2 := by
  have hB0 : 0 ≤ B := by linarith
  constructor
  · intro y
    have hcover' (x : {x : H // x ≠ y}) (hx : 0 < mass weight (lines x ∩ lines y)) :
        ∃ i ∈ T, a i ≤ mass weight (lines x ∩ lines y) ∧
          mass weight (lines x ∩ lines y) ≤ 2*a i := by
      have hh := hcover ⟨y, x⟩
      simpa only [strength, mass, Finset.inter_comm] using hh (by
        simpa only [strength, mass, Finset.inter_comm] using hx)
    have hs := shift_row_dyadic weight lines p 200 (by decide) y T a
      (B*Real.exp (P/50)) (by positivity) ha hcover' (hrow y)
    apply hs.trans
    calc
      _ ≤ 4*B+(T.card : ℝ)*B*Real.exp (P/50)*(2*(p : ℝ))^200 := by
        nlinarith only [hB]
      _ ≤ _ := shifted_dyadic_budget p T.card P B hP hB0 hpoly
  · have hs := shift_pairs_dyadic weight lines p 200 (by decide) T a
      (B^2*Real.exp (P/50)) (by positivity) ha hcover hcount
    apply hs.trans
    calc
      _ ≤ 4*B^2+(T.card : ℝ)*B^2*Real.exp (P/50)*(2*(p : ℝ))^200 := by
        nlinarith only [hH]
      _ ≤ B^2*Real.exp (P/10) := shifted_dyadic_budget p T.card P (B^2) hP (sq_nonneg _) hpoly
      _ ≤ (B*Real.exp (P/10))^2 := by
        have he : 1 ≤ Real.exp (P/10) := Real.one_le_exp_iff.mpr (by positivity)
        have hsq : Real.exp (P/10) ≤ Real.exp (P/10)^2 := le_self_pow₀ he (by decide : 2 ≠ 0)
        simpa only [mul_pow] using mul_le_mul_of_nonneg_left hsq (sq_nonneg B)

omit [Fintype D] [DecidableEq I] in

theorem strong_relation_pairs (weight : D → ℝ≥0) (lines : H → Finset D)
    (p : ℕ) (hp : 0 < p) (B P : ℝ) (hP : 0 ≤ P)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ)*
        a i^200 ≤ B^2*Real.exp (P/50))
    (hpoly : shiftOverhead p T.card ≤ Real.exp (2*P/25)) :
    (Fintype.card (RelatedPair (overlapRelation weight lines (1/(100*p)))) : ℝ) ≤
      B^2*Real.exp (P/10) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpne : (100*(p : ℝ)) ≠ 0 := by positivity
  have hmoment := DyadicMoments.moment_le_of_cover (strength lines weight) a T 200
    (by decide) (B^2*Real.exp (P/50)) (by positivity)
    (strength_nonneg lines weight) ha hcover hcount
  have hmarkov := strong_pairs_markov (strength lines weight) (strength_nonneg lines weight)
    (1/(100*(p : ℝ))) (by positivity) 200
  have hm := mul_le_mul_of_nonneg_right (hmarkov.trans hmoment)
    (pow_nonneg (show 0 ≤ 100*(p : ℝ) by positivity) 200)
  have hcancel : (1/(100*(p : ℝ)))^200*(100*(p : ℝ))^200 = 1 := by
    rw [← mul_pow, one_div_mul_cancel hpne, one_pow]
  have hdistinct : ((Finset.univ.filter (fun z : DistinctPairs H =>
      1/(100*(p : ℝ)) < strength lines weight z)).card : ℝ) ≤
      (T.card : ℝ)*(B^2)*Real.exp (P/50)*(200*(p : ℝ))^200 := by
    rw [mul_assoc, hcancel, mul_one] at hm
    apply hm.trans_eq
    rw [show 200*(p : ℝ) = 2*(100*(p : ℝ)) by ring, mul_pow]
    ring
  have hh := relation_pairs_card (overlapRelation weight lines (1/(100*(p : ℝ))))
  apply hh.trans
  have hn : ((Finset.univ.filter (fun z : DistinctPairs H =>
      overlapRelation weight lines (1/(100*(p : ℝ))) z.1 z.2)).card : ℝ) ≤
      (T.card : ℝ)*B^2*Real.exp (P/50)*(200*(p : ℝ))^200 := by
    convert hdistinct using 1
    congr 2
  calc
    _ ≤ 4*B^2+(T.card : ℝ)*B^2*Real.exp (P/50)*(200*(p : ℝ))^200 := add_le_add hH hn
    _ ≤ _ := strong_dyadic_budget p T.card P (B^2) hP (sq_nonneg B) hpoly

omit [Fintype D] in

theorem strong_relation_degree (weight : D → ℝ≥0) (lines : H → Finset D)
    (p : ℕ) (B P : ℝ) (hP : 1 ≤ P) (hB : Real.exp (3*P) ≤ B)
    (hstrong : ∀ y,
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        1/(100*(p : ℝ)) ≤ mass weight (lines x ∩ lines y))).card : ℝ) ≤ B*Real.exp (-3*P)) :
    ∃ Δ : ℕ,
      (∀ y, Fintype.card {x : H // overlapRelation weight lines (1/(100*p)) y x} ≤ Δ) ∧
      (Δ : ℝ) ≤ B*Real.exp (-P) := by
  have hB0 : 0 ≤ B := (Real.exp_pos _).le.trans hB
  refine ⟨⌊B*Real.exp (-P)⌋₊, ?_, Nat.floor_le (by positivity)⟩
  intro y
  apply Nat.le_floor
  have hh := relation_row_card (overlapRelation weight lines (1/(100*(p : ℝ)))) y
  have hm : ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
      overlapRelation weight lines (1/(100*(p : ℝ))) y x)).card : ℝ) ≤
        ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
          1/(100*(p : ℝ)) ≤ mass weight (lines x ∩ lines y))).card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have ht := hx.le
    simpa only [overlapRelation, Finset.inter_comm] using ht
  apply hh.trans
  calc
    _ ≤ 1+B*Real.exp (-3*P) := by linarith only [hm, hstrong y]
    _ ≤ _ := strong_degree_budget B P hP hB

omit [DecidableEq I] in

theorem prepared_pencil_high_moment (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (R : ℕ) (own : H → Fin R → Bool)
    (L : ℝ≥0) (base B : ℝ)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (24/25 : ℝ) ≤ base)
    (hlower : ∀ x, (3/4 : ℝ) ≤ mass weight (lines x))
    (hupper : ∀ x, mass weight (lines x) ≤ 2)
    (hdelta : ∀ x, |mass weight (lines x)-base| ≤ (17/100 : ℝ))
    (hB : Real.exp (3*((L : ℝ)*R)) ≤ B)
    (hH : (Fintype.card H : ℝ) ≤ 4*B^2)
    (N : ℕ) (hN : (N : ℝ) ≤ 4*B)
    (hone : ∀ d, (Finset.univ.filter (fun x => d ∈ lines x)).card ≤ N)
    (htwo : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun x => d ∈ lines x ∧ e ∈ lines x)).card ≤ 1)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2*a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ)*
        a i^200 ≤ B^2*Real.exp (((L : ℝ)*R)/50))
    (hrow : ∀ y i, i ∈ T →
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        a i ≤ mass weight (lines x ∩ lines y))).card : ℝ)*a i^200 ≤
          B*Real.exp (((L : ℝ)*R)/50))
    (hstrong : ∀ y,
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        1/(100*(p : ℝ)) ≤ mass weight (lines x ∩ lines y))).card : ℝ) ≤
          B*Real.exp (-3*((L : ℝ)*R)))
    (hsq : (∑ x, (mass weight (lines x)-base)^2) ≤ B*Real.exp (((L : ℝ)*R)/100))
    (hpoly : certificateOverhead p T.card ((L : ℝ)*R) ≤ Real.exp (2*((L : ℝ)*R)/25))
    (hshift : shiftOverhead p T.card ≤ Real.exp (2*((L : ℝ)*R)/25))
    (hp2 : (p : ℝ)^2 ≤ Real.exp (((L : ℝ)*R)/10))
    (hps : 2*(p : ℝ)+3 ≤ Real.exp (((L : ℝ)*R)/10))
    (h : ℕ) (hh : 0 < h) (hR : 400 ≤ R)
    (hsize : h ≤ (R/2)/400)
    (herr : (p : ℝ)*h*(19/20 : ℝ)^(h-1) < 1/2) :
    (∫ ω, (∑ x : H, scoreTerm (lines x) (Real.exp (-(L : ℝ)*base)) (own x)
      (fun r d => ω (r,d)))^p
      ∂batchMeasure (fun i : Fin R × D => L*weight i.2)) ≤
        B^p*Real.exp (-(1/10 : ℝ)*(p*((L : ℝ)*R))) := by
  have hP0 : 0 ≤ (L : ℝ)*R := by positivity
  have hP : 1 ≤ (L : ℝ)*R := by
    have hR' : (400 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  have hB1 : 1 ≤ B := (Real.one_le_exp_iff.mpr (by positivity)).trans hB
  have hB0 : 0 ≤ B := by linarith
  have hbranch := full_branching_bound weight lines p R N L B hB1 hH hN hupper
    T a ha hcover hcount hpoly
  obtain ⟨hrows, hpairs⟩ := dyadic_shift_bounds weight lines p B ((L : ℝ)*R)
    hB1 hP0 hH T a ha hcover hcount hrow hshift
  obtain ⟨Δ, hΔ, hdeg⟩ := strong_relation_degree weight lines p B ((L : ℝ)*R) hP hB hstrong
  have hrel := strong_relation_pairs weight lines p hp B ((L : ℝ)*R) hP0 hH
    T a ha hcover hcount hshift
  have hmass x : ∑ d ∈ lines x, ((L*weight d : ℝ≥0) : ℝ) ≤ 2*(L : ℝ) := by
    simp only [NNReal.coe_mul, ← Finset.mul_sum]
    have ht := mul_le_mul_of_nonneg_left (hupper x) L.coe_nonneg
    simpa only [mass, mul_comm] using ht
  exact ambient_untruncated_moment weight lines hp R own L B B (2*(L : ℝ))
    (B*Real.exp (((L : ℝ)*R)/10)) (B*Real.exp (((L : ℝ)*R)/100)) base B
    hL (by linarith) hlower hdelta (by linarith) hB1 (by positivity)
    (by positivity) (by positivity) hB0 hmass 200 h N 1 (by decide) (by omega)
    hh hsize herr hone htwo hbranch hrows hpairs
    (deviation_sum weight lines base R (by omega) hdelta _ hsq)
    (singleton_budget p B ((L : ℝ)*R) hB0 hP0 hps) hp2 Δ hΔ hdeg hrel

end SharpLogRamsey.HighMoment

end

end OAI
