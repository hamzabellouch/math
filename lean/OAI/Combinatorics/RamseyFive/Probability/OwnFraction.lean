import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.ClippedWeight

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity

section
open Module ProjectiveIncidence CellVariance PencilRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma cellMass_nonneg (C : Finset (ℙ K V)) {δ : ℝ} (hδ : 0 ≤ δ)
    (H : ℙ K (Dual K V)) : 0 ≤ cellMass C δ H :=
  mul_nonneg hδ (Nat.cast_nonneg _)

lemma cellMass_mono {A B : Finset (ℙ K V)} (hAB : A ⊆ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (H : ℙ K (Dual K V)) : cellMass A δ H ≤ cellMass B δ H := by
  apply mul_le_mul_of_nonneg_left _ hδ
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hAB))

lemma cellMass_union (A B : Finset (ℙ K V)) (δ : ℝ) (H : ℙ K (Dual K V)) :
    cellMass (A∪B) δ H = cellMass A δ H+cellMass B δ H-cellMass (A∩B) δ H := by
  have he := Finset.card_union_add_card_inter
    (A.filter fun y => Incident y H) (B.filter fun y => Incident y H)
  have he' : (((A∪B).filter fun y => Incident y H).card:ℝ)+
      ((A∩B).filter fun y => Incident y H).card =
        (A.filter fun y => Incident y H).card+(B.filter fun y => Incident y H).card := by
    rw [Finset.filter_union,Finset.filter_inter_distrib]
    exact_mod_cast he
  unfold cellMass
  linear_combination δ*he'

lemma filter_sdiff_eq {α : Type*} [DecidableEq α] (S O : Finset α)
    (p : α→Prop) [DecidablePred p] : (S\O).filter p = S.filter p\O.filter p := by
  ext y
  simp only [Finset.mem_filter,Finset.mem_sdiff]
  tauto

lemma cellMass_sdiff {S O : Finset (ℙ K V)} (hOS : O ⊆ S) (δ : ℝ)
    (H : ℙ K (Dual K V)) : cellMass (S\O) δ H = cellMass S δ H-cellMass O δ H := by
  have he := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter (fun y => Incident y H) hOS)
  have he' : (((S\O).filter fun y => Incident y H).card:ℝ)+
      (O.filter fun y => Incident y H).card = (S.filter fun y => Incident y H).card := by
    rw [filter_sdiff_eq]
    exact_mod_cast he
  unfold cellMass
  linear_combination δ*he'

lemma cellMass_erase (S : Finset (ℙ K V)) (x : ℙ K V) {δ : ℝ} (hδ : 0 ≤ δ)
    (H : ℙ K (Dual K V)) :
    0 ≤ cellMass S δ H-cellMass (S\{x}) δ H ∧
      cellMass S δ H-cellMass (S\{x}) δ H ≤ δ := by
  have hl := cellMass_mono (Finset.sdiff_subset : S\{x} ⊆ S) hδ H
  have hc : (S.filter fun y => Incident y H).card ≤
      ((S\{x}).filter fun y => Incident y H).card+1 := by
    rw [filter_sdiff_eq]
    have h := Finset.card_le_card_sdiff_add_card (s:=S.filter fun y => Incident y H)
      (t:=({x}:Finset (ℙ K V)).filter fun y => Incident y H)
    have h1 : (({x}:Finset (ℙ K V)).filter fun y => Incident y H).card ≤ 1 :=
      (Finset.card_filter_le ..).trans_eq (Finset.card_singleton x)
    omega
  have hc' : ((S.filter fun y => Incident y H).card:ℝ) ≤
      ((S\{x}).filter fun y => Incident y H).card+1 := by exact_mod_cast hc
  constructor
  · exact sub_nonneg.mpr hl
  · have hm := mul_le_mul_of_nonneg_left hc' hδ
    unfold cellMass
    nlinarith only [hm]

variable [Finite K] [Fintype (ℙ K (Dual K V))]

omit [Finite K] in
lemma typical_deviation {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) {H : ℙ K (Dual K V)} (hH : H∉exceptional S C)
    (j : Option J) : |deviation S C j H| ≤ threshold j := by
  by_contra hn
  exact hH (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,lt_of_not_ge hn⟩)

noncomputable def ownFraction (S A B : Finset (ℙ K V)) : ℝ :=
  ((A∪B).card:ℝ)/(S.card:ℝ)

noncomputable def outsideMass (S O : Finset (ℙ K V)) (x : ℙ K V) (H : ℙ K (Dual K V)) : ℝ :=
  cellMass (S\(O∪{x})) ((Nat.card K:ℝ)/S.card) H

noncomputable def queryLoss (S O : Finset (ℙ K V)) (x : ℙ K V) (H : ℙ K (Dual K V)) : ℝ :=
  cellMass (S\O) ((Nat.card K:ℝ)/S.card) H-outsideMass S O x H

omit [Finite K] [Fintype (ℙ K (Dual K V))] in
lemma queryLoss_bounds (S O : Finset (ℙ K V)) (x : ℙ K V) (H : ℙ K (Dual K V)) :
    0 ≤ queryLoss S O x H ∧ queryLoss S O x H ≤ (Nat.card K:ℝ)/S.card := by
  have h := cellMass_erase (S\O) x (show 0 ≤ (Nat.card K:ℝ)/S.card by positivity) H
  have he : (S\O)\{x}=S\(O∪{x}) := by
    ext y
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  simpa only [queryLoss,outsideMass,he] using h

omit [Finite K] [Fintype (ℙ K (Dual K V))] in
lemma outsideMass_deviation {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (hS : S.Nonempty) (a b c : J)
    (ha : C a ⊆ S) (hb : C b ⊆ S) (hc : C c=C a∩C b)
    (x : ℙ K V) (H : ℙ K (Dual K V)) :
    outsideMass S (C a∪C b) x H-(1-ownFraction S (C a) (C b)) =
      deviation S C none H-deviation S C (some a) H-deviation S C (some b) H+
        deviation S C (some c) H-queryLoss S (C a∪C b) x H := by
  have hn : (S.card:ℝ)≠0 := by exact_mod_cast hS.card_pos.ne'
  have hmass := cellMass_sdiff (Finset.union_subset ha hb) ((Nat.card K:ℝ)/S.card) H
  rw [cellMass_union] at hmass
  have hcard : ((C a∪C b).card:ℝ)+((C a∩C b).card:ℝ)=(C a).card+(C b).card := by
    exact_mod_cast Finset.card_union_add_card_inter (C a) (C b)
  simp only [deviation,familyCell,queryLoss,ownFraction,div_self hn,hc]
  rw [hmass]
  have hs := congrArg (fun z : ℝ => z/(S.card:ℝ)) hcard
  simp only [add_div] at hs
  linarith only [hs]

omit [Finite K] in

theorem typical_mass_bounds {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (hS : S.Nonempty) (a b c : J)
    (ha : C a ⊆ S) (hb : C b ⊆ S) (hc : C c=C a∩C b)
    (x : ℙ K V) {H : ℙ K (Dual K V)} (hH : H∉exceptional S C)
    (hf : ownFraction S (C a) (C b) ≤ 2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1/100) :
    3/4 ≤ outsideMass S (C a∪C b) x H ∧
    |outsideMass S (C a∪C b) x H-(1-ownFraction S (C a) (C b))| ≤ 17/100 ∧
    outsideMass S (C a∪C b) x H ≤ 11/10 := by
  have h0 := typical_deviation S C hH none
  have h1 := typical_deviation S C hH (some a)
  have h2 := typical_deviation S C hH (some b)
  have h3 := typical_deviation S C hH (some c)
  simp only [threshold,abs_le] at h0 h1 h2 h3
  have hl := queryLoss_bounds S (C a∪C b) x H
  have he := outsideMass_deviation S C hS a b c ha hb hc x H
  have hmass : outsideMass S (C a∪C b) x H ≤ cellMass S ((Nat.card K:ℝ)/S.card) H :=
    cellMass_mono Finset.sdiff_subset (by positivity) H
  have hbase : deviation S C none H=cellMass S ((Nat.card K:ℝ)/S.card) H-1 := by
    simp only [deviation,familyCell,div_self (show (S.card:ℝ)≠0 by exact_mod_cast hS.card_pos.ne')]
  rw [hbase] at h0
  refine ⟨?_,⟨?_,?_⟩⟩
  · linarith
  · rw [abs_le]; constructor <;> linarith
  · linarith

end

open Module ProjectiveIncidence CellVariance PencilRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma typical_variance_component {d : ℕ} {J : Type*} [Fintype J]
    (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) (x : ℙ K V)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C) {ξ : ℝ}
    (hx : x∉irregular (d:=d) S C ξ) (j : Option J) :
    (∑ H : F,(deviation S C j H.val)^2) ≤ scale (K:=K) d S.card*Real.exp ξ := by
  have hr : weightOnPencil (clippedWeight S C (some j)) x ≤ scale (K:=K) d S.card*Real.exp ξ := by
    by_contra hn
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,some j,lt_of_not_ge hn⟩)
  have he : (∑ H : F,(deviation S C j H.val)^2)=
      ∑ H∈F,incidenceEntry x H*clippedWeight S C (some j) H := by
    rw [Finset.sum_coe_sort F (fun H => (deviation S C j H)^2)]
    apply Finset.sum_congr rfl
    intro H hH
    have hd := typical_deviation S C (hF H hH).2 j
    have ht : threshold j ≤ 1 := by cases j <;> norm_num [threshold]
    have hs : (deviation S C j H)^2 ≤ 1 := by
      have ha := abs_nonneg (deviation S C j H)
      have hb := hd.trans ht
      nlinarith [sq_abs (deviation S C j H)]
    simp only [incidenceEntry,ite_eq_left (hF H hH).1,clippedWeight,min_eq_right hs,one_mul]
  rw [he]
  apply le_trans _ hr
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro H _ _
  have hw := (clippedWeight_bounds S C (some j) H).1
  by_cases h : Incident x H <;> simp [incidenceEntry,h,hw]

lemma Q_le_two_pow (q k : ℕ) (hq : 2≤q) : (Q q k:ℝ) ≤ 2*(q:ℝ)^k-1 := by
  induction k with
  | zero => norm_num [Q]
  | succ k ih =>
    have he : (Q q (k+1):ℝ)=(Q q k:ℝ)+(q:ℝ)^(k+1) := by
      unfold Q
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_pow]
    rw [he,pow_succ]
    have hq' : (2:ℝ)≤q := by exact_mod_cast hq
    have hp := pow_nonneg (Nat.cast_nonneg q : (0:ℝ)≤q) k
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]

omit [Fintype (ℙ K V)] in
lemma typical_pencil_card {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (x : ℙ K V) (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H) : (F.card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-1) := by
  have hf : F ⊆ Finset.univ.filter (Incident x) := fun H hH =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hF H hH⟩
  have he : (Finset.univ.filter (Incident x)).card=Q (Nat.card K) (d-1) := by
    rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card,card_hyperplanes_through_point,hdim]
    unfold Q
    congr 1
    congr 1
    omega
  have hc : (F.card:ℝ)≤Q (Nat.card K) (d-1) := by exact_mod_cast (Finset.card_le_card hf).trans_eq he
  have hq : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  linarith [Q_le_two_pow (Nat.card K) (d-1) hq]

omit [Fintype (ℙ K V)] in
lemma queryLoss_square_sum {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (S O : Finset (ℙ K V)) (hS : S.Nonempty) (x : ℙ K V)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1) :
    (∑ H : F,(queryLoss S O x H.val)^2) ≤ 2*scale (K:=K) d S.card := by
  have hn0 : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hδ : 0≤(Nat.card K:ℝ)/S.card := by positivity
  have hc := typical_pencil_card hdim hd x F hF
  have he : (Nat.card K:ℝ)^(d-1)*(Nat.card K:ℝ)=(Nat.card K:ℝ)^d := by
    rw [←pow_succ]; congr 1; omega
  calc
    _ ≤ ∑ H : F,((Nat.card K:ℝ)/S.card)^2 := by
      apply Finset.sum_le_sum
      intro H _
      exact pow_le_pow_left₀ (queryLoss_bounds S O x H.val).1 (queryLoss_bounds S O x H.val).2 2
    _ = (F.card:ℝ)*((Nat.card K:ℝ)/S.card)^2 := by simp
    _ ≤ (2*(Nat.card K:ℝ)^(d-1))*((Nat.card K:ℝ)/S.card)^2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = 2*scale (K:=K) d S.card*((Nat.card K:ℝ)/S.card) := by
      unfold scale
      rw [←he]
      ring
    _ ≤ 2*scale (K:=K) d S.card := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn
        (mul_nonneg (by norm_num) (scale_nonneg _ _ hn0.le))

lemma four_sq (a b c d : ℝ) : (a-b-c+d)^2 ≤ 4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a+b),sq_nonneg (c+d),sq_nonneg ((a-b)+(c-d))]

theorem typical_mass_variance {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type*} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (x : ℙ K V) (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    {ξ : ℝ} (hξ : 0≤ξ) (hx : x∉irregular (d:=d) S C ξ)
    (hn : (Nat.card K:ℝ)/S.card ≤ 1) :
    (∑ H : F,(outsideMass S (C a∪C b) x H.val-(1-ownFraction S (C a) (C b)))^2) ≤
      40*scale (K:=K) d S.card*Real.exp ξ := by
  have hv (j : Option J) := typical_variance_component S C x F hF hx j
  have hl := queryLoss_square_sum hdim hd S (C a∪C b) hS x F (fun H hH => (hF H hH).1) hn
  have hB := scale_nonneg (K:=K) d (S.card:ℝ) (Nat.cast_nonneg _)
  have he : 1≤Real.exp ξ := Real.one_le_exp_iff.mpr hξ
  have hs : (∑ H : F,(outsideMass S (C a∪C b) x H.val-(1-ownFraction S (C a) (C b)))^2) ≤
      8*((∑ H : F,(deviation S C none H.val)^2)+
        (∑ H : F,(deviation S C (some a) H.val)^2)+
        (∑ H : F,(deviation S C (some b) H.val)^2)+
        (∑ H : F,(deviation S C (some c) H.val)^2))+
      2*∑ H : F,(queryLoss S (C a∪C b) x H.val)^2 := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro H _
    rw [outsideMass_deviation S C hS a b c ha hb hc x H.val]
    have h4 := four_sq (deviation S C none H.val) (deviation S C (some a) H.val)
      (deviation S C (some b) H.val) (deviation S C (some c) H.val)
    nlinarith [sq_nonneg (deviation S C none H.val-deviation S C (some a) H.val-
      deviation S C (some b) H.val+deviation S C (some c) H.val+
      queryLoss S (C a∪C b) x H.val)]
  have hb' := mul_le_mul_of_nonneg_left he hB
  nlinarith only [hs,hv none,hv (some a),hv (some b),hv (some c),hl,hb',hB]

end SharpRamseyFive.ScoreRegularity

end OAI
