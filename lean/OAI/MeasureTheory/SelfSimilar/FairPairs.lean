import OAI.MeasureTheory.SelfSimilar.TranslationGain

namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

structure Law where
  support : Finset ℝ
  prob : ℝ → ℝ
  prob_pos : ∀ x ∈ support, 0 < prob x
  prob_sum : ∑ x ∈ support, prob x = 1

noncomputable def Law.edges (ν : Law) (ℓ : ℤ) : Finset (ℝ × ℝ) := by
  classical
  exact (ν.support ×ˢ ν.support).filter fun e =>
    e.1 < e.2 ∧ (2 : ℝ) ^ (-ℓ) ≤ e.2 - e.1 ∧ e.2 - e.1 < (2 : ℝ) ^ (1 - ℓ)

noncomputable def incident {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact ∑ e, ((if e.val.1 = x then w e / 2 else 0) +
      (if e.val.2 = x then w e / 2 else 0))

def Feasible {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) : Prop :=
  (∀ e, 0 ≤ w e) ∧ ∀ x ∈ ν.support, incident w x ≤ ν.prob x

noncomputable def capacity (ν : Law) (ℓ : ℤ) : ℝ :=
  sSup {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t}

theorem edge_mem_left {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.1 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).1

theorem edge_mem_right {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.2 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).2

theorem incident_sum {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ∑ x ∈ ν.support, incident w x = ∑ e, w e := by
  classical
  simp only [incident]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, edge_mem_left e, edge_mem_right e, ite_true]
  ring

theorem feasible_zero (ν : Law) (ℓ : ℤ) : Feasible (ν := ν) (ℓ := ℓ) (fun _ => 0) := by
  constructor
  · simp
  · intro x hx
    simpa [incident] using (ν.prob_pos x hx).le

theorem total_nonneg {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    0 ≤ ∑ e, w e :=
  Finset.sum_nonneg (fun e _ => hw.1 e)

theorem total_le_one {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ 1 := by
  rw [← incident_sum w, ← ν.prob_sum]
  exact Finset.sum_le_sum hw.2

theorem weight_le_one {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w)
    (e : ν.edges ℓ) : w e ≤ 1 := by
  exact (Finset.single_le_sum (fun a _ => hw.1 a) (Finset.mem_univ e)).trans (total_le_one hw)

theorem totals_nonempty (ν : Law) (ℓ : ℤ) :
    {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t}.Nonempty :=
  ⟨0, (fun _ => 0), feasible_zero ν ℓ, by simp⟩

theorem totals_bddAbove (ν : Law) (ℓ : ℤ) :
    BddAbove {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t} := by
  refine ⟨1, ?_⟩
  rintro t ⟨w, hw, rfl⟩
  exact total_le_one hw

theorem capacity_nonneg (ν : Law) (ℓ : ℤ) : 0 ≤ capacity ν ℓ := by
  apply le_csSup (totals_bddAbove ν ℓ)
  exact ⟨(fun _ => 0), feasible_zero ν ℓ, by simp⟩

theorem capacity_le_one (ν : Law) (ℓ : ℤ) : capacity ν ℓ ≤ 1 := by
  apply csSup_le (totals_nonempty ν ℓ)
  rintro t ⟨w, hw, rfl⟩
  exact total_le_one hw

theorem total_le_capacity {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ capacity ν ℓ :=
  le_csSup (totals_bddAbove ν ℓ) ⟨w, hw, rfl⟩

theorem capacity_eq_zero_of_edges_eq_empty {ν : Law} {ℓ : ℤ}
    (he : ν.edges ℓ = ∅) : capacity ν ℓ = 0 := by
  apply le_antisymm _ (capacity_nonneg ν ℓ)
  apply csSup_le (totals_nonempty ν ℓ)
  rintro t ⟨w, _, rfl⟩
  have : IsEmpty (ν.edges ℓ) := ⟨fun e => by simpa [he] using e.property⟩
  simp

theorem feasible_isClosed (ν : Law) (ℓ : ℤ) :
    IsClosed {w : ν.edges ℓ → ℝ | Feasible w} := by
  classical
  change IsClosed ({w : ν.edges ℓ → ℝ | ∀ e, 0 ≤ w e} ∩
    {w | ∀ x ∈ ν.support, incident w x ≤ ν.prob x})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun e => isClosed_le continuous_const (continuous_apply e))
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    apply isClosed_le _ continuous_const
    unfold incident
    apply continuous_finsetSum
    intro e _
    apply Continuous.add <;> split_ifs <;> fun_prop

theorem feasible_isCompact (ν : Law) (ℓ : ℤ) :
    IsCompact {w : ν.edges ℓ → ℝ | Feasible w} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : ν.edges ℓ → ℝ) 1)).of_isClosed_subset
    (feasible_isClosed ν ℓ)
  intro w hw
  exact ⟨hw.1, weight_le_one hw⟩

theorem capacity_attained (ν : Law) (ℓ : ℤ) :
    ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = capacity ν ℓ := by
  obtain ⟨w, hw, hmax⟩ := (feasible_isCompact ν ℓ).exists_isMaxOn
    ⟨(fun _ => 0), feasible_zero ν ℓ⟩
    (continuous_finsetSum _ (fun e _ => continuous_apply e)).continuousOn
  refine ⟨w, hw, le_antisymm (total_le_capacity hw) ?_⟩
  apply csSup_le (totals_nonempty ν ℓ)
  rintro t ⟨v, hv, rfl⟩
  exact hmax hv

theorem sum_first_endpoint {α : Type uα} [DecidableEq α] (F : Finset α) (P : α × α → Prop)
    [DecidablePred P] (q : α → α → ℝ) {x : α} (hx : x ∈ F) :
    (∑ e ∈ (F ×ˢ F).filter P, if e.1 = x then q e.1 e.2 else 0) =
      ∑ y ∈ F, if P (x, y) then q x y else 0 := by
  classical
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · exact fun h => (h hx).elim

theorem sum_second_endpoint {α : Type uα} [DecidableEq α] (F : Finset α) (P : α × α → Prop)
    [DecidablePred P] (q : α → α → ℝ) {x : α} (hx : x ∈ F) :
    (∑ e ∈ (F ×ˢ F).filter P, if e.2 = x then q e.1 e.2 else 0) =
      ∑ y ∈ F, if P (y, x) then q y x else 0 := by
  classical
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · exact fun h => (h hx).elim

theorem coupling_incident {ν : Law} (ℓ : ℤ) (π : ℝ → ℝ → ℝ)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    {x : ℝ} (hx : x ∈ ν.support) :
    incident (ν := ν) (ℓ := ℓ) (fun e => 2 * π e.val.1 e.val.2) x =
      ∑ y ∈ ν.support, if (2 : ℝ) ^ (-ℓ) ≤ |y - x| ∧
        |y - x| < (2 : ℝ) ^ (1 - ℓ) then π x y else 0 := by
  classical
  simp only [incident, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Finset.sum_coe_sort (ν.edges ℓ) (fun e : ℝ × ℝ =>
    (if e.1 = x then π e.1 e.2 else 0) + (if e.2 = x then π e.1 e.2 else 0)),
    Finset.sum_add_distrib]
  unfold Law.edges
  rw [sum_first_endpoint _ _ _ hx, sum_second_endpoint _ _ _ hx, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← hsym x hx y hy]
  rcases lt_trichotomy x y with h | h | h
  · have hxy : ¬y < x := not_lt.mpr h.le
    simp [h, hxy, abs_of_pos (sub_pos.mpr h)]
  · subst y
    have hp : 0 < (2 : ℝ) ^ (-ℓ) := zpow_pos (by norm_num) _
    simp only [lt_self_iff_false, false_and, ite_false, sub_self, abs_zero, not_le.mpr hp, add_zero]
  · have hxy : ¬x < y := not_lt.mpr h.le
    have habs : |y - x| = x - y := by rw [abs_of_neg (sub_neg.mpr h)]; ring
    simp [h, hxy, habs]

theorem coupling_band_le_capacity {ν : Law} (ℓ : ℤ) (π : ℝ → ℝ → ℝ)
    (hπ : ∀ x ∈ ν.support, ∀ y ∈ ν.support, 0 ≤ π x y)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    (hrow : ∀ x ∈ ν.support, ∑ y ∈ ν.support, π x y ≤ ν.prob x) :
    (∑ x ∈ ν.support, ∑ y ∈ ν.support,
      if (2 : ℝ) ^ (-ℓ) ≤ |y - x| ∧ |y - x| < (2 : ℝ) ^ (1 - ℓ)
      then π x y else 0) ≤ capacity ν ℓ := by
  classical
  let w : ν.edges ℓ → ℝ := fun e => 2 * π e.val.1 e.val.2
  have hw : Feasible w := by
    constructor
    · intro e
      exact mul_nonneg (by norm_num) (hπ _ (edge_mem_left e) _ (edge_mem_right e))
    · intro x hx
      rw [coupling_incident ℓ π hsym hx]
      apply le_trans _ (hrow x hx)
      apply Finset.sum_le_sum
      intro y hy
      split_ifs
      · exact le_rfl
      · exact hπ x hx y hy
  calc
    _ = ∑ x ∈ ν.support, incident w x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (coupling_incident ℓ π hsym hx).symm
    _ = ∑ e, w e := incident_sum w
    _ ≤ capacity ν ℓ := total_le_capacity hw

noncomputable def bandIndex (u : ℝ) : ℤ := -⌊Real.logb 2 u⌋

theorem bandIndex_eq {u : ℝ} {ℓ : ℤ}
    (hu : 0 < u) (hl : (2 : ℝ) ^ (-ℓ) ≤ u) (hr : u < (2 : ℝ) ^ (1 - ℓ)) :
    bandIndex u = ℓ := by
  have hlo : (-ℓ : ℤ) = ⌊Real.logb 2 u⌋ := by
    symm
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hu).mpr
      simpa only [Real.rpow_intCast] using hl
    · apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hu).mpr
      have hexp : ((-ℓ : ℤ) : ℝ) + 1 = ((1 - ℓ : ℤ) : ℝ) := by push_cast; ring
      rw [hexp, Real.rpow_intCast]
      exact hr
  simp [bandIndex, ← hlo]

theorem capacity_eq_zero_outside_pair_bands (ν : Law) {ℓ : ℤ}
    (hℓ : ℓ ∉ (ν.support ×ˢ ν.support).image (fun e => bandIndex (e.2 - e.1))) :
    capacity ν ℓ = 0 := by
  classical
  apply capacity_eq_zero_of_edges_eq_empty
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hmem, hlt, hlo, hup⟩ := Finset.mem_filter.mp he
  apply hℓ
  exact Finset.mem_image.mpr ⟨e, hmem, bandIndex_eq (sub_pos.mpr hlt) hlo hup⟩

theorem exists_capacity_cutoff (ν : Law) (a : ℤ) :
    ∃ B : ℤ, a ≤ B ∧ ∀ ℓ, B < ℓ → capacity ν ℓ = 0 := by
  classical
  let s := (ν.support ×ˢ ν.support).image (fun e => bandIndex (e.2 - e.1))
  obtain ⟨B, hB⟩ := (s.finite_toSet.bddAbove.union (bddAbove_singleton : BddAbove ({a} : Set ℤ)))
  refine ⟨B, hB (Or.inr (Set.mem_singleton a)), ?_⟩
  intro ℓ hℓ
  apply capacity_eq_zero_outside_pair_bands
  intro hm
  exact (not_le_of_gt hℓ) (hB (Or.inl hm))

noncomputable def conditionalCoupling {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) (x y : ℝ) : ℝ :=
  if g x = g y then ν.prob x * ν.prob y / FiniteEntropy.mass ν.support ν.prob g (g x) else 0

theorem cell_mass_pos {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x : ℝ} (hx : x ∈ ν.support) :
    0 < FiniteEntropy.mass ν.support ν.prob g (g x) := by
  apply lt_of_lt_of_le (ν.prob_pos x hx)
  apply Finset.single_le_sum
  · intro y hy
    exact (ν.prob_pos y (Finset.mem_filter.mp hy).1).le
  · exact Finset.mem_filter.mpr ⟨hx, rfl⟩

theorem conditionalCoupling_nonneg {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x y : ℝ} (hx : x ∈ ν.support) (hy : y ∈ ν.support) :
    0 ≤ conditionalCoupling ν g x y := by
  unfold conditionalCoupling
  split_ifs
  · exact div_nonneg (mul_nonneg (ν.prob_pos x hx).le (ν.prob_pos y hy).le)
      (cell_mass_pos ν g hx).le
  · exact le_rfl

theorem conditionalCoupling_symm {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) (x y : ℝ) :
    conditionalCoupling ν g x y = conditionalCoupling ν g y x := by
  by_cases h : g x = g y
  · simp only [conditionalCoupling, h, ite_true, mul_comm]
  · simp only [conditionalCoupling, h, Ne.symm h, ite_false]

theorem conditionalCoupling_row {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x : ℝ} (hx : x ∈ ν.support) :
    ∑ y ∈ ν.support, conditionalCoupling ν g x y = ν.prob x := by
  classical
  have hp := ne_of_gt (cell_mass_pos ν g hx)
  unfold conditionalCoupling
  simp only [eq_comm (a := g x), ← Finset.sum_filter]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change ν.prob x * FiniteEntropy.mass ν.support ν.prob g (g x) /
    FiniteEntropy.mass ν.support ν.prob g (g x) = _
  exact mul_div_cancel_right₀ _ hp

theorem conditionalCoupling_eq_zero_of_ne {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x y : ℝ} (h : g x ≠ g y) :
    conditionalCoupling ν g x y = 0 := by
  simp only [conditionalCoupling, h, ite_false]

theorem deviation_le_pair_distance {α : Type uα} (s : Finset α) (p : α → ℝ)
    (X : α → ℝ) (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    (∑ a ∈ s, p a * |X a - ∑ b ∈ s, p b * X b|) ≤
      ∑ a ∈ s, ∑ b ∈ s, p a * p b * |X a - X b| := by
  apply Finset.sum_le_sum
  intro a ha
  have he : X a - ∑ b ∈ s, p b * X b = ∑ b ∈ s, p b * (X a - X b) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
  rw [he]
  have ht := Finset.abs_sum_le_sum_abs (s := s) (f := fun b => p b * (X a - X b))
  have hh : ∑ b ∈ s, |p b * (X a - X b)| = ∑ b ∈ s, p b * |X a - X b| := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [abs_mul, abs_of_nonneg (hp b hb)]
  rw [hh] at ht
  have hm := mul_le_mul_of_nonneg_left ht (hp a ha)
  simpa only [Finset.mul_sum, mul_assoc] using hm

theorem mem_bandIndex {u : ℝ} (hu : 0 < u) :
    (2 : ℝ) ^ (-bandIndex u) ≤ u ∧ u < (2 : ℝ) ^ (1 - bandIndex u) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  constructor
  · rw [← Real.rpow_intCast]
    apply (Real.le_logb_iff_rpow_le hb hu).mp
    simpa only [bandIndex, neg_neg] using Int.floor_le (Real.logb 2 u)
  · rw [← Real.rpow_intCast]
    apply (Real.logb_lt_iff_lt_rpow hb hu).mp
    simpa only [bandIndex, sub_neg_eq_add, Int.cast_add, Int.cast_one, add_comm] using
      Int.lt_floor_add_one (Real.logb 2 u)

theorem coupling_distance_le {ν : Law} (π : ℝ → ℝ → ℝ) (R : ℝ)
    (hπ : ∀ x ∈ ν.support, ∀ y ∈ ν.support, 0 ≤ π x y)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    (hrow : ∀ x ∈ ν.support, ∑ y ∈ ν.support, π x y ≤ ν.prob x)
    (hdiam : ∀ x ∈ ν.support, ∀ y ∈ ν.support, R < |y - x| → π x y = 0) :
    (∑ x ∈ ν.support, ∑ y ∈ ν.support, π x y * |y - x|) ≤
      ∑ ℓ ∈ ((ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2 - e.1|)).filter
        (fun ℓ => (2 : ℝ) ^ (-ℓ) ≤ R), (2 : ℝ) ^ (1 - ℓ) * capacity ν ℓ := by
  classical
  let B := ((ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2 - e.1|)).filter
    (fun ℓ => (2 : ℝ) ^ (-ℓ) ≤ R)
  let cost := fun (ℓ : ℤ) (x y : ℝ) =>
    if (2 : ℝ) ^ (-ℓ) ≤ |y - x| ∧ |y - x| < (2 : ℝ) ^ (1 - ℓ)
    then π x y else 0
  have hcost : ∀ ℓ x y, x ∈ ν.support → y ∈ ν.support → 0 ≤ cost ℓ x y := by
    intro ℓ x y hx hy
    dsimp [cost]
    split_ifs <;> first | exact hπ x hx y hy | exact le_rfl
  calc
    _ ≤ ∑ x ∈ ν.support, ∑ y ∈ ν.support,
        ∑ ℓ ∈ B, (2 : ℝ) ^ (1 - ℓ) * cost ℓ x y := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      by_cases hd : |y - x| = 0
      · rw [hd, mul_zero]
        exact Finset.sum_nonneg (fun ℓ _ => mul_nonneg (zpow_pos (by norm_num) _).le
          (hcost ℓ x y hx hy))
      by_cases hR : R < |y - x|
      · rw [hdiam x hx y hy hR, zero_mul]
        exact Finset.sum_nonneg (fun ℓ _ => mul_nonneg (zpow_pos (by norm_num) _).le
          (hcost ℓ x y hx hy))
      have hu : 0 < |y - x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
      have hb := mem_bandIndex hu
      have hm : bandIndex |y - x| ∈ B := Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, rfl⟩,
          hb.1.trans (le_of_not_gt hR)⟩
      apply le_trans _ (Finset.single_le_sum (fun ℓ _ =>
        mul_nonneg (zpow_pos (by norm_num) _).le (hcost ℓ x y hx hy)) hm)
      dsimp only [cost]
      rw [ite_eq_left hb]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb.2.le (hπ x hx y hy)
    _ = ∑ ℓ ∈ B, (2 : ℝ) ^ (1 - ℓ) *
        ∑ x ∈ ν.support, ∑ y ∈ ν.support, cost ℓ x y := by
      conv_lhs =>
        arg 2
        intro x
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ℓ _
      apply mul_le_mul_of_nonneg_left (coupling_band_le_capacity ℓ π hπ hsym hrow)
      exact (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le

theorem geometric_fine_scale_bound (s : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hs : ∀ h ∈ s, a * (4 : ℝ)^h ≤ 2) :
    (∑ h ∈ s, a * (4 : ℝ)^h) ≤ 8 / 3 := by
  by_cases hn : s.Nonempty
  · let m := s.max' hn
    have hm : m ∈ s := Finset.max'_mem s hn
    have hsub : s ⊆ Finset.range (m + 1) := by
      intro h hh
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' s h hh))
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun h => a * (4 : ℝ)^h) hsub
      (fun h _ _ => mul_nonneg ha (pow_nonneg (by norm_num) h))
    have hg := geom_sum_mul (4 : ℝ) (m + 1)
    have he : (∑ h ∈ Finset.range (m+1), a * (4 : ℝ)^h) * 3 =
        4 * (a * (4 : ℝ)^m) - a := by
      rw [← Finset.mul_sum, mul_assoc]
      norm_num only [show (4 : ℝ) - 1 = 3 by norm_num] at hg
      rw [hg, pow_succ]
      ring
    linarith [hs m hm]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty]
    norm_num

end FairPairs

end EntropyRateDimension

end OAI
