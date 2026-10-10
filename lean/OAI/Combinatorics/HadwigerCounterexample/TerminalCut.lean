import OAI.Combinatorics.HadwigerCounterexample.EntropyContainers

namespace OAI

/-! # Terminal Cut -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Individual marginal caps (mapW denotes the actual marginals) and a joint cap. -/
def pairCaps (μ : Wgt α) (m d : ℝ) (w : Wgt (α × α)) :=
  (∀ x, mapW w Prod.fst x ≤ m * μ x) ∧
  (∀ x, mapW w Prod.snd x ≤ m * μ x) ∧
  (∀ p, w p ≤ d * pairW μ μ p)

theorem closed_pairCaps (μ : Wgt α) (m d : ℝ) :
    IsClosed {w : Wgt (α × α) | pairCaps μ m d w} := by
  have e :
    {w : Wgt (α × α) | pairCaps μ m d w} =
      (⋂ x, {w | mapW w Prod.fst x ≤ m * μ x}) ∩
      ((⋂ x, {w | mapW w Prod.snd x ≤ m * μ x}) ∩
       (⋂ p, {w | w p ≤ d * pairW μ μ p})) := by ext; simp [pairCaps]
  rw [e]
  exact (isClosed_iInter fun _ => isClosed_le (pr_continuous _) continuous_const).inter
    ((isClosed_iInter fun _ => isClosed_le (pr_continuous _) continuous_const).inter
      (isClosed_iInter fun _ => isClosed_le (continuous_apply _) continuous_const))

theorem mid_pairCaps {μ : Wgt α} {m d : ℝ} {w v : Wgt (α × α)}
    (hw : pairCaps μ m d w) (hv : pairCaps μ m d v) :
    pairCaps μ m d (midLaw w v) := by
  have h1 (f : α × α → α) (x : α) :
      mapW (midLaw w v) f x = (mapW w f x + mapW v f x) * 2⁻¹ := midLaw_pr w v _
  constructor
  · intro x
    rw [h1]
    linarith only [hw.1 x, hv.1 x]
  refine ⟨fun x => ?_, fun p => ?_⟩
  · rw [h1]
    linarith only [hw.2.1 x, hv.2.1 x]
  · unfold midLaw
    linarith only [hw.2.2 p, hv.2.2 p]

theorem compact_subLaw : IsCompact {w : Wgt α | SubLaw w} := by
  refine IsCompact.of_isClosed_subset (s:=Set.Icc (0 : Wgt α) 1) isCompact_Icc ?_ ?_
  · have he :
        {w : Wgt α | SubLaw w} =
        (⋂ x, {w | 0 ≤ w x}) ∩ {w : Wgt α | tot w ≤ 1} := by
      ext w
      have : SubLaw w ↔ (∀ x, 0 ≤ w x) ∧ tot w ≤ 1 :=
        ⟨fun h => ⟨h.nz,h.total⟩, fun ⟨h,g⟩ => ⟨h,g⟩⟩
      simp [this]
    rw [he]
    exact (isClosed_iInter fun _ => isClosed_le continuous_const (continuous_apply _)).inter
      (isClosed_le tot_continuous continuous_const)
  · intro w hw
    exact ⟨hw.nz,hw.weight_le_one⟩

private def incW (w : Wgt α) (p : α) (b : ℝ) : Wgt α :=
  fun x => w x + b * ind (x = p)

private theorem incW_tot (w : Wgt α) (p : α) (b : ℝ) :
    tot (incW w p b) = tot w + b := by
  classical simp [tot, incW, ind, Finset.sum_add_distrib]

private theorem incW_pr (w : Wgt α) (p : α) (b : ℝ) (q : α → Prop) :
    pr (incW w p b) q = pr w q + b * ind (q p) := by
  classical
  simp only [pr, avg, incW, add_mul, Finset.sum_add_distrib, add_right_inj]
  rw [Finset.sum_eq_single p]
  · simp [ind]
  · intro x _ h; simp [ind,h]
  · simp

private theorem sat_le_tot {u v : Wgt α} (hu : ∀ x, 0 ≤ u x) (b : ℝ) :
    b * pr v (fun x => u x = b * v x) ≤ tot u := by
  have e :
      b * pr v (fun x => u x = b * v x) = pr u (fun x => u x = b * v x) := by
    unfold pr avg
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : u x = b * v x <;> simp [ind, h]
  rw [e]; exact pr_le_tot hu

private theorem mapW_tot' {β : Type*} [Fintype β] (w : Wgt α) (f : α → β) :
    tot (mapW w f) = tot w := by simpa using mapW_pr w f (fun _ => True)

theorem terminal {μ : Wgt α} (hu : ∀ x, 0 ≤ μ x)
    {m d : ℝ} (hm : 0 < m) (hd : 0 < d) (R : α × α → Prop)
    (hR : ¬∃ w : Wgt (α × α), IsLaw w ∧ pairCaps μ m d w ∧ carried w R) :
    ∃ (S : α → Prop) (E : α × α → Prop),
      m * pr μ S < 2 ∧ d * pr (pairW μ μ) E < 1 ∧
      ∀ x : α × α, R x → S x.1 ∨ S x.2 ∨ E x := by
  let T := {w : Wgt (α × α) | SubLaw w} ∩
    ({w | pairCaps μ m d w} ∩ {w | carried w R})
  have hc : IsCompact T := compact_subLaw.inter_right
    ((closed_pairCaps _ _ _).inter (closed_carried _))
  have ht : T.Nonempty := by
    refine ⟨(fun _ => 0), ⟨?_,?_⟩, ⟨fun x => ?_, fun x => ?_, fun p => ?_⟩, fun _ _ => rfl⟩
    · exact fun _ => le_rfl
    · simp [tot]
    · simpa [mapW,pr,avg] using mul_nonneg hm.le (hu x)
    · simpa [mapW,pr,avg] using mul_nonneg hm.le (hu x)
    · exact mul_nonneg hd.le (mul_nonneg (hu _) (hu _))
  obtain ⟨w,hw,hwmax⟩ := hc.exists_isMaxOn ht tot_continuous.continuousOn
  have hwL : SubLaw w := hw.1
  have hwC : pairCaps μ m d w := hw.2.1
  have hw' : tot w < 1 := lt_of_le_of_ne hwL.total (fun he =>
    hR ⟨w,⟨hwL.nz,he⟩,hwC,hw.2.2⟩)
  let hit (f : α × α → α) (x : α) := mapW w f x = m * μ x
  let EH (p : α × α) := w p = d * pairW μ μ p
  refine ⟨fun x => hit Prod.fst x ∨ hit Prod.snd x, EH, ?_, ?_, ?_⟩
  · have hh (f : α × α → α) : m * pr μ (hit f) < 1 := by
      apply lt_of_le_of_lt _ hw'
      rw [← mapW_tot' w f]
      exact sat_le_tot (fun _ => pr_nonneg hwL.nz) m
    have h := mul_le_mul_of_nonneg_left
      (pr_or_le (p:=hit Prod.fst) (q:=hit Prod.snd) hu) hm.le
    linarith only [h, hh Prod.fst, hh Prod.snd]
  · exact lt_of_le_of_lt (sat_le_tot hwL.nz d) hw'
  intro x hx
  by_contra hn
  push Not at hn
  have hg : 0 < m * μ x.1 - mapW w Prod.fst x.1 :=
    sub_pos.mpr (lt_of_le_of_ne (hwC.1 _) hn.1.1)
  have hi : 0 < m * μ x.2 - mapW w Prod.snd x.2 :=
    sub_pos.mpr (lt_of_le_of_ne (hwC.2.1 _) hn.2.1.2)
  have hj : 0 < d * pairW μ μ x - w x := sub_pos.mpr
    (lt_of_le_of_ne (hwC.2.2 _) hn.2.2)
  obtain ⟨b,hb,h1,h2,h3,h4⟩ : ∃ b : ℝ, 0 < b ∧ b ≤ 1 - tot w ∧
      b ≤ m * μ x.1 - mapW w Prod.fst x.1 ∧
      b ≤ m * μ x.2 - mapW w Prod.snd x.2 ∧ b ≤ d * pairW μ μ x - w x := by
    let b := min (min (1 - tot w) (m * μ x.1 - mapW w Prod.fst x.1))
      (min (m * μ x.2 - mapW w Prod.snd x.2) (d * pairW μ μ x - w x))
    refine ⟨b, lt_min (lt_min (sub_pos.mpr hw') hg) (lt_min hi hj), ?_,?_,?_,?_⟩
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hmap (f : α × α → α) (y : α) : mapW (incW w x b) f y =
      mapW w f y + b * ind (f x = y) := incW_pr w x b _
  have hm : incW w x b ∈ T := by
    refine ⟨⟨fun _ => add_nonneg (hwL.nz _) (mul_nonneg hb.le (ind_nonneg _)),?_⟩,
      ⟨fun y => ?_, fun y => ?_, fun p => ?_⟩, fun y hy => ?_⟩
    · rw [incW_tot]; linarith only [h1]
    · by_cases h : x.1 = y
      · subst y
        rw [hmap]
        simp only [ind_true, mul_one]
        linarith only [h2]
      · rw [hmap, ind_zero h, mul_zero, add_zero]
        exact hwC.1 y
    · by_cases h : x.2 = y
      · subst y
        rw [hmap]
        simp only [ind_true, mul_one]
        linarith only [h3]
      · rw [hmap, ind_zero h, mul_zero, add_zero]
        exact hwC.2.1 y
    · by_cases h : p = x
      · subst p
        simp only [incW, ind_true, mul_one]
        linarith only [h4]
      · rw [incW, ind_zero h, mul_zero, add_zero]
        exact hwC.2.2 p
    · have h : y ≠ x := fun he => hy (he.symm ▸ hx)
      rw [incW, hw.2.2 y hy, ind_zero h, mul_zero, add_zero]
  have hle : tot (incW w x b) ≤ tot w := hwmax hm
  rw [incW_tot] at hle
  linarith only [hb, hle]

end HadwigerCounterexample

end

end OAI
