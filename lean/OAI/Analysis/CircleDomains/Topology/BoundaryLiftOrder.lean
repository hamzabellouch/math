import OAI.Analysis.CircleDomains.Topology.CircleLifts
import OAI.Analysis.CircleDomains.Transfer.PeriodicFilling
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone

namespace OAI

/-! An embedded circle has a monotone or antitone normalized real boundary
lift, with one turn in absolute value. This fixes the orientation issue for
the physical collar without differentiating its topological disk chart. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem strictMonoOn_Icc_of_continuous_strictMonoOn_Ioo
    (q : ℝ → ℝ) (hq : Continuous q) (hm : StrictMonoOn q (Ioo (0 : ℝ) 1)) :
    StrictMonoOn q (Icc (0 : ℝ) 1) := by
  have h0 : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨zero_le_one, le_rfl⟩
  have hm0 := hm.monotoneOn.insert_of_continuousWithinAt
    (mem_closure_iff_clusterPt.mp h0) hq.continuousAt.continuousWithinAt
  have hm1 := hm0.insert_of_continuousWithinAt
    (mem_closure_iff_clusterPt.mp ((closure_mono (subset_insert 0 _)) h1))
    hq.continuousAt.continuousWithinAt
  have hs : insert (1 : ℝ) (insert 0 (Ioo (0 : ℝ) 1)) = Icc 0 1 := by
    ext x
    simp only [mem_insert_iff, mem_Ioo, mem_Icc]
    constructor
    · rintro (rfl | rfl | hx)
      · exact ⟨zero_le_one, le_rfl⟩
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨hx.1.le, hx.2.le⟩
    · intro hx
      by_cases h0x : x = 0
      · exact Or.inr (Or.inl h0x)
      by_cases h1x : x = 1
      · exact Or.inl h1x
      exact Or.inr (Or.inr ⟨lt_of_le_of_ne hx.1 (Ne.symm h0x), lt_of_le_of_ne hx.2 h1x⟩)
  rw [hs] at hm1
  intro x hx y hy hxy
  obtain ⟨a, hxa, hay⟩ := exists_between hxy
  obtain ⟨b, hab, hby⟩ := exists_between hay
  have ha : a ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hx.1 hxa, hay.trans_le hy.2⟩
  have hb : b ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hab, hby.trans_le hy.2⟩
  exact (hm1 hx ⟨ha.1.le, ha.2.le⟩ hxa.le).trans_lt
    ((hm ha hb hab).trans_le (hm1 ⟨hb.1.le, hb.2.le⟩ hy hby.le))

 theorem positive_boundary_lift_one_turn
    (q : ℝ → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hinj : InjOn (fun t => (q t : UnitAddCircle)) (Ico (0 : ℝ) 1))
    (hloop : (q 1 : UnitAddCircle) = (q 0 : UnitAddCircle)) (hpos : 0 < q 1) :
    q 1 = 1 := by
  obtain ⟨k, hk⟩ := (addCircle_eq_iff_exists_int 1 (q 1) (q 0)).mp hloop
  have hk' : q 1 = (k : ℝ) := by simpa only [hq0, zero_add, mul_one] using hk
  have hkpos : (0 : ℤ) < k := by exact_mod_cast (hk' ▸ hpos)
  have hle : (1 : ℝ) ≤ q 1 := by rw [hk']; exact_mod_cast (Int.add_one_le_iff.mpr hkpos)
  apply le_antisymm _ hle
  by_contra hn
  have hlt : 1 < q 1 := lt_of_not_ge hn
  obtain ⟨t, ht, hqt⟩ := intermediate_value_Icc zero_le_one hq.continuousOn
    (show (1 : ℝ) ∈ Icc (q 0) (q 1) by rw [hq0]; exact ⟨zero_le_one, hlt.le⟩)
  have ht0 : t ≠ 0 := by intro h; rw [h, hq0] at hqt; norm_num at hqt
  have ht1 : t ≠ 1 := by intro h; rw [h] at hqt; linarith
  have heq : (q t : UnitAddCircle) = (q 0 : UnitAddCircle) := by
    rw [hqt, hq0]
    exact (addCircle_eq_iff_exists_int 1 (1 : ℝ) 0).mpr ⟨1, by norm_num⟩
  exact ht0 (hinj ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ ⟨le_rfl, zero_lt_one⟩ heq)

 theorem boundary_lift_order_and_period
    (q : ℝ → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hinj : InjOn (fun t => (q t : UnitAddCircle)) (Ico (0 : ℝ) 1))
    (hloop : (q 1 : UnitAddCircle) = (q 0 : UnitAddCircle)) :
    (StrictMonoOn q (Icc (0 : ℝ) 1) ∧ q 1 = 1) ∨
      (StrictAntiOn q (Icc (0 : ℝ) 1) ∧ q 1 = -1) := by
  have hqi : InjOn q (Ioo (0 : ℝ) 1) := by
    intro x hx y hy heq
    exact hinj (Ioo_subset_Ico_self hx) (Ioo_subset_Ico_self hy) (congrArg (fun r : ℝ => (r : UnitAddCircle)) heq)
  rcases hq.continuousOn.strictMonoOn_of_injOn_Ioo zero_lt_one hqi with hm | ha
  · have hm' := strictMonoOn_Icc_of_continuous_strictMonoOn_Ioo q hq hm
    refine Or.inl ⟨hm', positive_boundary_lift_one_turn q hq hq0 hinj hloop ?_⟩
    simpa only [hq0] using hm' (left_mem_Icc.mpr zero_le_one)
      (right_mem_Icc.mpr zero_le_one) zero_lt_one
  · have hn : StrictMonoOn (fun t => -q t) (Ioo (0 : ℝ) 1) := by
      intro x hx y hy hxy
      exact neg_lt_neg (ha hx hy hxy)
    have hn' := strictMonoOn_Icc_of_continuous_strictMonoOn_Ioo _ hq.neg hn
    have hni : InjOn (fun t => ((-q t : ℝ) : UnitAddCircle)) (Ico (0 : ℝ) 1) := by
      intro x hx y hy heq
      apply hinj hx hy
      exact neg_injective (by simpa only [AddCircle.coe_neg] using heq)
    have hp : 0 < -q 1 := by
      have hh : -q 0 < -q 1 := hn' (left_mem_Icc.mpr zero_le_one)
        (right_mem_Icc.mpr zero_le_one) zero_lt_one
      simpa only [hq0, neg_zero] using hh
    have hperiod := positive_boundary_lift_one_turn (fun t => -q t) hq.neg
      (by simp only [hq0, neg_zero]) hni
      (by simpa only [AddCircle.coe_neg] using congrArg Neg.neg hloop) hp
    refine Or.inr ⟨?_, by linarith⟩
    intro x hx y hy hxy
    exact neg_lt_neg_iff.mp (hn' hx hy hxy)

 theorem exists_ordered_circle_boundary_lift
    (g : ℝ → UnitAddCircle) (hg : Continuous g) (hperiod : Function.Periodic g 1)
    (hg0 : g 0 = 0) (hinj : InjOn g (Ico (0 : ℝ) 1)) :
    ∃ q : ℝ → ℝ, Continuous q ∧ q 0 = 0 ∧ (∀ t, (q t : UnitAddCircle) = g t) ∧
      ((StrictMonoOn q (Icc (0 : ℝ) 1) ∧ q 1 = 1) ∨
        (StrictAntiOn q (Icc (0 : ℝ) 1) ∧ q 1 = -1)) := by
  let : ContractibleSpace (univ : Set ℝ) := convex_univ.contractibleSpace Set.univ_nonempty
  let : LocallyPathConnectedSpace (univ : Set ℝ) := isOpen_univ.locallyPathConnectedSpace
  obtain ⟨q, hq, hq0, hqp⟩ := exists_continuous_circle_lift g hg.continuousOn (mem_univ 0) 0
    (by simpa only [AddCircle.coe_zero] using hg0.symm)
  have hqp' : ∀ t, (q t : UnitAddCircle) = g t := fun t => hqp t (mem_univ t)
  have hqi : InjOn (fun t => (q t : UnitAddCircle)) (Ico (0 : ℝ) 1) := by
    intro x hx y hy heq
    apply hinj hx hy
    simpa only [hqp'] using heq
  refine ⟨q, continuousOn_univ.mp hq, hq0, hqp', ?_⟩
  apply boundary_lift_order_and_period q (continuousOn_univ.mp hq) hq0 hqi
  rw [hqp', hqp', hperiod.eq]

end CircleDomainRigidity

end

end OAI
