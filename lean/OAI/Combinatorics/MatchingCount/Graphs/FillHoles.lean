import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.AffineWeights

namespace OAI

namespace MatchingFPRAS.Switching
open Finset
open scoped Classical symmDiff

variable {V : Type*}
theorem mate_mem_holes_iff [DecidableEq V] (m : Mate V) (S : Finset V)
    (hm : HasHoles m S) (v : V) : m.1 v ∈ S ↔ v ∈ S := by
  rw [← hm (m.1 v), ← hm v, mate_mate]
  exact eq_comm

noncomputable def fillHoles [Fintype V] [DecidableEq V] (m q : Mate V) (S : Finset V)
    (hm : HasHoles m S) (hq : HasHoles q Sᶜ) : Mate V := by
  classical
  refine ⟨fun v => if v ∈ S then q.1 v else m.1 v, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · have hqv : q.1 v ∈ S := by
      have h := mate_mem_holes_iff q Sᶜ hq v
      have he : q.1 v ∈ S ↔ v ∈ S := by
        simpa only [Finset.mem_compl, not_iff_not] using h
      exact he.mpr hv
    simp [hv,hqv,mate_mate]
  · have hmv : m.1 v ∉ S := fun h => hv ((mate_mem_holes_iff m S hm v).mp h)
    simp [hv,hmv,mate_mate]

@[simp] theorem fillHoles_apply [Fintype V] [DecidableEq V] (m q : Mate V) (S : Finset V)
    (hm : HasHoles m S) (hq : HasHoles q Sᶜ) (v : V) :
    (fillHoles m q S hm hq).1 v = if v ∈ S then q.1 v else m.1 v := rfl

theorem fillHoles_perfect [Fintype V] [DecidableEq V] (m q : Mate V) (S : Finset V)
    (hm : HasHoles m S) (hq : HasHoles q Sᶜ) : HasHoles (fillHoles m q S hm hq) ∅ := by
  classical
  intro v
  simp only [fillHoles_apply, Finset.notMem_empty, iff_false]
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv]
    intro he
    exact (Finset.mem_compl.mp ((hq v).mp he)) hv
  · rw [ite_eq_right hv]
    intro he
    exact hv ((hm v).mp he)

theorem fillHoles_injective [Fintype V] [DecidableEq V] (q : Mate V) (S : Finset V)
    (hq : HasHoles q Sᶜ) : Function.Injective
      (fun m : {m : Mate V // HasHoles m S} => fillHoles m.1 q S m.2 hq) := by
  classical
  intro m n he
  apply Subtype.ext
  apply Subtype.ext
  funext v
  by_cases hv : v ∈ S
  · exact ((m.2 v).mpr hv).trans ((n.2 v).mpr hv).symm
  · have h := congrArg (fun r : Mate V => r.1 v) he
    simpa [hv] using h

theorem fillHoles_weight_le [Fintype V] [LinearOrder V]
    (w d u : V → V → ℝ) (hw : ∀ a b, 0 ≤ w a b) (hd : ∀ a b, 0 ≤ d a b)
    (hwu : ∀ a b, w a b ≤ u a b) (hdu : ∀ a b, d a b ≤ u a b)
    (m q : Mate V) (S : Finset V) (hm : HasHoles m S) (hq : HasHoles q Sᶜ) :
    weight w m * weight d q ≤ weight u (fillHoles m q S hm hq) := by
  classical
  unfold weight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro v _
    exact mul_nonneg (by split_ifs; exact hw _ _; norm_num)
      (by split_ifs; exact hd _ _; norm_num)
  · intro v _
    rw [fillHoles_apply]
    by_cases hv : v ∈ S
    · have hmfix := (hm v).mpr hv
      simp only [hv, ite_true, hmfix, lt_self_iff_false, ite_false, one_mul]
      split_ifs
      · exact hdu _ _
      · rfl
    · have hqfix := (hq v).mpr (Finset.mem_compl.mpr hv)
      simp only [hv, ite_false, hqfix, lt_self_iff_false, mul_one]
      split_ifs
      · exact hwu _ _
      · rfl

theorem fillHoles_partition_le [Fintype V] [LinearOrder V]
    (w d u : V → V → ℝ) (hw : ∀ a b, 0 ≤ w a b) (hd : ∀ a b, 0 ≤ d a b)
    (hwu : ∀ a b, w a b ≤ u a b) (hdu : ∀ a b, d a b ≤ u a b)
    (q : Mate V) (S : Finset V) (hq : HasHoles q Sᶜ) :
    partition w S * weight d q ≤ partition u ∅ := by
  classical
  let f : Mate V → Mate V := fun m =>
    if hm : HasHoles m S then fillHoles m q S hm hq else m
  have hi : Set.InjOn f (matchings S) := by
    intro m hm n hn he
    have hm' := (mem_matchings m S).mp hm
    have hn' := (mem_matchings n S).mp hn
    have h : (⟨m,hm'⟩ : {m : Mate V // HasHoles m S}) = ⟨n,hn'⟩ :=
      fillHoles_injective q S hq (by simpa [f,hm',hn'] using he)
    exact congrArg Subtype.val h
  have hsub : (matchings S).image f ⊆ matchings ∅ := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    have hn' := (mem_matchings n S).mp hn
    simp only [f,dite_eq_left hn',mem_matchings]
    exact fillHoles_perfect n q S hn' hq
  calc
    partition w S * weight d q = ∑ m ∈ matchings S, weight w m * weight d q :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ m ∈ matchings S, weight u (f m) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm' := (mem_matchings m S).mp hm
      simpa [f,hm'] using fillHoles_weight_le w d u hw hd hwu hdu m q S hm' hq
    _ = ∑ m ∈ (matchings S).image f, weight u m := (Finset.sum_image hi).symm
    _ ≤ partition u ∅ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ => weight_nonneg u (fun a b => (hw a b).trans (hwu a b)) m)

theorem mate_edge_count [Fintype V] [LinearOrder V] (q : Mate V) (S : Finset V)
    (hq : HasHoles q Sᶜ) :
    2 * (Finset.univ.filter (fun v => v < q.1 v)).card = S.card := by
  let L := Finset.univ.filter (fun v => v < q.1 v)
  let R := Finset.univ.filter (fun v => q.1 v < v)
  have himg : L.image q.1 = R := by
    ext v
    simp only [Finset.mem_image, L,R,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a,ha,rfl⟩
      simpa using ha
    · intro hv
      exact ⟨q.1 v,by simpa using hv,mate_mate q v⟩
  have hcard : L.card = R.card := by
    rw [← himg]
    exact (Finset.card_image_of_injective L q.2.injective).symm
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro v hl hr
    have hl' : v < q.1 v := (Finset.mem_filter.mp hl).2
    have hr' : q.1 v < v := (Finset.mem_filter.mp hr).2
    exact (lt_asymm hl' hr')
  have hunion : L ∪ R = S := by
    ext v
    simp only [L,R,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← ne_iff_lt_or_gt]
    have h := hq v
    simp only [Finset.mem_compl] at h
    simpa only [ne_eq, eq_comm, not_not] using (not_congr h)
  have hc := Finset.card_union_of_disjoint hdis
  rw [hunion,← hcard] at hc
  change 2 * L.card = S.card
  omega

theorem weight_div_const [Fintype V] [LinearOrder V]
    (w : V → V → ℝ) (c : ℝ) (q : Mate V) (S : Finset V) (hq : HasHoles q Sᶜ) :
    weight (fun a b => w a b / c) q = weight w q / c^(S.card/2) := by
  have hc : (Finset.univ.filter (fun v => v < q.1 v)).card = S.card/2 := by
    have := mate_edge_count q S hq
    omega
  unfold weight
  rw [← Finset.prod_filter, ← Finset.prod_filter, Finset.prod_div_distrib]
  simp only [Finset.prod_const, hc]

theorem pairing_exists [Fintype V] [DecidableEq V] (S : Finset V) (hS : Even S.card) :
    ∃ q : Mate V, HasHoles q Sᶜ := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hEmpty : S = ∅
    · subst S
      refine ⟨⟨id,fun _ => rfl⟩,?_⟩
      intro v
      simp
    · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hcardpos := Finset.card_pos.mpr (show S.Nonempty from ⟨a,ha⟩)
      have hcard2 : 2 ≤ S.card := by obtain ⟨k,hk⟩ := hS; omega
      have herase : (S.erase a).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem ha]
        omega
      obtain ⟨b,hb⟩ := herase
      have hba := (Finset.mem_erase.mp hb).1
      have hbS := (Finset.mem_erase.mp hb).2
      let T := S \ {a,b}
      have hTcard : T.card + 2 = S.card := by
        have h := sdiff_pair_card S a b ha hbS hba.symm
        change T.card = S.card - 2 at h
        omega
      have hTeven : Even T.card := by
        obtain ⟨k,hk⟩ := hS
        refine ⟨k-1,?_⟩
        omega
      have hTsub : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.sdiff_subset,by intro he; have := congrArg Finset.card he; omega⟩
      obtain ⟨q,hq⟩ := ih T hTsub hTeven
      have haT : a ∈ Tᶜ := by simp [T]
      have hbT : b ∈ Tᶜ := by simp [T]
      refine ⟨withEdge q a b,?_⟩
      have hh := withEdge_holes q Tᶜ hq a b haT hbT hba.symm
      have he : Tᶜ \ {a,b} = Sᶜ := by
        ext v
        simp only [T,Finset.mem_sdiff,Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton]
        have hsub : ({a,b} : Finset V) ⊆ S := by
          intro x hx
          simp only [Finset.mem_insert,Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        constructor
        · intro h
          tauto
        · intro hv
          constructor
          · tauto
          · intro hvp
            exact hv (hsub (by simpa using hvp))
      rwa [he] at hh

noncomputable def pairingCapacity [Fintype V] [LinearOrder V]
    (B : V → V → ℝ) (S : Finset V) (hS : Even S.card) : ℝ :=
  (matchings Sᶜ).sup' (by
    obtain ⟨q,hq⟩ := pairing_exists S hS
    exact ⟨q,(mem_matchings q Sᶜ).mpr hq⟩) (weight B)

theorem logical_hole_bound [Fintype V] [LinearOrder V]
    (hn : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hz : 0 < partition w ∅)
    (hrlo : ∀ a, (1:ℝ)/4 ≤ rowMax hn w a) (hrhi : ∀ a, rowMax hn w a ≤ 1)
    (S : Finset V) (hS : Even S.card) :
    holeRatio w S * pairingCapacity (bottleneck w) S hS ≤
      2 * holeScale V ^ (S.card / 2) := by
  classical
  obtain ⟨q,hq,hmax⟩ := Finset.exists_mem_eq_sup'
    (show (matchings Sᶜ).Nonempty from by
      obtain ⟨q,hq⟩ := pairing_exists S hS
      exact ⟨q,(mem_matchings _ _).mpr hq⟩) (weight (bottleneck w))
  have hq' := (mem_matchings q Sᶜ).mp hq
  have hc : pairingCapacity (bottleneck w) S hS = weight (bottleneck w) q := hmax
  let d := holeAugmentation w
  let u := affineWeights w d 1
  have hd : ∀ a b, 0 ≤ d a b := holeAugmentation_nonneg w
  have hfill := fillHoles_partition_le w d u hw hd
    (fun a b => by change w a b ≤ w a b + 1*d a b; linarith [hd a b])
    (fun a b => by change d a b ≤ w a b + 1*d a b; linarith [hw a b]) q S hq'
  have hinfl := logical_inflation hn w hw hz hrlo hrhi
  have hdiv : weight d q = weight (bottleneck w) q / holeScale V ^ (S.card/2) :=
    weight_div_const (bottleneck w) (holeScale V) q S hq'
  rw [hdiv] at hfill
  rw [hc,holeRatio]
  have hpow : 0 < holeScale V ^ (S.card/2) := pow_pos holeScale_pos _
  have hmain : partition w S * weight (bottleneck w) q ≤
      2 * partition w ∅ * holeScale V ^ (S.card/2) := by
    have h' := hfill.trans hinfl.le
    rw [← mul_div_assoc, div_le_iff₀ hpow] at h'
    exact h'
  rw [div_mul_eq_mul_div, div_le_iff₀ hz]
  nlinarith only [hmain]

end MatchingFPRAS.Switching

end OAI
