import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EnumeratedBest

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus

lemma correct_entry_exists (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (hk : 0 < kappa) (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (w : V) (hw : w ∈ D) :
    ∃ e : Entry (firstSize kappa) (geometricCap kappa hk) (thirdSize kappa C.bad.card),
    ∃ R : ℝ,
      menuRadius D hD (comparisonCost D C.assign) kappa C.bad.card
        (firstSize kappa) (geometricCap kappa hk) (thirdSize kappa C.bad.card) s w e = some R ∧
      0 < R ∧ dist w (C.assign w) ≤ R ∧
      R ≤ (1+kappa)*dist w (C.assign w)+
        kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w ∧
      (∀ j, e = .inr (.inr j) →
        10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w (C.assign w) ∧
        (∀ z ∈ s.leaves, 10*dist w (C.assign w) < dist w z.1+z.2) ∧
        j.val+1 = Nat.ceil (dist w (C.assign w)/
          (kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w))) := by
  let q := Population.radius D hD (comparisonCost D C.assign) C.bad.card w
  let r := dist w (C.assign w)
  have hq : 0 < q := Population.radius_pos D hD _ _ w hP hm
  by_cases hsmall : r ≤ 10*q
  · have ha := first_menu_available kappa q r hk hq dist_nonneg hsmall
    let j : Fin (firstSize kappa) := ⟨upwardIndex kappa q r-1, by omega⟩
    have hj : j.val+1 = upwardIndex kappa q r := by dsimp [j]; omega
    refine ⟨.inl j, additiveRadius kappa q (upwardIndex kappa q r), ?_,
      additiveRadius_pos kappa q _ hk hq (by omega), ha.2.2.1, ha.2.2.2, ?_⟩
    · simp only [menuRadius, additiveRadius, ← Nat.cast_add_one, hj, q]
    · intro j' he
      contradiction
  · have hr : 0 < r := lt_trans (mul_pos (by norm_num) hq) (lt_of_not_ge hsmall)
    by_cases hleaf : ∃ d, nearestLeaf s w = some d ∧ d ≤ 10*r
    · obtain ⟨d,hd,hdub⟩ := hleaf
      obtain ⟨e,he,hlo,hhi⟩ := geometric_menu_available kappa d r hk hr
        (C.correct_nearestLeaf_lower hD kappa s hs w hw d hd) hdub
      refine ⟨.inr (.inl ⟨e,by omega⟩),d/(1+kappa)^e,?_,hr.trans_le hlo,hlo,?_,?_⟩
      · simp only [menuRadius, hd, Option.map_some]
      · have h0 : 0 ≤ kappa*q := mul_nonneg hk.le hq.le
        linarith
      · intro j heq
        cases Sum.inr.inj heq
    · have hb := C.single_radius_ratio hD hP hm w hw (lt_of_not_ge hsmall)
      have ha := third_menu_available kappa q r C.bad.card hk hq hr hb
      let j : Fin (thirdSize kappa C.bad.card) := ⟨Nat.ceil (r/(kappa*q))-1,by omega⟩
      have hj : j.val+1 = Nat.ceil (r/(kappa*q)) := by dsimp [j]; omega
      refine ⟨.inr (.inr j),additiveRadius kappa q (Nat.ceil (r/(kappa*q))),?_,
        additiveRadius_pos kappa q _ hk hq (by omega),ha.2.2.1,ha.2.2.2,?_⟩
      · simp only [menuRadius, additiveRadius, ← Nat.cast_add_one, hj, q, r]
      · intro j' heq
        have he : j = j' := Sum.inr.inj (Sum.inr.inj heq)
        subst j'
        refine ⟨lt_of_not_ge hsmall,?_,hj⟩
        intro z hz
        obtain ⟨d,hd,hle⟩ := nearestLeaf_of_mem s w z hz
        have hdgt : 10*r < d := lt_of_not_ge (fun h => hleaf ⟨d,hd,h⟩)
        exact hdgt.trans_le hle

lemma third_ball_disjoint (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (_hk : 0 ≤ kappa) (hk1 : kappa ≤ 1)
    (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (w : V) (hw : w ∈ D) (z : V × ℝ) (hz : z ∈ s.leaves)
    (hzthird : 10*Population.radius D hD (comparisonCost D C.assign) C.bad.card z.1 < dist z.1 (C.assign z.1))
    (hwthird : 10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w (C.assign w))
    (hwleaf : 10*dist w (C.assign w) < dist w z.1+z.2) :
    Disjoint (Population.ball D z.1 (Population.radius D hD (comparisonCost D C.assign) C.bad.card z.1))
      (Population.ball D w (Population.radius D hD (comparisonCost D C.assign) C.bad.card w)) := by
  apply Finset.disjoint_left.mpr
  intro p hpz hpw
  have hzp := (Finset.mem_filter.mp hpz).2
  have hwp := (Finset.mem_filter.mp hpw).2
  have ht := dist_triangle z.1 p w
  rw [dist_comm p w] at ht
  have ht' := C.comparison_triangle z.1 w (hs.2.2 z hz).1 hw
  have hR := (hs.2.2 z hz).2.2.2.2.2
  have hq := Population.radius_pos D hD (comparisonCost D C.assign) C.bad.card z.1 hP hm
  have hm1 := mul_le_mul_of_nonneg_right hk1 (dist_nonneg (x := z.1) (y := C.assign z.1))
  have hm2 := mul_le_mul_of_nonneg_right hk1 hq.le
  rw [dist_comm w z.1] at hwleaf
  nlinarith

noncomputable def nearEligible (C : Comparison D S O) (s : State V) : Finset V :=
  D.filter (fun p => C.assign p ∈ C.bad \ C.covered s ∧
    dist p (C.assign p) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign p))

noncomputable def removalEligible (C : Comparison D S O) (Δ : ℝ) (s : State V) : Finset V :=
  D.filter (fun p => ∃ o ∈ C.nonproxy \ s.deleted, chosen S Δ s p = realTag o)

lemma nearTotal_eq (C : Comparison D S O) (Δ : ℝ) (s : State V) :
    C.nearTotal Δ s = ∑ p ∈ C.nearEligible s, reference S Δ s p := by
  classical
  simp only [nearTotal, near, cluster, Finset.filter_filter, nearEligible, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have he : ∀ o, (if C.assign p = o ∧ dist p o ≤ (6/5 : ℝ)*clusterMean D C.assign o
      then reference S Δ s p else 0) =
      (if o = C.assign p then
        (if dist p (C.assign p) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign p)
        then reference S Δ s p else 0) else 0) := by
    intro o
    by_cases h : o = C.assign p
    · subst o
      simp
    · simp [h, Ne.symm h]
  simp_rw [he]
  simp only [Finset.sum_ite_eq']
  split_ifs <;> simp_all

lemma nearTotal_nonneg (C : Comparison D S O) (hD : D.Nonempty) (kappa Δ : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ) : 0 ≤ C.nearTotal Δ s := by
  rw [C.nearTotal_eq]
  exact Finset.sum_nonneg (fun p _ => reference_nonneg S Δ s p hΔ
    (C.correct_radii_nonneg hD kappa s hs))

lemma removalTotal_nonneg (C : Comparison D S O) (hD : D.Nonempty) (kappa Δ : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ) : 0 ≤ C.removalTotal Δ s :=
  Finset.sum_nonneg (fun p _ => reference_nonneg S Δ s p hΔ
    (C.correct_radii_nonneg hD kappa s hs))

lemma nearTotal_le_weight (C : Comparison D S O) (hD : D.Nonempty) (kappa Δ : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ) :
    C.nearTotal Δ s ≤ totalWeight D S Δ s := by
  rw [C.nearTotal_eq]
  have he : (∑ p ∈ C.nearEligible s, reference S Δ s p) =
      ∑ p ∈ C.nearEligible s, clientWeight S Δ s p :=
    Finset.sum_congr rfl (fun p _ => (clientWeight_eq S Δ s p hΔ
      (C.correct_radii_nonneg hD kappa s hs)).symm)
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => clientWeight_nonneg S Δ s p)

lemma removalTotal_le_weight (C : Comparison D S O) (hD : D.Nonempty) (kappa Δ : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ) :
    C.removalTotal Δ s ≤ totalWeight D S Δ s := by
  have he : C.removalTotal Δ s = ∑ p ∈ C.removalEligible Δ s, clientWeight S Δ s p :=
    Finset.sum_congr rfl (fun p _ => (clientWeight_eq S Δ s p hΔ
      (C.correct_radii_nonneg hD kappa s hs)).symm)
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => clientWeight_nonneg S Δ s p)

def Terminal (C : Comparison D S O) (kappa Δ : ℝ) (s : State V) : Prop :=
  C.nearTotal Δ s ≤ kappa*comparisonCost D C.assign ∧
    C.removalTotal Δ s ≤ kappa*comparisonCost D C.assign

noncomputable def counter (C : Comparison D S O) (s : State V) : ℕ :=
  2*C.bad.card-(s.leaves.length+s.deleted.card)

lemma counter_zero_terminal (C : Comparison D S O) (hD : D.Nonempty) (kappa Δ : ℝ)
    (s : State V) (hs : C.Correct hD kappa s) (hk : 0 ≤ kappa)
    (hz : C.counter s = 0) : C.Terminal kappa Δ s := by
  have hlen := C.correct_lengths hD kappa s hs
  have he1 : s.leaves.length = C.bad.card := by unfold counter at hz; omega
  have he2 : s.deleted.card = C.bad.card := by unfold counter at hz; omega
  have hcard : (C.covered s).card = C.bad.card := by
    rw [covered, List.toFinset_card_of_nodup hs.2.1, List.length_map, he1]
  have hcov : C.covered s = C.bad := Finset.eq_of_subset_of_card_le
    (C.correct_covered_subset hD kappa s hs) hcard.ge
  have hdel : s.deleted = C.nonproxy := Finset.eq_of_subset_of_card_le hs.1
    (by rw [he2, C.nonproxy_card])
  have hP : 0 ≤ comparisonCost D C.assign := Finset.sum_nonneg (fun p _ => dist_nonneg)
  have hT : C.nearTotal Δ s = 0 := by simp only [nearTotal, hcov, Finset.sdiff_self, Finset.sum_empty]
  have hI : C.removalTotal Δ s = 0 := by simp [removalTotal, hdel]
  exact ⟨hT ▸ mul_nonneg hk hP, hI ▸ mul_nonneg hk hP⟩

lemma eligible_ball_correct (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (hw : w ∈ C.nearEligible s) (R : ℝ) (hR : 0 < R)
    (hlo : dist w (C.assign w) ≤ R)
    (hhi : R ≤ (1+kappa)*dist w (C.assign w)+
      kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w) :
    C.Correct hD kappa (s.add w R) := by
  obtain ⟨hwD,hb,hnear⟩ := Finset.mem_filter.mp hw
  exact C.correct_add hD kappa s hs w R hwD (Finset.mem_sdiff.mp hb).1
    (Finset.mem_sdiff.mp hb).2 hnear hR hlo hhi

lemma counter_ball_decreases (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (w : V) (R : ℝ)
    (hs' : C.Correct hD kappa (s.add w R)) : C.counter (s.add w R) < C.counter s := by
  have hlen := C.correct_lengths hD kappa (s.add w R) hs'
  simp only [State.add, List.length_append, List.length_singleton] at hlen
  simp only [counter, State.add, List.length_append, List.length_singleton]
  omega

lemma counter_remove_decreases (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (v : V) (hv : v ∉ s.deleted)
    (hs' : C.Correct hD kappa (s.remove v)) : C.counter (s.remove v) < C.counter s := by
  have hlen := C.correct_lengths hD kappa (s.remove v) hs'
  have hcard : (s.remove v).deleted.card = s.deleted.card+1 := by
    exact @Finset.card_insert_of_notMem V s.deleted v (fun a b => Classical.propDecidable (a = b)) hv
  rw [hcard] at hlen
  unfold counter
  rw [hcard]
  change 2*C.bad.card-(s.leaves.length+(s.deleted.card+1)) < _
  change (s.leaves.length ≤ C.bad.card ∧ s.deleted.card+1 ≤ C.bad.card) at hlen
  omega

open scoped Classical

noncomputable def conditionalClients (D S : Finset V) (Δ : ℝ) (s : State V)
    (E : Finset V) (hE : E ⊆ D) (T : ℝ) (hT : 0 < T)
    (he : ∑ p ∈ E, clientWeight S Δ s p = T) : Guided.Kernel Unit D := by
  classical
  refine ⟨fun _ w => if w.val ∈ E then clientWeight S Δ s w/T else 0, ?_, ?_⟩
  · intro u w
    split_ifs
    · exact div_nonneg (clientWeight_nonneg S Δ s w) hT.le
    · exact le_rfl
  · intro u
    have hh : (∑ w : D, if w.val ∈ E then clientWeight S Δ s w/T else 0) =
        (∑ w : D, if w.val ∈ E then clientWeight S Δ s w else 0)/T := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
    rw [hh,Finset.sum_coe_sort D (fun p => if p ∈ E then clientWeight S Δ s p else 0),
      ← Finset.sum_filter,Finset.filter_mem_eq_of_subset hE,he]
    exact div_self (ne_of_gt hT)

lemma conditionalClients_pos (D S : Finset V) (Δ : ℝ) (s : State V)
    (E : Finset V) (hE : E ⊆ D) (T : ℝ) (hT : 0 < T)
    (he : ∑ p ∈ E, clientWeight S Δ s p = T) (w : D)
    (hw : 0 < (conditionalClients D S Δ s E hE T hT he).weight () w) :
    w.val ∈ E ∧ 0 < clientWeight S Δ s w := by
  change 0 < (if w.val ∈ E then clientWeight S Δ s w/T else 0) at hw
  by_cases h : w.val ∈ E
  · have hh : 0 < clientWeight S Δ s w/T := by simpa only [ite_eq_left h] using hw
    rcases div_pos_iff.mp hh with ⟨hp,_⟩ | ⟨_,htneg⟩
    · exact ⟨h,hp⟩
    · linarith
  · simp only [ite_eq_right h,lt_self_iff_false] at hw

noncomputable def mainKappa : ℝ := 1/1000000
lemma mainKappa_pos : 0 < mainKappa := by norm_num [mainKappa]
lemma mainKappa_le_one : mainKappa ≤ 1 := by norm_num [mainKappa]
abbrev MainEntry (m : ℕ) := Entry (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos)
  (thirdSize mainKappa m)
abbrev MainAction (D : Finset V) (m : ℕ) :=
  Action D (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m)

noncomputable def prescribedEntry (C : Comparison D S O) (hD : D.Nonempty)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (w : D) : MainEntry C.bad.card :=
  if hs : C.Correct hD mainKappa s then
    (C.correct_entry_exists hD mainKappa mainKappa_pos s hs hP hm w w.property).choose
  else .inl ⟨0,by unfold firstSize; omega⟩

lemma prescribedEntry_spec (C : Comparison D S O) (hD : D.Nonempty)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (w : D) :
    ∃ R : ℝ,
      menuRadius D hD (comparisonCost D C.assign) mainKappa C.bad.card
        (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
        s w (C.prescribedEntry hD hP hm s w) = some R ∧
      0 < R ∧ dist w.val (C.assign w) ≤ R ∧
      R ≤ (1+mainKappa)*dist w.val (C.assign w)+
        mainKappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w ∧
      (∀ j, C.prescribedEntry hD hP hm s w = .inr (.inr j) →
        10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w.val (C.assign w) ∧
        (∀ z ∈ s.leaves, 10*dist w.val (C.assign w) < dist w.val z.1+z.2) ∧
        j.val+1 = Nat.ceil (dist w.val (C.assign w)/
          (mainKappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w))) := by
  simp only [prescribedEntry,dite_eq_left hs]
  exact (C.correct_entry_exists hD mainKappa mainKappa_pos s hs hP hm w w.property).choose_spec

lemma eligible_near_weight (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (s : State V) (hs : C.Correct hD mainKappa s) :
    (∑ p ∈ C.nearEligible s, clientWeight S Δ s p) = C.nearTotal Δ s := by
  rw [C.nearTotal_eq]
  exact Finset.sum_congr rfl (fun p _ => clientWeight_eq S Δ s p hΔ
    (C.correct_radii_nonneg hD mainKappa s hs))

lemma eligible_removal_weight (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (s : State V) (hs : C.Correct hD mainKappa s) :
    (∑ p ∈ C.removalEligible Δ s, clientWeight S Δ s p) = C.removalTotal Δ s :=
  Finset.sum_congr rfl (fun p _ => clientWeight_eq S Δ s p hΔ
    (C.correct_radii_nonneg hD mainKappa s hs))

noncomputable def activeGuide (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (ht : ¬C.Terminal mainKappa Δ s) :
    Guided.Kernel Unit (MainAction D C.bad.card) :=
  if hball : mainKappa*comparisonCost D C.assign < C.nearTotal Δ s then
    Guided.routed
      (conditionalClients D S Δ s (C.nearEligible s) (Finset.filter_subset _ _)
        (C.nearTotal Δ s) ((mul_pos mainKappa_pos hP).trans hball)
        (C.eligible_near_weight hD Δ hΔ s hs))
      (fun _ w => .inr (.inr (w,C.prescribedEntry hD hP hm s w)))
  else Guided.routed
      (conditionalClients D S Δ s (C.removalEligible Δ s) (Finset.filter_subset _ _)
        (C.removalTotal Δ s)
        (by have hh : mainKappa*comparisonCost D C.assign < C.removalTotal Δ s := by
              by_contra hc
              exact ht ⟨le_of_not_gt hball,le_of_not_gt hc⟩
            exact (mul_pos mainKappa_pos hP).trans hh)
        (C.eligible_removal_weight hD Δ hΔ s hs))
      (fun _ w => .inr (.inl w))

lemma activeGuide_support (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (ht : ¬C.Terminal mainKappa Δ s)
    (a : MainAction D C.bad.card)
    (ha : 0 < (C.activeGuide hD Δ hΔ hP hm s hs ht).weight () a) :
    (mainKappa*comparisonCost D C.assign < C.nearTotal Δ s ∧
      ∃ w : D, a = .inr (.inr (w,C.prescribedEntry hD hP hm s w)) ∧
        w.val ∈ C.nearEligible s) ∨
    (C.nearTotal Δ s ≤ mainKappa*comparisonCost D C.assign ∧
      mainKappa*comparisonCost D C.assign < C.removalTotal Δ s ∧
      ∃ w : D, a = .inr (.inl w) ∧ w.val ∈ C.removalEligible Δ s) := by
  unfold activeGuide at ha
  split_ifs at ha with hb
  · obtain ⟨w,he,hw⟩ := Guided.routed_pos _ _ () a ha
    exact Or.inl ⟨hb,w,he.symm,(conditionalClients_pos _ _ _ _ _ _ _ _ _ w hw).1⟩
  · have hi : mainKappa*comparisonCost D C.assign < C.removalTotal Δ s := by
      by_contra hh
      exact ht ⟨le_of_not_gt hb,le_of_not_gt hh⟩
    obtain ⟨w,he,hw⟩ := Guided.routed_pos _ _ () a ha
    exact Or.inr ⟨le_of_not_gt hb,hi,w,he.symm,(conditionalClients_pos _ _ _ _ _ _ _ _ _ w hw).1⟩

lemma active_weight_pos (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign)
    (s : State V) (hs : C.Correct hD mainKappa s) (ht : ¬C.Terminal mainKappa Δ s) :
    0 < totalWeight D S Δ s := by
  have h0 := mul_pos mainKappa_pos hP
  by_cases hb : mainKappa*comparisonCost D C.assign < C.nearTotal Δ s
  · exact (h0.trans hb).trans_le (C.nearTotal_le_weight hD mainKappa Δ s hs hΔ)
  · have hi : mainKappa*comparisonCost D C.assign < C.removalTotal Δ s := by
      by_contra hh
      exact ht ⟨le_of_not_gt hb,le_of_not_gt hh⟩
    exact (h0.trans hi).trans_le (C.removalTotal_le_weight hD mainKappa Δ s hs hΔ)

lemma update_eligible_ball (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (hW : 0 < totalWeight D S Δ s)
    (w : D) (hw : w.val ∈ C.nearEligible s) :
    ∃ R, update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
        (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
        (some s) (.inr (.inr (w,C.prescribedEntry hD hP hm s w))) = some (s.add w R) ∧
      C.Correct hD mainKappa (s.add w R) ∧ C.counter (s.add w R) < C.counter s := by
  obtain ⟨R,hmenu,hR,hlo,hhi,_⟩ := C.prescribedEntry_spec hD hP hm s hs w
  have hc := C.eligible_ball_correct hD mainKappa s hs w hw R hR hlo hhi
  have hball : (F.filter (fun v => dist w.val v ≤ R)).Nonempty :=
    ⟨C.assign w,Finset.mem_filter.mpr ⟨hOF (C.assigned w w.property),hlo⟩⟩
  refine ⟨R,?_,hc,C.counter_ball_decreases hD mainKappa s w R hc⟩
  simp only [update,ite_eq_left hW,hmenu,ite_eq_left hball,retain,
    ite_eq_left (C.correct_lengths hD mainKappa (s.add w R) hc)]

lemma update_eligible_removal (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (Δ : ℝ) (s : State V) (hs : C.Correct hD mainKappa s)
    (hW : 0 < totalWeight D S Δ s) (w : D) (hw : w.val ∈ C.removalEligible Δ s) :
    ∃ v, v ∈ C.nonproxy \ s.deleted ∧
      update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
        (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
        (some s) (.inr (.inl w)) = some (s.remove v) ∧
      C.Correct hD mainKappa (s.remove v) ∧ C.counter (s.remove v) < C.counter s := by
  obtain ⟨v,hv,hchosen⟩ := (Finset.mem_filter.mp hw).2
  have hc := C.correct_remove hD mainKappa s hs v (Finset.mem_sdiff.mp hv).1
  refine ⟨v,hv,?_,hc,C.counter_remove_decreases hD mainKappa s v (Finset.mem_sdiff.mp hv).2 hc⟩
  simp only [update,ite_eq_left hW,hchosen,realTag,ofLex_toLex,retain,
    ite_eq_left (C.correct_lengths hD mainKappa (s.remove v) hc)]

noncomputable abbrev mainActual (D S : Finset V) (Δ : ℝ) (m : ℕ) :=
  actualKernel D S Δ (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos)
    (thirdSize mainKappa m) (by unfold firstSize; omega) (by unfold thirdSize; omega)

noncomputable def stop (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) : Option (State V) → Prop
  | none => False
  | some s => C.Correct hD mainKappa s ∧ C.Terminal mainKappa Δ s

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
