import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Guide

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

lemma history_ball_before (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i j : Fin n) (hi : i ∈ ballSteps seed) (hij : i < j) :
    ∃ R, ((ballLeader hD (seed i)).val,R) ∈ (C.history hD F Δ n seed j.castSucc).leaves := by
  obtain ⟨R,_,_,he⟩ := C.history_ball hD F hOF Δ hΔ hP hm n seed hseed i hi
  have hmem : ((ballLeader hD (seed i)).val,R) ∈ (C.history hD F Δ n seed i.succ).leaves := by
    rw [he]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hij' : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact hij
  exact ⟨R,List.mem_toFinset.mp (C.history_leaves_mono hD F hOF Δ hΔ hP hm n seed hseed hij'
    (List.mem_toFinset.mpr hmem))⟩

lemma covered_of_leaf (C : Comparison D S O) (s : State V) (w : V) (R : ℝ)
    (hmem : (w,R) ∈ s.leaves) : C.assign w ∈ C.covered s := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(w,R),hmem,rfl⟩)

lemma history_ball_count (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    (ballSteps seed).card ≤ C.bad.card := by
  let center := fun i : Fin n => C.assign (ballLeader hD (seed i))
  have hmemb : ∀ i ∈ ballSteps seed, center i ∈ C.bad \ C.covered (C.history hD F Δ n seed i.castSucc) := by
    intro i hi
    obtain ⟨_,_,hw,_⟩ := C.history_ball hD F hOF Δ hΔ hP hm n seed hseed i hi
    exact (Finset.mem_filter.mp hw).2.1
  have hne : ∀ i ∈ ballSteps seed, ∀ j ∈ ballSteps seed, i < j → center i ≠ center j := by
    intro i hi j hj hij he
    obtain ⟨R,hR⟩ := C.history_ball_before hD F hOF Δ hΔ hP hm n seed hseed i j hi hij
    have hc := C.covered_of_leaf _ _ _ hR
    have hn := (Finset.mem_sdiff.mp (hmemb j hj)).2
    exact hn (he ▸ hc)
  apply Finset.card_le_card_of_injOn center (fun i hi => (Finset.mem_sdiff.mp (hmemb i hi)).1)
  intro i hi j hj he
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hne i hi j hj hij he
  · exact hne j hj i hi hji he.symm

lemma history_third_spec (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin n) (hi : i ∈ thirdSteps seed) :
    let s := C.history hD F Δ n seed i.castSucc
    let w := ballLeader hD (seed i)
    10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w.val (C.assign w) ∧
      (∀ z ∈ s.leaves, 10*dist w.val (C.assign w) < dist w.val z.1+z.2) := by
  dsimp only
  obtain ⟨R,ha,_,_⟩ := C.history_ball hD F hOF Δ hΔ hP hm n seed hseed i ((thirdSteps_subset seed) hi)
  obtain ⟨w,j,hj⟩ := (Finset.mem_filter.mp hi).2
  have he : C.prescribedEntry hD hP hm (C.history hD F Δ n seed i.castSucc)
      (ballLeader hD (seed i)) = .inr (.inr j) := by
    rw [hj] at ha
    simpa only [hj] using (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj ha))).2.symm
  obtain ⟨_,_,_,_,_,hentry⟩ := C.prescribedEntry_spec hD hP hm _
    (C.history_correct hD F hOF Δ hΔ hP hm n seed hseed i.castSucc) (ballLeader hD (seed i))
  exact ⟨(hentry j he).1,(hentry j he).2.1⟩

lemma history_disjoint (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    Set.PairwiseDisjoint (↑(thirdSteps seed)) (fun i => Population.ball D (ballLeader hD (seed i))
      (Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i)))) := by
  have hordered : ∀ i ∈ thirdSteps seed, ∀ j ∈ thirdSteps seed, i < j →
      Disjoint (Population.ball D (ballLeader hD (seed i))
        (Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i))))
        (Population.ball D (ballLeader hD (seed j))
        (Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed j)))) := by
    intro i hi j hj hij
    obtain ⟨R,hR⟩ := C.history_ball_before hD F hOF Δ hΔ hP hm n seed hseed i j
      ((thirdSteps_subset seed) hi) hij
    have hti := C.history_third_spec hD F hOF Δ hΔ hP hm n seed hseed i hi
    have htj := C.history_third_spec hD F hOF Δ hΔ hP hm n seed hseed j hj
    exact C.third_ball_disjoint hD mainKappa mainKappa_pos.le (by norm_num [mainKappa])
      _ (C.history_correct hD F hOF Δ hΔ hP hm n seed hseed j.castSucc) hP hm
      (ballLeader hD (seed j)) (ballLeader hD (seed j)).property
      ((ballLeader hD (seed i)).val,R) hR hti.1 htj.1 (htj.2 _ hR)
  intro i hi j hj hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hordered i hi j hj hij
  · exact (hordered j hj i hi hji).symm

lemma history_population_budget (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    ∑ i ∈ thirdSteps seed, dist (ballLeader hD (seed i)).val (C.assign (ballLeader hD (seed i))) /
      Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i)) ≤
      (10/9 : ℝ)*C.bad.card := by
  apply Population.disjoint_population_budget D (thirdSteps seed)
    (fun i => Population.ball D (ballLeader hD (seed i))
      (Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i))))
    _ _ (fun p => dist p (C.assign p)) (comparisonCost D C.assign) C.bad.card hP hm
    (fun _ _ => dist_nonneg) rfl (fun _ _ => Finset.filter_subset _ _)
    (C.history_disjoint hD F hOF Δ hΔ hP hm n seed hseed)
    (fun _ _ => Population.radius_pos D hD _ _ _ hP hm) (fun _ _ => dist_nonneg)
    (fun _ _ => Population.radius_feasible D hD _ _ _ hP hm)
  intro i hi p hp
  have ht := C.history_third_spec hD F hOF Δ hΔ hP hm n seed hseed i hi
  obtain ⟨hpD,hpd⟩ := Finset.mem_filter.mp hp
  have htri := C.comparison_triangle (ballLeader hD (seed i)) p
    (ballLeader hD (seed i)).property hpD
  linarith [ht.1]

def entryIndex {m : ℕ} : MainAction D m → ℕ
  | .inr (.inr (_,.inr (.inr j))) => j.val+1
  | _ => 0

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma entryIndex_zero {m : ℕ} (a : MainAction D m) (ha : ¬IsThird a) : entryIndex a = 0 := by
  rcases a with u | (w | ⟨w,e⟩)
  · rfl
  · rfl
  · rcases e with j | (e | j)
    · rfl
    · rfl
    · exact False.elim (ha ⟨w,j,rfl⟩)

lemma history_third_index (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin n) (hi : i ∈ thirdSteps seed) :
    entryIndex (seed i) = Nat.ceil (dist (ballLeader hD (seed i)).val (C.assign (ballLeader hD (seed i))) /
      (mainKappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i)))) := by
  obtain ⟨R,ha,_,_⟩ := C.history_ball hD F hOF Δ hΔ hP hm n seed hseed i ((thirdSteps_subset seed) hi)
  obtain ⟨w,j,hj⟩ := (Finset.mem_filter.mp hi).2
  have he : C.prescribedEntry hD hP hm (C.history hD F Δ n seed i.castSucc)
      (ballLeader hD (seed i)) = .inr (.inr j) := by
    rw [hj] at ha
    simpa only [hj] using (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj ha))).2.symm
  obtain ⟨_,_,_,_,_,hentry⟩ := C.prescribedEntry_spec hD hP hm _
    (C.history_correct hD F hOF Δ hΔ hP hm n seed hseed i.castSucc) (ballLeader hD (seed i))
  have hh := (hentry j he).2.2
  simpa only [hj,entryIndex,ballLeader] using hh

lemma history_index_budget (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    (∑ i ∈ ballSteps seed, (entryIndex (seed i) : ℝ)) ≤ (10/(9*mainKappa)+1)*C.bad.card := by
  have he : (∑ i ∈ ballSteps seed, (entryIndex (seed i) : ℝ)) =
      ∑ i ∈ thirdSteps seed, (entryIndex (seed i) : ℝ) := by
    symm
    apply Finset.sum_subset (thirdSteps_subset seed)
    intro i _ hi
    have hh : ¬IsThird (seed i) := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    rw [entryIndex_zero (seed i) hh,Nat.cast_zero]
  rw [he]
  have hh := Population.ceiling_index_budget (thirdSteps seed)
    (fun i => Population.radius D hD (comparisonCost D C.assign) C.bad.card (ballLeader hD (seed i)))
    (fun i => dist (ballLeader hD (seed i)).val (C.assign (ballLeader hD (seed i))))
    mainKappa C.bad.card mainKappa_pos
    ((Finset.card_le_card (thirdSteps_subset seed)).trans
      (C.history_ball_count hD F hOF Δ hΔ hP hm n seed hseed))
    (fun _ _ => Population.radius_pos D hD _ _ _ hP hm) (fun _ _ => dist_nonneg)
    (C.history_population_budget hD F hOF Δ hΔ hP hm n seed hseed)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [C.history_third_index hD F hOF Δ hΔ hP hm n seed hseed i hi]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma action_entry_lower (m : ℕ) (a : MainAction D m) :
    menuConstant mainKappa mainKappa_pos * (1/2 : ℝ)^(entryIndex a) ≤ actionMenuWeight m a := by
  rcases a with u | (w | ⟨w,e⟩)
  · simpa only [entryIndex,actionMenuWeight,pow_zero,mul_one] using menuConstant_le_one mainKappa mainKappa_pos
  · simpa only [entryIndex,actionMenuWeight,pow_zero,mul_one] using menuConstant_le_one mainKappa mainKappa_pos
  · rcases e with j | (e | j)
    · simpa only [entryIndex,actionMenuWeight,menuWeight,pow_zero,mul_one] using
        first_entry_lower mainKappa mainKappa_pos
    · simpa only [entryIndex,actionMenuWeight,menuWeight,pow_zero,mul_one] using
        second_entry_lower mainKappa mainKappa_pos
    · exact third_entry_lower mainKappa mainKappa_pos (thirdSize mainKappa m) (j.val+1)
        (by unfold thirdSize; omega)

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma actionMenuWeight_of_notBall (m : ℕ) (a : MainAction D m) (ha : ¬IsBall a) :
    actionMenuWeight m a = 1 := by
  rcases a with u | (w | ⟨w,e⟩)
  · rfl
  · rfl
  · exact False.elim (ha ⟨w,e,rfl⟩)

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma actionMenuWeight_le_one (m : ℕ) (a : MainAction D m) : actionMenuWeight m a ≤ 1 := by
  rcases a with u | (w | ⟨w,e⟩)
  · exact le_rfl
  · exact le_rfl
  · have hh := Finset.single_le_sum (s := (Finset.univ : Finset (MainEntry m)))
      (f := menuWeight (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m))
      (fun j _ => menuWeight_nonneg _ _ _ j) (Finset.mem_univ e)
    rw [menuWeight_total _ _ _ (by unfold firstSize; omega) (by unfold thirdSize; omega)] at hh
    exact hh

lemma progressConstant_le_one : NearClients.progressConstant mainKappa ≤ 1 := by
  norm_num [NearClients.progressConstant,mainKappa]

lemma guideLoss_lower (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ)
    (s : Option (State V)) (a : MainAction D C.bad.card) :
    NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a ≤ C.guideLoss hD Δ s a := by
  unfold guideLoss
  split_ifs
  · exact le_rfl
  · exact (mul_le_mul_of_nonneg_left (actionMenuWeight_le_one _ _)
      (NearClients.progressConstant_pos mainKappa mainKappa_pos).le).trans
      (by simpa only [mul_one] using progressConstant_le_one)

lemma history_menu_budget (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    (menuConstant mainKappa mainKappa_pos)^C.bad.card *
      (2 : ℝ)^(-((10/(9*mainKappa)+1)*C.bad.card)) ≤
        ∏ i : Fin n, actionMenuWeight C.bad.card (seed i) := by
  have hh := menu_product_budget (ballSteps seed) C.bad.card (menuConstant mainKappa mainKappa_pos)
    (menuConstant_pos mainKappa mainKappa_pos) (menuConstant_le_one mainKappa mainKappa_pos)
    (fun i => entryIndex (seed i)) (fun i => actionMenuWeight C.bad.card (seed i))
    (fun i _ => action_entry_lower _ (seed i))
    (C.history_ball_count hD F hOF Δ hΔ hP hm n seed hseed) _
    (C.history_index_budget hD F hOF Δ hΔ hP hm n seed hseed)
  have he : (∏ i ∈ ballSteps seed, actionMenuWeight C.bad.card (seed i)) =
      ∏ i : Fin n, actionMenuWeight C.bad.card (seed i) := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro i _ hi
    exact actionMenuWeight_of_notBall _ _ (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
  exact hh.trans_eq he

lemma history_loss_budget (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    NearClients.progressConstant mainKappa ^ n * (menuConstant mainKappa mainKappa_pos)^C.bad.card *
      (2 : ℝ)^(-((10/(9*mainKappa)+1)*C.bad.card)) ≤
        Guided.pathWeight (C.guidedUpdate hD F Δ) (C.guideLoss hD Δ) n (some State.initial) seed := by
  have hρ := (NearClients.progressConstant_pos mainKappa mainKappa_pos).le
  rw [Guided.pathWeight_eq_prod]
  calc
    _ = NearClients.progressConstant mainKappa ^ n *
        ((menuConstant mainKappa mainKappa_pos)^C.bad.card *
          (2 : ℝ)^(-((10/(9*mainKappa)+1)*C.bad.card))) := mul_assoc _ _ _
    _ ≤ NearClients.progressConstant mainKappa ^ n *
        (∏ i : Fin n, actionMenuWeight C.bad.card (seed i)) :=
      mul_le_mul_of_nonneg_left (C.history_menu_budget hD F hOF Δ hΔ hP hm n seed hseed) (pow_nonneg hρ n)
    _ = ∏ i : Fin n, NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card (seed i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => mul_nonneg hρ (actionMenuWeight_nonneg _ _))
      (fun i _ => C.guideLoss_lower hD Δ _ _)

noncomputable def samplingBound (m : ℕ) : ℝ :=
  NearClients.progressConstant mainKappa ^ (2*m) * (menuConstant mainKappa mainKappa_pos)^m *
    (2 : ℝ)^(-((10/(9*mainKappa)+1)*m))

lemma samplingBound_pos (m : ℕ) : 0 < samplingBound m := by
  exact mul_pos (mul_pos (pow_pos (NearClients.progressConstant_pos mainKappa mainKappa_pos) _)
    (pow_pos (menuConstant_pos mainKappa mainKappa_pos) _)) (Real.rpow_pos_of_pos (by norm_num) _)

theorem actual_records_success (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    samplingBound C.bad.card ≤ Guided.hitMass
      (update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
        (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card))
      (mainActual D S Δ C.bad.card) (C.stop hD Δ) (2*C.bad.card) (some State.initial) := by
  rw [← Guided.hitMass_stopped _ _ _ (Sum.inl ())]
  change samplingBound C.bad.card ≤ Guided.hitMass (C.guidedUpdate hD F Δ)
    (C.stoppedActual hD Δ) (C.stop hD Δ) (2*C.bad.card) (some State.initial)
  apply Guided.history_likelihood_bound (C.guidedUpdate hD F Δ) (C.stoppedActual hD Δ)
    (C.guideKernel hD Δ hΔ hP hm) (C.guideLoss hD Δ) (C.guideLoss_nonneg hD Δ)
    (C.guideLoss_domination hD Δ hΔ hP hm) _ _ _ _ (samplingBound_pos _).le
  · intro seed hseed
    exact C.history_loss_budget hD F hOF Δ hΔ hP hm _ seed hseed
  · exact C.guide_hits hD F hOF Δ hΔ hP hm

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
