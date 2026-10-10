import Mathlib

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {E R : Type*} [Fintype R]

noncomputable def score (baseline : ℝ) (offer : E → ℝ) (X : Finset E) : ℝ :=
  X.fold max baseline offer

lemma score_le_iff {baseline t : ℝ} {offer : E → ℝ} {X : Finset E} :
    score baseline offer X ≤ t ↔ baseline ≤ t ∧ ∀ e ∈ X, offer e ≤ t :=
  Finset.fold_max_le t

lemma le_score_iff {baseline t : ℝ} {offer : E → ℝ} {X : Finset E} :
    t ≤ score baseline offer X ↔ t ≤ baseline ∨ ∃ e ∈ X, t ≤ offer e :=
  Finset.le_fold_max t

@[simp] lemma score_empty (baseline : ℝ) (offer : E → ℝ) :
    score baseline offer ∅ = baseline := rfl

lemma baseline_le_score (baseline : ℝ) (offer : E → ℝ) (X : Finset E) :
    baseline ≤ score baseline offer X := le_score_iff.mpr (Or.inl le_rfl)

lemma offer_le_score (baseline : ℝ) (offer : E → ℝ) {X : Finset E} {e : E}
    (he : e ∈ X) : offer e ≤ score baseline offer X :=
  le_score_iff.mpr (Or.inr ⟨e,he,le_rfl⟩)

lemma score_mono (baseline : ℝ) (offer : E → ℝ) : Monotone (score baseline offer) := by
  intro X Y hXY
  exact score_le_iff.mpr ⟨baseline_le_score _ _ _, fun e he => offer_le_score _ _ (hXY he)⟩

@[simp] lemma score_insert [DecidableEq E] (baseline : ℝ) (offer : E → ℝ) (X : Finset E) (e : E) :
    score baseline offer (insert e X) = max (offer e) (score baseline offer X) := by
  apply le_antisymm
  · apply score_le_iff.mpr
    refine ⟨(baseline_le_score _ _ _).trans (le_max_right _ _), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (offer_le_score _ _ hx).trans (le_max_right _ _)
  · exact max_le (offer_le_score _ _ (Finset.mem_insert_self _ _))
      (score_mono _ _ (Finset.subset_insert _ _))

lemma score_diminishing [DecidableEq E] (baseline : ℝ) (offer : E → ℝ) {X Y : Finset E}
    (hXY : X ⊆ Y) (e : E) :
    score baseline offer (insert e Y) - score baseline offer Y ≤
      score baseline offer (insert e X) - score baseline offer X := by
  rw [score_insert, score_insert]
  have hm := score_mono baseline offer hXY
  rcases le_total (offer e) (score baseline offer Y) with h | h
  · rw [max_eq_right h, sub_self]
    exact sub_nonneg.mpr (le_max_right _ _)
  · rw [max_eq_left h]
    have hh := le_max_left (offer e) (score baseline offer X)
    linarith

noncomputable def topSum (q : ℕ) (v : R → ℝ) : ℝ :=
  (Finset.univ.powersetCard (min q (Fintype.card R))).sup'
    (Finset.powersetCard_nonempty.mpr (by simp)) (fun S => ∑ s ∈ S, v s)

lemma le_topSum {q : ℕ} (v : R → ℝ) {S : Finset R}
    (hS : S.card = min q (Fintype.card R)) : (∑ s ∈ S, v s) ≤ topSum q v := by
  apply Finset.le_sup' (f := fun S => ∑ s ∈ S, v s)
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  exact hS

lemma topSum_le {q : ℕ} {v : R → ℝ} {a : ℝ}
    (h : ∀ S : Finset R, S.card = min q (Fintype.card R) → (∑ s ∈ S, v s) ≤ a) :
    topSum q v ≤ a := by
  apply Finset.sup'_le
  intro S hS
  exact h S (Finset.mem_powersetCard.mp hS).2

lemma topSum_attained (q : ℕ) (v : R → ℝ) :
    ∃ S : Finset R, S.card = min q (Fintype.card R) ∧ (∑ s ∈ S, v s) = topSum q v := by
  classical
  obtain ⟨S,hS,hm⟩ := Finset.exists_max_image
    (Finset.univ.powersetCard (min q (Fintype.card R)))
    (fun S => ∑ s ∈ S, v s) (Finset.powersetCard_nonempty.mpr (by simp))
  have hc := (Finset.mem_powersetCard.mp hS).2
  refine ⟨S,hc,le_antisymm (le_topSum v hc) ?_⟩
  exact topSum_le (fun T hT => hm T (by simp [Finset.mem_powersetCard, hT]))

lemma topSum_mono (q : ℕ) {v w : R → ℝ} (h : ∀ s, v s ≤ w s) :
    topSum q v ≤ topSum q w := by
  apply topSum_le
  intro S hS
  exact (Finset.sum_le_sum (fun s _ => h s)).trans (le_topSum w hS)

lemma topSum_exchange (q : ℕ) (u v p r : R → ℝ)
    (hu : ∀ s, u s ≤ max (p s) (r s))
    (hv : ∀ s, v s ≤ min (p s) (r s))
    (huv : ∀ s, u s + v s ≤ p s + r s) :
    topSum q u + topSum q v ≤ topSum q p + topSum q r := by
  classical
  obtain ⟨I,hI,eI⟩ := topSum_attained q u
  obtain ⟨J,hJ,eJ⟩ := topSum_attained q v
  let C := I ∩ J
  let A := I \ J
  let B := J \ I
  let A₁ := A.filter (fun s => u s ≤ p s)
  let A₂ := A \ A₁
  have hA₁ : A₁ ⊆ A := Finset.filter_subset _ _
  have hA₂ : A₂ ⊆ A := Finset.sdiff_subset
  have hAC : Disjoint A C := by simp [A,C,Finset.disjoint_left]; tauto
  have hBC : Disjoint B C := by simp [B,C,Finset.disjoint_left]; tauto
  have hAB : Disjoint A B := by simp [A,B,Finset.disjoint_left]; tauto
  have hACard : A.card + C.card = I.card := Finset.card_sdiff_add_card_inter I J
  have hBCard : B.card + C.card = J.card := by
    simpa [B,C,Finset.inter_comm] using Finset.card_sdiff_add_card_inter J I
  have hABCard : A.card = B.card := by omega
  have hAparts : A₂.card + A₁.card = A.card := Finset.card_sdiff_add_card_eq_card hA₁
  obtain ⟨B₁,hB₁,hB₁card⟩ := Finset.exists_subset_card_eq
    (show A₂.card ≤ B.card by rw [← hABCard]; exact Finset.card_le_card hA₂)
  let B₂ := B \ B₁
  have hB₂ : B₂ ⊆ B := Finset.sdiff_subset
  have hBparts : B₂.card + B₁.card = B.card := Finset.card_sdiff_add_card_eq_card hB₁
  let K := C ∪ (A₁ ∪ B₁)
  let L := C ∪ (A₂ ∪ B₂)
  have hKA : Disjoint A₁ B₁ := hAB.mono hA₁ hB₁
  have hLA : Disjoint A₂ B₂ := hAB.mono hA₂ hB₂
  have hKC : Disjoint C (A₁ ∪ B₁) :=
    Finset.disjoint_union_right.mpr ⟨hAC.symm.mono_right hA₁,hBC.symm.mono_right hB₁⟩
  have hLC : Disjoint C (A₂ ∪ B₂) :=
    Finset.disjoint_union_right.mpr ⟨hAC.symm.mono_right hA₂,hBC.symm.mono_right hB₂⟩
  have hK : K.card = min q (Fintype.card R) := by
    simp only [K,Finset.card_union_of_disjoint hKC,Finset.card_union_of_disjoint hKA]
    omega
  have hL : L.card = min q (Fintype.card R) := by
    simp only [L,Finset.card_union_of_disjoint hLC,Finset.card_union_of_disjoint hLA]
    omega
  have hsI : (∑ s ∈ I,u s) = (∑ s ∈ C,u s) + (∑ s ∈ A,u s) := by
    exact (Finset.sum_inter_add_sum_sdiff I J u).symm
  have hsJ : (∑ s ∈ J,v s) = (∑ s ∈ C,v s) + (∑ s ∈ B,v s) := by
    simpa [C,B,Finset.inter_comm] using (Finset.sum_inter_add_sum_sdiff J I v).symm
  have hsA : (∑ s ∈ A,u s) = (∑ s ∈ A₁,u s) + (∑ s ∈ A₂,u s) := by
    simpa only [A₂,add_comm] using (Finset.sum_sdiff (f := u) hA₁).symm
  have hsB : (∑ s ∈ B,v s) = (∑ s ∈ B₁,v s) + (∑ s ∈ B₂,v s) := by
    simpa only [B₂,add_comm] using (Finset.sum_sdiff (f := v) hB₁).symm
  have hC : (∑ s ∈ C,u s) + (∑ s ∈ C,v s) ≤
      (∑ s ∈ C,p s) + (∑ s ∈ C,r s) := by
    simpa only [Finset.sum_add_distrib] using Finset.sum_le_sum (fun s (_ : s ∈ C) => huv s)
  have h₁ : (∑ s ∈ A₁,u s) ≤ (∑ s ∈ A₁,p s) :=
    Finset.sum_le_sum (fun s hs => (Finset.mem_filter.mp hs).2)
  have h₂ : (∑ s ∈ A₂,u s) ≤ (∑ s ∈ A₂,r s) := by
    apply Finset.sum_le_sum
    intro s hs
    have hs' := Finset.mem_sdiff.mp hs
    have hn : ¬u s ≤ p s := by
      intro hh
      exact hs'.2 (Finset.mem_filter.mpr ⟨hs'.1,hh⟩)
    exact (le_max_iff.mp (hu s)).resolve_left hn
  have h₃ : (∑ s ∈ B₁,v s) ≤ (∑ s ∈ B₁,p s) :=
    Finset.sum_le_sum (fun s _ => (hv s).trans (min_le_left _ _))
  have h₄ : (∑ s ∈ B₂,v s) ≤ (∑ s ∈ B₂,r s) :=
    Finset.sum_le_sum (fun s _ => (hv s).trans (min_le_right _ _))
  have hfront : (∑ s ∈ I,u s) + (∑ s ∈ J,v s) ≤
      (∑ s ∈ K,p s) + (∑ s ∈ L,r s) := by
    rw [hsI,hsJ,hsA,hsB]
    simp only [K,L,Finset.sum_union hKC,Finset.sum_union hKA,
      Finset.sum_union hLC,Finset.sum_union hLA]
    linarith
  rw [← eI,← eJ]
  exact hfront.trans (add_le_add (le_topSum p hK) (le_topSum r hL))

lemma topScores_diminishing [DecidableEq E] (q : ℕ)
    (baseline : R → ℝ) (offer : R → E → ℝ) {X Y : Finset E}
    (hXY : X ⊆ Y) (e : E) :
    topSum q (fun r => score (baseline r) (offer r) (insert e Y)) -
        topSum q (fun r => score (baseline r) (offer r) Y) ≤
    topSum q (fun r => score (baseline r) (offer r) (insert e X)) -
        topSum q (fun r => score (baseline r) (offer r) X) := by
  have hh := topSum_exchange q
    (fun r => score (baseline r) (offer r) (insert e Y))
    (fun r => score (baseline r) (offer r) X)
    (fun r => score (baseline r) (offer r) Y)
    (fun r => score (baseline r) (offer r) (insert e X))
  have h₁ : ∀ r, score (baseline r) (offer r) (insert e Y) ≤
      max (score (baseline r) (offer r) Y) (score (baseline r) (offer r) (insert e X)) := by
    intro r
    rw [score_insert,score_insert]
    exact max_le ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _)
  have h₂ : ∀ r, score (baseline r) (offer r) X ≤
      min (score (baseline r) (offer r) Y) (score (baseline r) (offer r) (insert e X)) := by
    intro r
    exact le_min (score_mono _ _ hXY) (score_mono _ _ (Finset.subset_insert _ _))
  have h₃ : ∀ r, score (baseline r) (offer r) (insert e Y) + score (baseline r) (offer r) X ≤
      score (baseline r) (offer r) Y + score (baseline r) (offer r) (insert e X) := by
    intro r
    linarith [score_diminishing (baseline r) (offer r) hXY e]
  linarith [hh h₁ h₂ h₃]

noncomputable def bottomSum (q : ℕ) (v : R → ℝ) : ℝ := -topSum q (fun r => -v r)

lemma bottomSum_attained (q : ℕ) (v : R → ℝ) :
    ∃ S : Finset R, S.card = min q (Fintype.card R) ∧ (∑ s ∈ S, v s) = bottomSum q v := by
  obtain ⟨S,hS,hm⟩ := topSum_attained q (fun r => -v r)
  refine ⟨S,hS,?_⟩
  unfold bottomSum
  rw [← hm,Finset.sum_neg_distrib,neg_neg]

lemma bottomSum_le {q : ℕ} (v : R → ℝ) {S : Finset R}
    (hS : S.card = min q (Fintype.card R)) : bottomSum q v ≤ ∑ s ∈ S, v s := by
  have hh := le_topSum (fun r => -v r) hS
  simp only [Finset.sum_neg_distrib] at hh
  exact neg_le.mp (by simpa only [bottomSum] using hh)

noncomputable def cappedCost (baseline : ℝ) (distance : E → ℝ) (X : Finset E) : ℝ :=
  X.fold min baseline distance

@[simp] lemma cappedCost_empty (baseline : ℝ) (distance : E → ℝ) :
    cappedCost baseline distance ∅ = baseline := rfl

lemma complement_cappedCost (C w baseline : ℝ) (distance : E → ℝ)
    (hw : 0 ≤ w) (X : Finset E) :
    C - w * cappedCost baseline distance X =
      score (C - w * baseline) (fun e => C - w * distance e) X := by
  classical
  induction X using Finset.induction_on with
  | empty => simp
  | @insert e X he ih =>
    simp only [cappedCost,Finset.fold_insert he,score_insert]
    change C-w*min (distance e) (cappedCost baseline distance X) = _
    rw [mul_min_of_nonneg _ _ hw,← max_sub_sub_left,ih]

variable {P : Type*} [Fintype P]

noncomputable def surrogate (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ) (X : Finset E) : ℝ :=
  K + ∑ p, cappedCost (base p) (distance p) X +
    bottomSum q (fun r => weight r * cappedCost (redBase r) (redDistance r) X)

noncomputable def saving (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ) (X : Finset E) : ℝ :=
  surrogate K q base distance weight redBase redDistance ∅ -
    surrogate K q base distance weight redBase redDistance X

lemma saving_eq_scores (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (X : Finset E) :
    saving K q base distance weight redBase redDistance X =
      (∑ p, score 0 (fun e => base p - distance p e) X) +
      topSum q (fun r => score (-(weight r * redBase r))
        (fun e => -(weight r * redDistance r e)) X) -
      topSum q (fun r => -(weight r * redBase r)) := by
  have hbase (p : P) := complement_cappedCost (base p) 1 (base p) (distance p) (by norm_num) X
  simp only [one_mul,sub_self] at hbase
  have hred (r : R) := complement_cappedCost 0 (weight r) (redBase r) (redDistance r) (hw r) X
  simp only [zero_sub] at hred
  simp only [saving,surrogate,cappedCost_empty,bottomSum]
  simp only [hred,← hbase,Finset.sum_sub_distrib]
  ring

@[simp] lemma saving_empty (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ) :
    saving K q base distance weight redBase redDistance ∅ = 0 := sub_self _

lemma saving_mono (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (hw : ∀ r, 0 ≤ weight r) :
    Monotone (saving K q base distance weight redBase redDistance) := by
  intro X Y hXY
  rw [saving_eq_scores K q base distance weight redBase redDistance hw X,
    saving_eq_scores K q base distance weight redBase redDistance hw Y]
  apply sub_le_sub_right
  apply add_le_add
  · exact Finset.sum_le_sum (fun p _ => score_mono 0 (fun e => base p-distance p e) hXY)
  · exact topSum_mono q (fun r => score_mono _ _ hXY)

lemma saving_nonneg (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (X : Finset E) :
    0 ≤ saving K q base distance weight redBase redDistance X := by
  simpa only [saving_empty] using
    saving_mono K q base distance weight redBase redDistance hw (Finset.empty_subset X)

lemma saving_diminishing [DecidableEq E] (K : ℝ) (q : ℕ)
    (base : P → ℝ) (distance : P → E → ℝ)
    (weight redBase : R → ℝ) (redDistance : R → E → ℝ)
    (hw : ∀ r, 0 ≤ weight r) {X Y : Finset E} (hXY : X ⊆ Y) (e : E) :
    saving K q base distance weight redBase redDistance (insert e Y) -
        saving K q base distance weight redBase redDistance Y ≤
    saving K q base distance weight redBase redDistance (insert e X) -
        saving K q base distance weight redBase redDistance X := by
  have hb := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) =>
    score_diminishing 0 (fun e => base p-distance p e) hXY e)
  simp only [Finset.sum_sub_distrib] at hb
  have hr := topScores_diminishing q (fun r => -(weight r*redBase r))
    (fun r e => -(weight r*redDistance r e)) hXY e
  simp only [saving_eq_scores K q base distance weight redBase redDistance hw]
  linarith

end MetricKMedianRecovery.Completion

end OAI
