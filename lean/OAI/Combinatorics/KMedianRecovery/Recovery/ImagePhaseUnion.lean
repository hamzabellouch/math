import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.OpenableMap

namespace OAI

namespace MetricKMedianRecovery.PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_phase_union (Q : Finset X) (H : List X) (r : X → X) :
    Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
  ext x
  simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
  aesop

omit [Fintype D] [PseudoMetricSpace X] in
lemma after_map (Q : Finset X) (T : List (List X)) (r : X → X) :
    after (Q.image r) (T.map (List.map r)) = (after Q T).image r := by
  induction T generalizing Q with
  | nil => rfl
  | cons H T ih =>
    simp only [List.map_cons,after,image_phase_union]
    exact ih _

lemma History.after_subset {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {T : List (List X)} (h : History loc F B v lam eta q Q T)
    (hQ : Q ⊆ F ∪ B) : after Q T ⊆ F ∪ B := by
  induction h with
  | nil => exact hQ
  | cons hhead htail ih =>
    exact ih (Finset.union_subset hQ hhead.1.opened_subset)

lemma advance_rows (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q : ℕ)
    (H : List X) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hhead : PhaseSequence.Valid loc F B Q v ((1+v^2)^q) lam eta H) :
    ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^(q+1)) (Q ∪ H.toFinset) i ≤ lam := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hrow' : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (Q ∪ H.toFinset) i ≤ lam := by
    intro i hi
    exact (bidRow_antitone_open loc (1-3*v) ((1+v^2)^q) Q (Q ∪ H.toFinset) i ht
      Finset.subset_union_left).trans (hrow i hi)
  have hz : 0 < (1+v^2)^q := by positivity
  simpa only [pow_succ,mul_comm] using
    phase_update_no_overbid loc F (Q ∪ H.toFinset) v ((1+v^2)^q) lam
      hv hvsmall hz hlam hrow' hhead.2

theorem history_map (loc : D → X) (F B Q : Finset X) (T : List (List X)) (q : ℕ)
    (r : X → X) (v lam lam' eta eps : ℝ) (hv : 0 < v) (hvsmall : v < 1/6)
    (hlam : 0 < lam) (heps : 0 ≤ eps) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i) (hQ : Q ⊆ F ∪ B)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hh : History loc F B v lam 0 q Q T) :
    History loc F (B.image r) v lam' eta q (Q.image r) (T.map (List.map r)) := by
  induction hh with
  | nil q Q => exact History.nil q (Q.image r)
  | @cons q Q H T hhead htail ih =>
    have hz : 0 < (1+v^2)^q := by positivity
    have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
    have hrowEnd : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (Q ∪ H.toFinset) i ≤ lam := by
      intro i hi
      exact (bidRow_antitone_open loc (1-3*v) ((1+v^2)^q) Q (Q ∪ H.toFinset) i ht
        Finset.subset_union_left).trans (hrow i hi)
    apply History.cons
    · exact PhaseParameterTransfer.valid_map loc F B Q H r v ((1+v^2)^q) lam lam' eta eps
        hv hvsmall hz hlam heps hprice herror hinj hfix hQ hshrink hloss hrowEnd hhead
    · rw [image_phase_union]
      exact ih (Finset.union_subset hQ hhead.1.opened_subset)
        (advance_rows loc F B Q v lam 0 q H hv hvsmall hlam hrow hhead)

omit [Fintype D] [PseudoMetricSpace X] in
lemma paid_image (F Q : Finset X) (r : X → X) (hinj : Function.Injective r)
    (hfix : ∀ i ∈ F, r i = i) :
    (Q.image r ∩ F).card = (Q ∩ F).card := by
  have heq : Q.image r ∩ F = (Q ∩ F).image r := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ,hxF⟩ := Finset.mem_inter.mp hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hxQ
      have haeq : r a = a := hinj (hfix (r a) hxF)
      exact Finset.mem_image.mpr ⟨a,Finset.mem_inter.mpr ⟨ha,haeq ▸ hxF⟩,rfl⟩
    · intro hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨a,(Finset.mem_inter.mp ha).1,rfl⟩,
        (hfix a (Finset.mem_inter.mp ha).2).symm ▸ (Finset.mem_inter.mp ha).2⟩
  rw [heq,Finset.card_image_of_injective _ hinj]

omit [Fintype D] [PseudoMetricSpace X] in
lemma free_image (F Q : Finset X) (r : X → X) (hinj : Function.Injective r)
    (hfix : ∀ i ∈ F, r i = i) :
    (Q.image r \ F).card = (Q \ F).card := by
  have hp := paid_image F Q r hinj hfix
  have hcard := Finset.card_image_of_injective Q hinj
  have h₁ := Finset.card_inter_add_card_sdiff (Q.image r) F
  have h₂ := Finset.card_inter_add_card_sdiff Q F
  omega

omit [Fintype D] in
lemma termination_map (loc : D → X) (F B Q : Finset X) (r : X → X) (t z : ℝ)
    (ht : 0 ≤ t) (hQ : Q ⊆ F ∪ B)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hterm : ∀ j, ¬activeAt loc t z Q j) :
    ∀ j, ¬activeAt loc t z (Q.image r) j := by
  intro j hj
  apply hterm j
  intro x hx
  exact (hj (r x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)).trans_le
    (mul_le_mul_of_nonneg_left (hshrink j x (hQ hx)) ht)

theorem terminal_history_map (loc : D → X) (F B : Finset X) (T : List (List X))
    (r : X → X) (v lam lam' eta eps zEnd : ℝ) (hv : 0 < v) (hvsmall : v < 1/6)
    (hlam : 0 < lam) (heps : 0 ≤ eps) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hfar : ∀ j, ∀ i ∈ F, 1 ≤ dist i (loc j))
    (hh : History loc F B v lam 0 0 ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) zEnd (after ∅ T) j) :
    History loc F (B.image r) v lam' eta 0 ∅ (T.map (List.map r)) ∧
    (∀ j, ¬activeAt loc (1-3*v) zEnd (after ∅ (T.map (List.map r))) j) ∧
    ((after ∅ (T.map (List.map r))) ∩ F).card = ((after ∅ T) ∩ F).card ∧
    ∀ H ∈ T, (((H.map r).toFinset) \ F).card = (H.toFinset \ F).card := by
  have hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^0) ∅ i ≤ lam := by
    intro i hi
    have he : bidRow loc (1-3*v) ((1+v^2)^0) ∅ i = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [clippedAt,Finset.not_nonempty_empty,↓reduceIte,pow_zero]
      exact max_eq_right (by linarith only [hfar j i hi])
    rw [he]
    exact hlam.le
  have hmap := history_map loc F B ∅ T 0 r v lam lam' eta eps hv hvsmall hlam heps
    hprice herror hinj hfix (Finset.empty_subset _) hshrink hloss hrow hh
  have he : after ∅ (T.map (List.map r)) = (after ∅ T).image r := by
    simpa only [Finset.image_empty] using after_map (∅ : Finset X) T r
  refine ⟨by simpa only [Finset.image_empty] using hmap,?_,?_,?_⟩
  · rw [he]
    exact termination_map loc F B (after ∅ T) r (1-3*v) zEnd
      (by linarith only [hvsmall]) (hh.after_subset (Finset.empty_subset _)) hshrink hterm
  · rw [he]
    exact paid_image F _ r hinj hfix
  · intro H _
    have heH : (H.map r).toFinset = H.toFinset.image r := by
      simpa only [Finset.image_empty,Finset.empty_union] using image_phase_union (∅ : Finset X) H r
    rw [heH]
    exact free_image F _ r hinj hfix

end MetricKMedianRecovery.PhaseHistoryTransfer

end OAI
