import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestInsertEqual
import OAI.Combinatorics.KMedianRecovery.Recovery.ImagePhaseUnion

namespace OAI

namespace MetricKMedianRecovery.CoincidentHistory
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] in
lemma nearest_image (loc : D → X) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (j : D) :
    nearestDistance (loc j) (Q.image r) = nearestDistance (loc j) Q := by
  by_cases hQ : Q.Nonempty
  · have hh := LeafTransfer.nearest_images Q hQ id r (loc j) 0
      (fun x _ => (hd j x).le) (fun x _ => by simp only [id_eq,hd,add_zero,le_refl])
    have hr := hh.2
    rw [add_zero] at hr
    simpa using le_antisymm hh.1 hr
  · simp [Finset.not_nonempty_iff_eq_empty.mp hQ,nearestDistance]

omit [Fintype D] in
lemma active_image (loc : D → X) (t z : ℝ) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (j : D) :
    activeAt loc t z (Q.image r) j ↔ activeAt loc t z Q j := by
  simp only [activeAt,Finset.forall_mem_image,hd]

omit [Fintype D] in
lemma admissible_image (loc : D → X) (t K v z : ℝ) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (i : X) (tau : D → ℝ) :
    admissibleBids loc t K v z (Q.image r) i tau ↔ admissibleBids loc t K v z Q i tau := by
  simp only [admissibleBids,active_image loc t z Q r hd,Finset.forall_mem_image,hd]

lemma payment_image (loc : D → X) (t z : ℝ) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (i : X) (tau : D → ℝ) :
    openingPayment loc t z (Q.image r) i tau = openingPayment loc t z Q i tau := by
  unfold openingPayment
  apply Finset.sum_congr rfl
  intro j _
  rw [active_image loc t z Q r hd j,nearest_image loc Q r hd j]

lemma dual_image (loc : D → X) (t z : ℝ) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (i : X) (tau : D → ℝ) (a : D) :
    openingDual loc t z (Q.image r) i tau a = openingDual loc t z Q i tau a := by
  unfold openingDual
  apply Finset.sum_congr rfl
  intro j _
  rw [active_image loc t z Q r hd j]

lemma openable_image (loc : D → X) (F Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (t K v z lam eta : ℝ) (i : X) :
    etaOpenable loc F (Q.image r) t K v z lam eta i ↔ etaOpenable loc F Q t K v z lam eta i := by
  simp only [etaOpenable,admissible_image loc t K v z Q r hd,
    payment_image loc t z Q r hd,dual_image loc t z Q r hd,active_image loc t z Q r hd]

omit [Fintype D] in
lemma swap_distances (loc : D → X) (i f : X) (hd : ∀ j, dist (loc j) i = dist (loc j) f) :
    ∀ j x, dist (loc j) (Equiv.swap i f x) = dist (loc j) x := by
  intro j x
  by_cases hxi : x = i
  · subst x; simpa using (hd j).symm
  by_cases hxf : x = f
  · subst x; simpa using hd j
  · rw [Equiv.swap_apply_of_ne_of_ne hxi hxf]

omit [PseudoMetricSpace X] in
lemma swap_alphabet (F B : Finset X) (i f : X) (hf : f ∉ F ∪ B) (x : X) (hx : x ∈ F ∪ B) :
    Equiv.swap i f x ∈ F ∪ insert f B := by
  by_cases hxi : x = i
  · subst x; simp
  · have hxf : x ≠ f := fun h => hf (h ▸ hx)
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxf]
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hx)

theorem entry_swap (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (i f x : X) (hf : f ∉ F ∪ B)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (h : PhaseSequence.Entry loc F B Q v z lam eta x) :
    PhaseSequence.Entry loc F (insert f B) (Q.image (Equiv.swap i f)) v z lam eta (Equiv.swap i f x) := by
  have hnot : Equiv.swap i f x ∉ Q.image (Equiv.swap i f) := by
    intro hh
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hh
    exact h.1 ((Equiv.swap i f).injective he ▸ hy)
  refine ⟨hnot,?_⟩
  by_cases hxi : x = i
  · subst x
    left
    simp
  have hxf : x ≠ f := fun he => hf (he ▸ h.mem)
  rw [Equiv.swap_apply_of_ne_of_ne hxi hxf]
  rcases h.2 with hx | ⟨hx,W,hQ,hW,hop⟩
  · exact Or.inl (Finset.mem_insert_of_mem hx)
  · right
    refine ⟨hx,W.image (Equiv.swap i f),Finset.image_subset_image hQ,?_,?_⟩
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact swap_alphabet F B i f hf x (hW hx)
    · exact (openable_image loc F W (Equiv.swap i f) (swap_distances loc i f hd)
        (1-3*v) (1+v^2) v z lam eta x).mpr hop

theorem prefix_swap (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (i f : X) (hf : f ∉ F ∪ B) (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (H : List X) (h : PhaseSequence.Prefix loc F B v z lam eta Q H) :
    PhaseSequence.Prefix loc F (insert f B) v z lam eta (Q.image (Equiv.swap i f))
      (H.map (Equiv.swap i f)) := by
  induction h with
  | nil => exact PhaseSequence.Prefix.nil _
  | cons he ht ih =>
    apply PhaseSequence.Prefix.cons (entry_swap loc F B _ v z lam eta i f _ hf hd he)
    simpa only [Finset.image_insert] using ih

theorem maximal_swap (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (i f : X) (hf : f ∉ F) (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (h : PhaseSequence.Maximal loc F Q v z lam) :
    PhaseSequence.Maximal loc F (Q.image (Equiv.swap i f)) v z lam := by
  intro x hx hnot hop
  by_cases hxi : x = i
  · subst x
    by_cases hiQ : i ∈ Q
    · have hfQ : f ∈ Q.image (Equiv.swap i f) := by
        exact Finset.mem_image.mpr ⟨i,hiQ,Equiv.swap_apply_left i f⟩
      exact CoincidentCopy.not_openable loc F (Q.image (Equiv.swap i f)) (1-3*v) (1+v^2)
        v z lam 0 i f hfQ hd ht (by simpa only [mul_zero,sub_zero] using hlam) hop
    · exact h i hx hiQ ((openable_image loc F Q (Equiv.swap i f) (swap_distances loc i f hd)
        (1-3*v) (1+v^2) v z lam 0 i).mp hop)
  · have hxf : x ≠ f := fun he => hf (he ▸ hx)
    have hxQ : x ∉ Q := by
      intro hh
      apply hnot
      exact Finset.mem_image.mpr ⟨x,hh,Equiv.swap_apply_of_ne_of_ne hxi hxf⟩
    exact h x hx hxQ ((openable_image loc F Q (Equiv.swap i f) (swap_distances loc i f hd)
      (1-3*v) (1+v^2) v z lam 0 x).mp hop)

theorem valid_swap (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (i f : X) (hf : f ∉ F ∪ B) (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (H : List X)
    (h : PhaseSequence.Valid loc F B Q v z lam eta H) :
    PhaseSequence.Valid loc F (insert f B) (Q.image (Equiv.swap i f)) v z lam eta (H.map (Equiv.swap i f)) := by
  refine ⟨prefix_swap loc F B Q v z lam eta i f hf hd H h.1,?_⟩
  rw [image_phase_union]
  exact maximal_swap loc F (Q ∪ H.toFinset) v z lam i f (fun he => hf (Finset.mem_union_left _ he)) hd ht hlam h.2

theorem history_swap (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (i f : X) (hf : f ∉ F ∪ B) (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (q : ℕ) (T : List (List X))
    (h : History loc F B v lam eta q Q T) :
    History loc F (insert f B) v lam eta q (Q.image (Equiv.swap i f))
      (T.map (List.map (Equiv.swap i f))) := by
  induction h with
  | nil => exact History.nil _ _
  | cons hhead htail ih =>
    apply History.cons (valid_swap loc F B _ v _ lam eta i f hf hd ht hlam _ hhead)
    simpa only [image_phase_union] using ih

omit [Fintype D] [PseudoMetricSpace X] in
lemma swap_set (Q : Finset X) (i f : X) (hi : i ∈ Q) (hf : f ∉ Q) :
    Q.image (Equiv.swap i f) = insert f (Q.erase i) := by
  have hkeep : (Q.erase i).image (Equiv.swap i f) = Q.erase i := by
    calc
      (Q.erase i).image (Equiv.swap i f) = (Q.erase i).image id := by
        apply Finset.image_congr
        intro x hx
        exact Equiv.swap_apply_of_ne_of_ne (Finset.ne_of_mem_erase hx)
          (fun he => hf (he ▸ Finset.mem_of_mem_erase hx))
      _ = Q.erase i := Finset.image_id
  calc
    Q.image (Equiv.swap i f) = (insert i (Q.erase i)).image (Equiv.swap i f) := by
      rw [Finset.insert_erase hi]
    _ = insert f (Q.erase i) := by rw [Finset.image_insert,Equiv.swap_apply_left,hkeep]

omit [Fintype D] [PseudoMetricSpace X] in
lemma paid_swap (F Q : Finset X) (i f : X) (hiF : i ∈ F) (hiQ : i ∈ Q)
    (hfF : f ∉ F) (hfQ : f ∉ Q) :
    (Q ∩ F).card = ((Q.image (Equiv.swap i f)) ∩ F).card+1 := by
  rw [swap_set Q i f hiQ hfQ]
  have hh := CoincidentCopy.paid_count F (Q.erase i) i f hiF (Finset.notMem_erase i Q) hfF
  rw [Finset.insert_erase hiQ] at hh
  simpa only [Finset.inter_comm] using hh

omit [Fintype D] [PseudoMetricSpace X] in
lemma free_swap (F Q : Finset X) (i f : X) (hiF : i ∈ F) (hiQ : i ∈ Q)
    (hfF : f ∉ F) (hfQ : f ∉ Q) :
    ((Q.image (Equiv.swap i f)) \ F).card = (Q \ F).card+1 := by
  have hp := paid_swap F Q i f hiF hiQ hfF hfQ
  have hc := Finset.card_image_of_injective Q (Equiv.swap i f).injective
  have h₁ := Finset.card_inter_add_card_sdiff (Q.image (Equiv.swap i f)) F
  have h₂ := Finset.card_inter_add_card_sdiff Q F
  omega

omit [Fintype D] [PseudoMetricSpace X] in
lemma phase_free_swap (F Q : Finset X) (i f : X) (hiF : i ∈ F)
    (hfF : f ∉ F) (hfQ : f ∉ Q) :
    ((Q.image (Equiv.swap i f)) \ F).card ≤ (Q \ F).card+1 := by
  by_cases hiQ : i ∈ Q
  · exact (free_swap F Q i f hiF hiQ hfF hfQ).le
  · have he : Q.image (Equiv.swap i f) = Q := by
      calc
        Q.image (Equiv.swap i f) = Q.image id := by
          apply Finset.image_congr
          intro x hx
          exact Equiv.swap_apply_of_ne_of_ne (fun he => hiQ (he ▸ hx))
            (fun he => hfQ (he ▸ hx))
        _ = Q := Finset.image_id
    rw [he]
    exact Nat.le_succ _

theorem endpoint (loc : D → X) (F B : Finset X) (v lam eta zEnd : ℝ)
    (i f : X) (hiF : i ∈ F) (hf : f ∉ F ∪ B)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (T : List (List X))
    (hh : History loc F B v lam eta 0 ∅ T) (hiQ : i ∈ after ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) zEnd (after ∅ T) j) :
    History loc F (insert f B) v lam eta 0 ∅ (T.map (List.map (Equiv.swap i f))) ∧
    (∀ j, ¬activeAt loc (1-3*v) zEnd (after ∅ (T.map (List.map (Equiv.swap i f)))) j) ∧
    ((after ∅ T) ∩ F).card = ((after ∅ (T.map (List.map (Equiv.swap i f)))) ∩ F).card+1 ∧
    ((after ∅ (T.map (List.map (Equiv.swap i f)))) \ F).card = ((after ∅ T) \ F).card+1 := by
  have hfF : f ∉ F := fun he => hf (Finset.mem_union_left _ he)
  have hfQ : f ∉ after ∅ T := fun he => hf (hh.after_subset (Finset.empty_subset _) he)
  have ha : after ∅ (T.map (List.map (Equiv.swap i f))) = (after ∅ T).image (Equiv.swap i f) := by
    simpa only [Finset.image_empty] using after_map (∅ : Finset X) T (Equiv.swap i f)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Finset.image_empty] using history_swap loc F B ∅ v lam eta i f hf hd ht hlam 0 T hh
  · intro j hj
    rw [ha] at hj
    exact hterm j ((active_image loc (1-3*v) zEnd (after ∅ T) (Equiv.swap i f)
      (swap_distances loc i f hd) j).mp hj)
  · rw [ha]
    exact paid_swap F (after ∅ T) i f hiF hiQ hfF hfQ
  · rw [ha]
    exact free_swap F (after ∅ T) i f hiF hiQ hfF hfQ

end MetricKMedianRecovery.CoincidentHistory

end OAI
