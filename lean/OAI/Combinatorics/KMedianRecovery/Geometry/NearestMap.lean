import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ImagePhaseUnion

namespace OAI

namespace MetricKMedianRecovery.HistoryIsometry
open PhaseHistoryTransfer
variable {D X Y : Type*} [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [DecidableEq X] [DecidableEq Y]

omit [Fintype D] [DecidableEq X] in
lemma nearest_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (p : X) (Q : Finset X) : nearestDistance (r p) (Q.image r) = nearestDistance p Q := by
  by_cases hQ : Q.Nonempty
  · apply le_antisymm
    · obtain ⟨x,hx,he⟩ := nearestDistance_attained p Q hQ
      rw [he,← hr p x]
      exact nearestDistance_le_mem _ _ _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    · obtain ⟨y,hy,he⟩ := nearestDistance_attained (r p) (Q.image r) (hQ.image r)
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      rw [he,hr]
      exact nearestDistance_le_mem _ _ _ hx
  · simp [Finset.not_nonempty_iff_eq_empty.mp hQ,nearestDistance]

omit [Fintype D] [DecidableEq X] in
lemma active_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D) :
    activeAt (fun a => r (loc a)) t z (Q.image r) j ↔ activeAt loc t z Q j := by
  simp only [activeAt,Finset.forall_mem_image,hr]

omit [Fintype D] [DecidableEq X] in
lemma admissible_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t K v z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) :
    admissibleBids (fun a => r (loc a)) t K v z (Q.image r) (r i) tau ↔
      admissibleBids loc t K v z Q i tau := by
  simp only [admissibleBids,active_map r hr loc t z Q,Finset.forall_mem_image,hr]

omit [DecidableEq X] in
lemma payment_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) :
    openingPayment (fun a => r (loc a)) t z (Q.image r) (r i) tau =
      openingPayment loc t z Q i tau := by
  unfold openingPayment
  apply Finset.sum_congr rfl
  intro j _
  rw [active_map r hr loc t z Q j,nearest_map r hr,hr]

omit [DecidableEq X] in
lemma dual_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) (a : D) :
    openingDual (fun j => r (loc j)) t z (Q.image r) (r i) tau a =
      openingDual loc t z Q i tau a := by
  unfold openingDual
  apply Finset.sum_congr rfl
  intro j _
  rw [active_map r hr loc t z Q j,hr,hr]

omit [DecidableEq X] in
lemma openable_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ) (i : X) :
    etaOpenable (fun j => r (loc j)) (F.image r) (Q.image r) t K v z lam eta (r i) ↔
      etaOpenable loc F Q t K v z lam eta i := by
  constructor
  · rintro ⟨tau,ha,hp,hd⟩
    refine ⟨tau,(admissible_map r hr loc t K v z Q i tau).mp ha,?_,?_⟩
    · simpa only [payment_map r hr loc t z Q i tau] using hp
    · intro i₀ hi₀ a hact
      have hh := hd (r i₀) (Finset.mem_image.mpr ⟨i₀,hi₀,rfl⟩) a
        ((active_map r hr loc t z Q a).mpr hact)
      simpa only [dual_map r hr loc t z Q i₀ tau a] using hh
  · rintro ⟨tau,ha,hp,hd⟩
    refine ⟨tau,(admissible_map r hr loc t K v z Q i tau).mpr ha,?_,?_⟩
    · simpa only [payment_map r hr loc t z Q i tau] using hp
    · intro i₀ hi₀ a hact
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hi₀
      simpa only [dual_map r hr loc t z Q i tau a] using hd i hi a
        ((active_map r hr loc t z Q a).mp hact)

lemma entry_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (i : X)
    (h : PhaseSequence.Entry loc F B Q v z lam eta i) :
    PhaseSequence.Entry (fun j => r (loc j)) (F.image r) (B.image r) (Q.image r)
      v z lam eta (r i) := by
  refine ⟨?_,?_⟩
  · simpa only [r.injective.mem_finset_image] using h.1
  · rcases h.2 with hi | ⟨hi,W,hQ,hW,hop⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · right
      refine ⟨Finset.mem_image.mpr ⟨i,hi,rfl⟩,W.image r,Finset.image_subset_image hQ,?_,?_⟩
      · intro x hx
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
        rcases Finset.mem_union.mp (hW hy) with hyF | hyB
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y,hyF,rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hyB,rfl⟩)
      · exact (openable_map r hr loc F W (1-3*v) (1+v^2) v z lam eta i).mpr hop

lemma prefix_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X)
    (h : PhaseSequence.Prefix loc F B v z lam eta Q H) :
    PhaseSequence.Prefix (fun j => r (loc j)) (F.image r) (B.image r) v z lam eta
      (Q.image r) (H.map r) := by
  induction h with
  | nil => exact PhaseSequence.Prefix.nil _
  | cons he ht ih =>
    apply PhaseSequence.Prefix.cons (entry_map r hr loc F B _ v z lam eta _ he)
    simpa only [Finset.image_insert] using ih

omit [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y] in
lemma image_union (r : X → Y) (Q : Finset X) (H : List X) :
    Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
  ext x
  simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
  aesop

omit [DecidableEq X] in
lemma maximal_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (h : PhaseSequence.Maximal loc F Q v z lam) :
    PhaseSequence.Maximal (fun j => r (loc j)) (F.image r) (Q.image r) v z lam := by
  intro x hx hnot hop
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  exact h i hi (fun hiQ => hnot (Finset.mem_image.mpr ⟨i,hiQ,rfl⟩))
    ((openable_map r hr loc F Q (1-3*v) (1+v^2) v z lam 0 i).mp hop)

lemma valid_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X)
    (h : PhaseSequence.Valid loc F B Q v z lam eta H) :
    PhaseSequence.Valid (fun j => r (loc j)) (F.image r) (B.image r) (Q.image r)
      v z lam eta (H.map r) := by
  refine ⟨prefix_map r hr loc F B Q v z lam eta H h.1,?_⟩
  rw [image_union]
  exact maximal_map r hr loc F (Q ∪ H.toFinset) v z lam h.2

theorem history_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q : ℕ) (T : List (List X))
    (h : History loc F B v lam eta q Q T) :
    History (fun j => r (loc j)) (F.image r) (B.image r) v lam eta q (Q.image r)
      (T.map (List.map r)) := by
  induction h with
  | nil => exact History.nil _ _
  | cons hhead htail ih =>
    apply History.cons (valid_map r hr loc F B _ v _ lam eta _ hhead)
    simpa only [image_union] using ih

omit [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y] in
lemma after_map (r : X → Y) (Q : Finset X) (T : List (List X)) :
    after (Q.image r) (T.map (List.map r)) = (after Q T).image r := by
  induction T generalizing Q with
  | nil => rfl
  | cons H T ih =>
    simp only [List.map_cons,after,image_union]
    exact ih _

omit [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y] in
lemma paid_map (r : X ↪ Y) (F Q : Finset X) :
    (Q.image r ∩ F.image r).card = (Q ∩ F).card := by
  rw [← Finset.image_inter _ _ r.injective,Finset.card_image_of_injective _ r.injective]

omit [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y] in
lemma free_map (r : X ↪ Y) (F Q : Finset X) :
    (Q.image r \ F.image r).card = (Q \ F).card := by
  have hp := paid_map r F Q
  have hc := Finset.card_image_of_injective Q r.injective
  have h₁ := Finset.card_inter_add_card_sdiff (Q.image r) (F.image r)
  have h₂ := Finset.card_inter_add_card_sdiff Q F
  omega

end MetricKMedianRecovery.HistoryIsometry

end OAI
