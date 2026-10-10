import OAI.NumberTheory.Ostmann.Arithmetic.BulkRegularSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullSupport

namespace OAI

/-! # The retained nonbulk coprimality support for the complete sampled tree -/

namespace Ostmann
open scoped Classical

theorem prime_list_outside_pairwise_iff_nonbulk {σ : Type*} (value : σ → ℕ)
    (bulk : σ → Bool) (L : List σ) (outside : List ℕ)
    (hprime : ∀ i ∈ L, (value i).Prime) (hnodup : (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ i ∈ L, ∀ j ∈ L, bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ i ∈ L, bulk i = true → ∀ p ∈ outside, (value i).Coprime p) :
    (L.map value ++ outside).Pairwise Nat.Coprime ↔
      ((L.filter fun i => !(bulk i)).map value ++ outside).Pairwise Nat.Coprime := by
  rw [List.pairwise_append, List.pairwise_append,
    prime_list_pairwise_iff_nonbulk value bulk L hprime hnodup hinj hcross]
  constructor
  · rintro ⟨hl, ho, hc⟩
    refine ⟨hl, ho, ?_⟩
    intro v hv p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hc _ (List.mem_map.mpr ⟨i, (List.mem_filter.mp hi).1, rfl⟩) p hp
  · rintro ⟨hl, ho, hc⟩
    refine ⟨hl, ho, ?_⟩
    intro v hv p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    cases hb : bulk i with
    | true => exact hout i hi hb p hp
    | false => exact hc _ (List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hb]⟩, rfl⟩) p hp

def MovingSlotData.regularLists {σ : Type*} : {n : ℕ} → MovingSlotData σ n → List (List σ)
  | _, .leaf _ regular => [regular]
  | _, .node _ CL CR _ left right => (CL ++ CR) :: (left.regularLists ++ right.regularLists)

theorem movingRegularOutsidePairwise_iff_lists {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) :
    movingRegularOutsidePairwise value outside T ↔
      ∀ L ∈ T.regularLists, (L.map value ++ outside).Pairwise Nat.Coprime := by
  induction T with
  | leaf => simp [movingRegularOutsidePairwise, MovingSlotData.regularLists, MovingSlotData.regularSlots]
  | node s CL CR U left right ihL ihR =>
    simp only [movingRegularOutsidePairwise, MovingSlotData.regularSlots,
      MovingSlotData.regularLists, List.mem_cons, List.mem_append, or_imp, forall_and,
      forall_eq, ihL, ihR]

def movingNonbulkOutsidePairwise {σ : Type*} (value : σ → ℕ) (bulk : σ → Bool)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) : Prop :=
  ∀ L ∈ T.regularLists, ((L.filter fun i => !(bulk i)).map value ++ outside).Pairwise Nat.Coprime

theorem movingRegularOutsidePairwise_iff_nonbulk {σ : Type*} (value : σ → ℕ)
    (bulk : σ → Bool) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hprime : ∀ L ∈ T.regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ L ∈ T.regularLists, (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ L ∈ T.regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ L ∈ T.regularLists, ∀ i ∈ L, bulk i = true →
      ∀ p ∈ outside, (value i).Coprime p) :
    movingRegularOutsidePairwise value outside T ↔ movingNonbulkOutsidePairwise value bulk outside T := by
  rw [movingRegularOutsidePairwise_iff_lists]
  exact forall_congr' fun L => forall_congr' fun hL =>
    prime_list_outside_pairwise_iff_nonbulk value bulk L outside (hprime L hL)
      (hnodup L hL) hinj (hcross L hL) (hout L hL)

theorem movingNonbulkOutsidePairwise_congr {σ : Type*} (v w : σ → ℕ)
    (bulk : σ → Bool) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hv : ∀ i, bulk i = false → v i = w i) :
    movingNonbulkOutsidePairwise v bulk outside T ↔ movingNonbulkOutsidePairwise w bulk outside T := by
  have he (L : List σ) : (L.filter fun i => !(bulk i)).map v =
      (L.filter fun i => !(bulk i)).map w := by
    apply List.map_congr_left
    intro i hi
    apply hv
    simpa using (List.mem_filter.mp hi).2
  unfold movingNonbulkOutsidePairwise
  simp_rw [he]

theorem movingRegularOutsidePairwise_frozen {σ : Type*} (value base : σ → ℕ)
    (bulk : σ → Bool) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hv : ∀ i, bulk i = false → value i = base i)
    (hprime : ∀ L ∈ T.regularLists, ∀ i ∈ L, (value i).Prime)
    (hnodup : ∀ L ∈ T.regularLists, (L.filter bulk).Nodup)
    (hinj : ∀ i j, bulk i = true → bulk j = true → value i = value j → i = j)
    (hcross : ∀ L ∈ T.regularLists, ∀ i ∈ L, ∀ j ∈ L,
      bulk i ≠ bulk j → value i ≠ value j)
    (hout : ∀ L ∈ T.regularLists, ∀ i ∈ L, bulk i = true →
      ∀ p ∈ outside, (value i).Coprime p) :
    movingRegularOutsidePairwise value outside T ↔ movingNonbulkOutsidePairwise base bulk outside T :=
  (movingRegularOutsidePairwise_iff_nonbulk value bulk outside T hprime hnodup hinj hcross hout).trans
    (movingNonbulkOutsidePairwise_congr value base bulk outside T hv)

end Ostmann

end OAI
