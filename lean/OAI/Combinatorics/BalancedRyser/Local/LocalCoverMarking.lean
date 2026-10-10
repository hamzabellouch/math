import OAI.Combinatorics.BalancedRyser.Local.LocalFourEvents
import OAI.Combinatorics.BalancedRyser.Local.LocalSurplus
import OAI.Combinatorics.BalancedRyser.Probability.PurposefulIndices

namespace OAI

namespace Balanced.Local.Surplus

noncomputable section
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
  (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
  (M : MergedPairs F)

structure CoverAssignment (A : Finset (LocalPiece F)) where
  piece : Fin b × Fin 4 → Option (LocalPiece F)
  precovered : ∀ ij, piece ij = none ↔
    prescribedPoint P a bits M ij ∈ prescribedPartners P a bits p M
  covered : ∀ ij L, piece ij = some L → L ∈ A ∧
    prescribedPoint P a bits M ij ∈ piecePoints M L

theorem badCover_exists_assignment (hbad : BadCover P a bits p M) :
    ∃ A : Finset (LocalPiece F), A.card ≤ b - 1 ∧
      (∀ L ∈ A, AllowedPiece a p M L) ∧
      Nonempty (CoverAssignment P a bits p M A) := by
  obtain ⟨A, hA, hallowed, hcover⟩ := hbad
  have hex : ∀ ij : Fin b × Fin 4, ∃ z : Option (LocalPiece F),
      (z = none ↔ prescribedPoint P a bits M ij ∈ prescribedPartners P a bits p M) ∧
      (∀ L, z = some L → L ∈ A ∧
        prescribedPoint P a bits M ij ∈ piecePoints M L) := by
    intro ij
    by_cases hp : prescribedPoint P a bits M ij ∈ prescribedPartners P a bits p M
    · exact ⟨none, by simp [hp]⟩
    · have hdesignated : prescribedPoint P a bits M ij ∈
          prescribedDesignated P a bits M :=
        Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩
      have hmem := Finset.mem_union.mp (hcover hdesignated)
      obtain ⟨L, hLA, hpL⟩ := Finset.mem_biUnion.mp (hmem.resolve_left hp)
      refine ⟨some L, by simp [hp], ?_⟩
      intro L' heq
      have hLL : L = L' := Option.some.inj heq
      subst L'
      exact ⟨hLA, hpL⟩
  choose f hf using hex
  exact ⟨A, hA, hallowed, ⟨⟨f, fun ij => (hf ij).1,
    fun ij L hL => (hf ij).2 L hL⟩⟩⟩

def pieceExtra (t : Direction F → ℕ) : LocalPiece F → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr d) => t d - 1

def pieceCapacity (t : Direction F → ℕ) (L : LocalPiece F) : ℕ :=
  2 + 2 * pieceExtra t L

omit [Field F] [DecidableEq F] in

theorem sum_pieceExtra_le (A : Finset (LocalPiece F)) (t : Direction F → ℕ) :
    (∑ L ∈ A, pieceExtra t L) ≤ ∑ d : Direction F, (t d - 1) := by
  calc
    (∑ L ∈ A, pieceExtra t L) ≤ ∑ L : LocalPiece F, pieceExtra t L :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = ∑ d : Direction F, (t d - 1) := by
      simp [pieceExtra, Fintype.sum_sum_type]

omit [Field F] [DecidableEq F] in

theorem sum_pieceCapacity_le (A : Finset (LocalPiece F)) (t : Direction F → ℕ) :
    (∑ L ∈ A, pieceCapacity t L) ≤
      2 * A.card + 2 * ∑ d : Direction F, (t d - 1) := by
  unfold pieceCapacity
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h := Nat.mul_le_mul_left 2 (sum_pieceExtra_le A t)
  simpa [Nat.mul_comm] using Nat.add_le_add_left h (2 * A.card)

def assignmentFibre {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (L : LocalPiece F) :
    Finset (Fin b × Fin 4) :=
  Finset.univ.filter (fun ij => f.piece ij = some L)

def protectedFibre {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) : LocalPiece F → Finset (Fin b × Fin 4)
  | Sum.inl _ => ∅
  | Sum.inr (Sum.inl _) => ∅
  | Sum.inr (Sum.inr d) =>
      assignmentFibre P a bits p M f (Sum.inr (Sum.inr d)) ∩
        purposefulDirections P a d

theorem protectedFibre_subset {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (L : LocalPiece F) :
    protectedFibre P a bits p M f L ⊆ assignmentFibre P a bits p M f L := by
  rcases L with U | l | d
  · exact Finset.empty_subset _
  · exact Finset.empty_subset _
  · exact Finset.inter_subset_left

theorem protectedFibre_card_le {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (ha : Function.Injective a.2)
    (L : LocalPiece F) :
    (protectedFibre P a bits p M f L).card ≤
      pieceCapacity (fun d => (FourEvents.usingTuples P a d).card) L := by
  rcases L with U | l | d
  · simp [protectedFibre, pieceCapacity, pieceExtra]
  · simp [protectedFibre, pieceCapacity, pieceExtra]
  · have h := purposefulDirections_card_le P a ha d
    have hp := Finset.card_le_card (Finset.inter_subset_right :
      assignmentFibre P a bits p M f (Sum.inr (Sum.inr d)) ∩
        purposefulDirections P a d ⊆ purposefulDirections P a d)
    change (assignmentFibre P a bits p M f (Sum.inr (Sum.inr d)) ∩
      purposefulDirections P a d).card ≤
        2 + 2 * ((FourEvents.usingTuples P a d).card - 1)
    change (purposefulDirections P a d).card ≤
      2 * (FourEvents.usingTuples P a d).card at h
    omega

theorem badCover_exists_marked_surplus (hb : 1 ≤ b) (hκ : κ ≤ 4 * b)
    (ha : Eligible P a) (hbad : BadCover P a bits p M) :
    ∃ A : Finset (LocalPiece F), A.card ≤ b - 1 ∧
      (∀ L ∈ A, AllowedPiece a p M L) ∧
      ∃ f : CoverAssignment P a bits p M A,
      ∃ R : LocalPiece F → Finset (Fin b × Fin 4),
        (∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L ∧
          R L ⊆ assignmentFibre P a bits p M f L ∧
          (R L).card = min
            (pieceCapacity (fun d => (FourEvents.usingTuples P a d).card) L)
            (assignmentFibre P a bits p M f L).card) ∧
        2 * b + 2 - 2 * κ ≤
          ((Finset.univ : Finset (Fin b × Fin 4)) \ A.biUnion R).card ∧
        (∀ D : Finset (Fin b × Fin 4), D.card ≤ 2 * κ →
          2 * b + 2 - 4 * κ ≤ ((Finset.univ \ A.biUnion R) \ D).card) := by
  obtain ⟨A, hA, hallowed, ⟨f⟩⟩ := badCover_exists_assignment P a bits p M hbad
  let t : Direction F → ℕ := fun d => (FourEvents.usingTuples P a d).card
  obtain ⟨R, hR⟩ := exists_retained_fibres Finset.univ A f.piece
    (protectedFibre P a bits p M f) (pieceCapacity t)
    (fun L _ => protectedFibre_subset P a bits p M f L)
    (fun L _ => protectedFibre_card_le P a bits p M f ha.2.1 L)
  have hRcard : ∀ L ∈ A, (R L).card ≤ pieceCapacity t L := by
    intro L hL
    exact (hR L hL).2.2.trans_le (min_le_left _ _)
  have hcap : (∑ L ∈ A, pieceCapacity t L) ≤ 2 * A.card + 2 * κ := by
    have h := sum_pieceCapacity_le A t
    simpa only [t, FourEvents.sum_direction_excess P a ha.2.1 hκ] using h
  have hU : (Finset.univ : Finset (Fin b × Fin 4)).card = 4 * b := by
    simp [Nat.mul_comm]
  refine ⟨A, hA, hallowed, f, R, hR, ?_, ?_⟩
  · exact source_surplus_card_ge Finset.univ A R (pieceCapacity t) b κ hb hU
      hA hRcard hcap
  · intro D hD
    exact source_independent_surplus_card_ge Finset.univ A R (pieceCapacity t)
      D b κ hb hU hA hRcard hcap hD

theorem assigned_precoverage_marked {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (hR : ∀ L ∈ A, R L ⊆ assignmentFibre P a bits p M f L)
    (ij : Fin b × Fin 4)
    (hp : prescribedPoint P a bits M ij ∈ prescribedPartners P a bits p M) :
    ij ∈ Finset.univ \ A.biUnion R :=
  precovered_mem_surplus Finset.univ A f.piece R hR (Finset.mem_univ _)
    ((f.precovered ij).mpr hp)

theorem assigned_merged_surplus_nonpurposeful {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (hR : ∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L)
    (d : Direction F) (ij : Fin b × Fin 4)
    (hf : f.piece ij = some (Sum.inr (Sum.inr d)))
    (hij : ij ∈ Finset.univ \ A.biUnion R) :
    ij ∉ purposefulDirections P a d := by
  intro hp
  have hA := (f.covered ij _ hf).1
  apply surplus_not_protected Finset.univ A
    (protectedFibre P a bits p M f) R hR hA hij
  exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, hp⟩

theorem assignmentFibre_small_card_le {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (hadm : Admissible P a bits p M)
    (U : Finset (Point F)) (hU : U.card ≤ 2) :
    (assignmentFibre P a bits p M f (Sum.inl U)).card ≤ 2 := by
  have hsub : (assignmentFibre P a bits p M f (Sum.inl U)).image
      (prescribedPoint P a bits M) ⊆ U := by
    intro x hx
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hx
    exact (f.covered ij _ (Finset.mem_filter.mp hij).2).2
  have hc := Finset.card_image_of_injective
    (assignmentFibre P a bits p M f (Sum.inl U)) hadm.2.1
  rw [← hc]
  exact (Finset.card_le_card hsub).trans hU

theorem retained_eq_fibre_of_fits {α : Type*} [DecidableEq α]
    (R U : Finset α) (c : ℕ) (hR : R ⊆ U)
    (hcard : R.card = min c U.card) (hfit : U.card ≤ c) : R = U := by
  apply Finset.eq_of_subset_of_card_le hR
  rw [hcard, min_eq_right hfit]

theorem small_piece_not_surplus {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A) (hadm : Admissible P a bits p M)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (U : Finset (Point F)) (hU : U.card ≤ 2)
    (hR : R (Sum.inl U) ⊆ assignmentFibre P a bits p M f (Sum.inl U))
    (hcard : (R (Sum.inl U)).card =
      min 2 (assignmentFibre P a bits p M f (Sum.inl U)).card)
    (ij : Fin b × Fin 4) (hf : f.piece ij = some (Sum.inl U)) :
    ij ∉ Finset.univ \ A.biUnion R := by
  intro hij
  have heq := retained_eq_fibre_of_fits _ _ 2 hR hcard
    (assignmentFibre_small_card_le P a bits p M f hadm U hU)
  apply (Finset.mem_sdiff.mp hij).2
  apply Finset.mem_biUnion.mpr
  refine ⟨Sum.inl U, (f.covered ij _ hf).1, ?_⟩
  rw [heq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩

theorem exists_two_anchors_of_surplus {α : Type*} [DecidableEq α]
    (R U : Finset α) (hR : R ⊆ U) (hcard : R.card = min 2 U.card)
    (x : α) (hx : x ∈ U \ R) :
    ∃ u v : α, R = {u, v} ∧ u ≠ v ∧ x ≠ u ∧ x ≠ v := by
  have hsize : 2 ≤ U.card := by
    by_contra hn
    have heq := retained_eq_fibre_of_fits R U 2 hR hcard (by omega)
    have hnot := (Finset.mem_sdiff.mp hx).2
    exact hnot (heq.symm ▸ (Finset.mem_sdiff.mp hx).1)
  have htwo : R.card = 2 := by rw [hcard, min_eq_left hsize]
  obtain ⟨u, v, huv, hRuv⟩ := Finset.card_eq_two.mp htwo
  refine ⟨u, v, hRuv, huv, ?_, ?_⟩
  · intro heq
    exact (Finset.mem_sdiff.mp hx).2 (by simp [hRuv, heq])
  · intro heq
    exact (Finset.mem_sdiff.mp hx).2 (by simp [hRuv, heq])

theorem assigned_surplus_two_anchors {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4)) (L : LocalPiece F)
    (hR : R L ⊆ assignmentFibre P a bits p M f L)
    (hcard : (R L).card = min 2 (assignmentFibre P a bits p M f L).card)
    (ij : Fin b × Fin 4) (hf : f.piece ij = some L)
    (hij : ij ∈ Finset.univ \ A.biUnion R) :
    ∃ u v : Fin b × Fin 4, R L = {u, v} ∧ u ≠ v ∧ ij ≠ u ∧ ij ≠ v ∧
      f.piece u = some L ∧ f.piece v = some L := by
  have hLA := (f.covered ij L hf).1
  have hnot : ij ∉ R L := by
    intro hmem
    exact (Finset.mem_sdiff.mp hij).2 (Finset.mem_biUnion.mpr ⟨L, hLA, hmem⟩)
  obtain ⟨u, v, hpair, huv, hiu, hiv⟩ := exists_two_anchors_of_surplus
    (R L) (assignmentFibre P a bits p M f L) hR hcard ij
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, hnot⟩)
  refine ⟨u, v, hpair, huv, hiu, hiv, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (hR (by simp [hpair]))).2
  · exact (Finset.mem_filter.mp (hR (by simp [hpair]))).2

end
end Balanced.Local.Surplus

end OAI
