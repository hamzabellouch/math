import OAI.Combinatorics.BalancedRyser.Local.LocalCoverMarking
import OAI.Combinatorics.BalancedRyser.Local.LocalParentMap

namespace OAI

namespace Balanced.Local.MarkedAnchors

noncomputable section
open scoped Classical
open Surplus

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (p : Point F) (M : MergedPairs F)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem mem_purposefulIndices (c : Fin (4 * b - κ))
    (v : Fin b × Fin 4) :
    v ∈ purposefulIndices P c ↔ AnchorExclusion.Purposeful P c v := by
  simp [purposefulIndices, AnchorExclusion.Purposeful]

omit [Field F] [Fintype F] in
@[simp] theorem mem_purposefulDirections (ha : Function.Injective a.2)
    (c : Fin (4 * b - κ)) (v : Fin b × Fin 4) :
    v ∈ purposefulDirections P a (a.2 c) ↔ AnchorExclusion.Purposeful P c v := by
  simp [purposefulDirections, AnchorExclusion.Purposeful, ha.eq_iff]

omit [Field F] [Fintype F] [DecidableEq F] in

theorem marked_not_retained {A : Finset (LocalPiece F)}
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    {L : LocalPiece F} (hL : L ∈ A) {v : Fin b × Fin 4}
    (hv : v ∈ Finset.univ \ A.biUnion R) : v ∉ R L := by
  intro hvr
  exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨L, hL, hvr⟩)

theorem retained_pair_of_marked {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (L : LocalPiece F)
    (hR : R L ⊆ assignmentFibre P a bits p M f L)
    (hcard : (R L).card = min 2 (assignmentFibre P a bits p M f L).card)
    (v : Fin b × Fin 4) (hf : f.piece v = some L)
    (hv : v ∈ Finset.univ \ A.biUnion R) :
    ∃ x ∈ R L, ∃ y ∈ R L, x ≠ y ∧ x ≠ v ∧ y ≠ v := by
  have hn := marked_not_retained R (f.covered v L hf).1 hv
  have hfv : v ∈ assignmentFibre P a bits p M f L :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
  have hbig : 2 < (assignmentFibre P a bits p M f L).card := by
    by_contra h
    have heq := retained_eq_fibre_of_fits _ _ 2 hR hcard (by omega)
    exact hn (heq.symm ▸ hfv)
  have htwo : (R L).card = 2 := by
    rw [hcard, min_eq_left (by omega)]
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < (R L).card by omega)
  exact ⟨x, hx, y, hy, hxy, fun h => hn (h ▸ hx), fun h => hn (h ▸ hy)⟩

theorem retained_mem_piece {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (L : LocalPiece F)
    (hR : R L ⊆ assignmentFibre P a bits p M f L)
    {x : Fin b × Fin 4} (hx : x ∈ R L) :
    prescribedPoint P a bits M x ∈ piecePoints M L :=
  (f.covered x L (Finset.mem_filter.mp (hR hx)).2).2

theorem ordinary_marked_anchors {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    (l : Line F) (hl : AllowedPiece a p M (Sum.inr (Sum.inl l)))
    (hR : R (Sum.inr (Sum.inl l)) ⊆
      assignmentFibre P a bits p M f (Sum.inr (Sum.inl l)))
    (hcard : (R (Sum.inr (Sum.inl l))).card =
      min 2 (assignmentFibre P a bits p M f (Sum.inr (Sum.inl l))).card)
    (v : Fin b × Fin 4) (hf : f.piece v = some (Sum.inr (Sum.inl l)))
    (hv : v ∈ Finset.univ \ A.biUnion R)
    (hvd : v ∉ ParentMap.dependent child s) :
    ∃ x ∈ R (Sum.inr (Sum.inl l)), ∃ y ∈ R (Sum.inr (Sum.inl l)),
      x ≠ y ∧ prescribedPoint P a bits M x ≠ prescribedPoint P a bits M y ∧
      OnLine (prescribedPoint P a bits M x) l ∧
      OnLine (prescribedPoint P a bits M y) l ∧
      ParentMap.underlying root child r s (bits root r) (bits child s) x ≠ v ∧
      ParentMap.underlying root child r s (bits root r) (bits child s) y ≠ v := by
  obtain ⟨x, hx, y, hy, hxy, hxv, hyv⟩ :=
    retained_pair_of_marked P a bits p M f R _ hR hcard v hf hv
  have hvl : OnLine (prescribedPoint P a bits M v) l :=
    (Finset.mem_filter.mp (f.covered v _ hf).2).2
  have hxl : OnLine (prescribedPoint P a bits M x) l :=
    (Finset.mem_filter.mp (retained_mem_piece P a bits p M f R _ hR hx)).2
  have hyl : OnLine (prescribedPoint P a bits M y) l :=
    (Finset.mem_filter.mp (retained_mem_piece P a bits p M f R _ hR hy)).2
  exact ⟨x, hx, y, hy, hxy, fun h => hxy (hadm.2.1 h), hxl, hyl,
    ParentMap.ordinary_anchor_not_self P a bits M ha p hadm root child r s
      hshared hvd hxv l hl hvl hxl,
    ParentMap.ordinary_anchor_not_self P a bits M ha p hadm root child r s
      hshared hvd hyv l hl hvl hyl⟩

theorem unused_marked_anchor {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (root child : Fin b) (r s : Fin 4)
    (d : Direction F) (hd : d ∉ FourEvents.usedDirections a)
    (hR : R (Sum.inr (Sum.inr d)) ⊆
      assignmentFibre P a bits p M f (Sum.inr (Sum.inr d)))
    (hcard : (R (Sum.inr (Sum.inr d))).card =
      min (pieceCapacity (fun e => (FourEvents.usingTuples P a e).card)
        (Sum.inr (Sum.inr d)))
        (assignmentFibre P a bits p M f (Sum.inr (Sum.inr d))).card)
    (v : Fin b × Fin 4) (hf : f.piece v = some (Sum.inr (Sum.inr d)))
    (hv : v ∈ Finset.univ \ A.biUnion R) :
    ∃ x ∈ R (Sum.inr (Sum.inr d)), x ≠ v ∧
      prescribedPoint P a bits M x ∈ mergedPoints M d ∧
      ParentMap.underlying root child r s (bits root r) (bits child s) x ≠ v := by
  have hcap : pieceCapacity (fun e => (FourEvents.usingTuples P a e).card)
      (Sum.inr (Sum.inr d)) = 2 := by
    simp [pieceCapacity, pieceExtra, FourEvents.usingTuples_eq_empty_of_not_used P a d hd]
  rw [hcap] at hcard
  obtain ⟨x, hx, y, hy, hxy, hxv, hyv⟩ :=
    retained_pair_of_marked P a bits p M f R _ hR hcard v hf hv
  rcases ParentMap.two_anchors_not_both_self root child r s
      (bits root r) (bits child s) hxv hyv hxy with hnx | hny
  · exact ⟨x, hx, hxv, retained_mem_piece P a bits p M f R _ hR hx, hnx⟩
  · exact ⟨y, hy, hyv, retained_mem_piece P a bits p M f R _ hR hy, hny⟩

omit [Fintype F] [DecidableEq F] in

theorem exists_purposeful_endpoint (ha : Eligible P a)
    (c : Fin (4 * b - κ)) (t : Bool) :
    ∃ x : Fin b × Fin 4, AnchorExclusion.Purposeful P c x ∧
      OnLine (prescribedPoint P a bits M x) (constituent M (a.2 c) t) := by
  obtain ⟨⟨i, j⟩, hij⟩ := P.everyClass c
  refine ⟨(i, ParentMap.endpointIndex j (bits i j) t), ?_, ?_⟩
  · simpa only [hij] using ParentMap.endpoint_purposeful P bits i j t
  · simpa only [hij] using ParentMap.endpoint_on_constituent P a bits M ha i j t

theorem used_marked_anchor {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Fin b × Fin 4))
    (hR : ∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L)
    (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    (c : Fin (4 * b - κ))
    (v : Fin b × Fin 4) (hf : f.piece v = some (Sum.inr (Sum.inr (a.2 c))))
    (hv : v ∈ Finset.univ \ A.biUnion R)
    (hvd : v ∉ ParentMap.dependent child s) :
    ∃ t : Bool, ∃ x : Fin b × Fin 4,
      AnchorExclusion.Purposeful P c x ∧ x ≠ v ∧
      OnLine (prescribedPoint P a bits M v) (constituent M (a.2 c) t) ∧
      OnLine (prescribedPoint P a bits M x) (constituent M (a.2 c) t) ∧
      ParentMap.underlying root child r s (bits root r) (bits child s) x ≠ v := by
  have hnp : ¬ AnchorExclusion.Purposeful P c v := by
    intro hp
    exact assigned_merged_surplus_nonpurposeful P a bits p M f R hR (a.2 c) v hf hv
      ((mem_purposefulDirections P a ha.2.1 c v).mpr hp)
  have hvm : prescribedPoint P a bits M v ∈ mergedPoints M (a.2 c) :=
    (f.covered v _ hf).2
  have ht : ∃ t : Bool,
      OnLine (prescribedPoint P a bits M v) (constituent M (a.2 c) t) := by
    simpa only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.exists_bool] using hvm
  obtain ⟨t, hvt⟩ := ht
  obtain ⟨x, hxp, hxt⟩ := exists_purposeful_endpoint P a bits M ha c t
  have hxv : x ≠ v := fun h => hnp (h ▸ hxp)
  exact ⟨t, x, hxp, hxv, hvt, hxt,
    ParentMap.used_pair_anchor_not_self P a bits M ha p hadm root child r s
      hshared hvd hxv c t hnp hvt hxt⟩

theorem constituent_ne_target (hadm : Admissible P a bits p M)
    (d : Direction F) (t : Bool) (v : Fin b × Fin 4) :
    constituent M d t ≠ lineThrough (a.1 v.1) p := by
  intro heq
  apply hadm.2.2.2.1 v.1
  rw [← heq]
  exact Finset.mem_image.mpr ⟨(d, t), Finset.mem_univ _, rfl⟩

theorem ordinary_ne_target (l : Line F)
    (hl : AllowedPiece a p M (Sum.inr (Sum.inl l))) (v : Fin b × Fin 4) :
    l ≠ lineThrough (a.1 v.1) p := by
  intro heq
  apply hl
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨v.1, Finset.mem_univ _, heq.symm⟩)

end
end Balanced.Local.MarkedAnchors

end OAI
