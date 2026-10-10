import OAI.Combinatorics.BalancedRyser.Profiles.LocalMarkedAnchors

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open Surplus MarkedAnchors

abbrev Position (b : ℕ) := Fin b × Fin 4

abbrev Code (b κ : ℕ) := Unit ⊕
  ((Position b × Position b) ⊕ (Position b ⊕ (Fin (4 * b - κ) × Position b)))

def anchors {b κ : ℕ} : Code b κ → Finset (Position b)
  | Sum.inl _ => ∅
  | Sum.inr (Sum.inl xy) => {xy.1, xy.2}
  | Sum.inr (Sum.inr (Sum.inl x)) => {x}
  | Sum.inr (Sum.inr (Sum.inr cx)) => {cx.2}

def underlyingAnchors {b κ : ℕ} (u : Position b → Position b)
    (z : Code b κ) : Finset (Position b) := (anchors z).image u

theorem anchors_card_le_two {b κ : ℕ} (z : Code b κ) : (anchors z).card ≤ 2 := by
  rcases z with _ | xy | x | cx
  · simp [anchors]
  · exact Finset.card_le_two
  · simp [anchors]
  · simp [anchors]

theorem underlyingAnchors_card_le_two {b κ : ℕ} (u : Position b → Position b)
    (z : Code b κ) : (underlyingAnchors u z).card ≤ 2 :=
  Finset.card_image_le.trans (anchors_card_le_two z)

theorem card_code (b κ : ℕ) :
    Fintype.card (Code b κ) = 1 + (4 * b) ^ 2 + 4 * b + (4 * b - κ) * (4 * b) := by
  simp only [Code, Position, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_unit, Fintype.card_fin]
  ring

theorem card_code_le (b κ : ℕ) (hb : 1 ≤ b) :
    Fintype.card (Code b κ) ≤ 37 * b ^ 2 := by
  rw [card_code]
  have hκ : 4 * b - κ ≤ 4 * b := Nat.sub_le _ _
  have hmul := Nat.mul_le_mul_right (4 * b) hκ
  nlinarith [Nat.mul_self_le_mul_self hb]

theorem card_test_code_le (b κ : ℕ) (hb : 1 ≤ b) :
    Fintype.card (Position b × Code b κ) ≤ 148 * b ^ 3 := by
  rw [Fintype.card_prod]
  have h := Nat.mul_le_mul_left (4 * b) (card_code_le b κ hb)
  simpa [Position, Nat.mul_comm, Nat.mul_left_comm, pow_succ, Nat.mul_assoc] using h

theorem card_specifications_le (b κ : ℕ) (hb : 1 ≤ b) :
    Fintype.card (Fin (3 - κ) → Position b × Code b κ) ≤ (148 * b ^ 3) ^ 3 := by
  rw [Fintype.card_fun, Fintype.card_fin]
  apply (Nat.pow_le_pow_left (card_test_code_le b κ hb) (3 - κ)).trans
  exact Nat.pow_le_pow_right (by positivity) (Nat.sub_le _ _)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (p : Point F) (M : MergedPairs F)

def Holds (v : Position b) : Code b κ → Prop
  | Sum.inl _ => ∃ d : Direction F, d ∉ FourEvents.usedDirections a ∧
      ∃ t : Bool, OnLine p (constituent M d t) ∧
        OnLine (prescribedPoint P a bits M v) (constituent M d (!t)) ∧
        constituent M d (!t) ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inl xy) =>
      prescribedPoint P a bits M xy.1 ≠ prescribedPoint P a bits M xy.2 ∧
      OnLine (prescribedPoint P a bits M v)
        (joiningLine (prescribedPoint P a bits M xy.1) (prescribedPoint P a bits M xy.2)) ∧
      joiningLine (prescribedPoint P a bits M xy.1) (prescribedPoint P a bits M xy.2) ≠
        lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inr (Sum.inl x)) =>
      ∃ d : Direction F, d ∉ FourEvents.usedDirections a ∧
        prescribedPoint P a bits M x ∈ mergedPoints M d ∧
        ∃ t : Bool, OnLine (prescribedPoint P a bits M v) (constituent M d t) ∧
          constituent M d t ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inr (Sum.inr cx)) =>
      OnLine (prescribedPoint P a bits M v)
        (lineThrough (a.2 cx.1) (prescribedPoint P a bits M cx.2)) ∧
      lineThrough (a.2 cx.1) (prescribedPoint P a bits M cx.2) ≠
        lineThrough (a.1 v.1) p

theorem marked_exists_spec {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Position b))
    (hallowed : ∀ L ∈ A, AllowedPiece a p M L)
    (hR : ∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L ∧
      R L ⊆ assignmentFibre P a bits p M f L ∧
      (R L).card = min
        (pieceCapacity (fun d => (FourEvents.usingTuples P a d).card) L)
        (assignmentFibre P a bits p M f L).card)
    (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s)
    (v : Position b) (hv : v ∈ Finset.univ \ A.biUnion R)
    (hvd : v ∉ ParentMap.dependent child s) :
    ∃ z : Code b κ, Holds P a bits p M v z ∧
      v ∉ underlyingAnchors
        (ParentMap.underlying root child r s (bits root r) (bits child s)) z := by
  cases hfv : f.piece v with
  | none =>
      have hp := (f.precovered v).mp hfv
      obtain ⟨_, ⟨d, t⟩, hd, hpt, hvt⟩ :=
        (PrescribedGeometry.mem_prescribedPartners_iff_unused ha hadm _).mp hp
      refine ⟨Sum.inl (), ?_, by simp [underlyingAnchors, anchors]⟩
      exact ⟨d, hd, t, hpt, hvt, constituent_ne_target P a bits p M hadm d (!t) v⟩
  | some L =>
      have hLA := (f.covered v L hfv).1
      have hret := hR L hLA
      rcases L with U | l | d
      · exact False.elim (small_piece_not_surplus P a bits p M f hadm R U
          (hallowed _ hLA) hret.2.1 hret.2.2 v hfv hv)
      · obtain ⟨x, hx, y, hy, hxy, hpoints, hxl, hyl, hnx, hny⟩ :=
          ordinary_marked_anchors P a bits p M f R ha hadm root child r s hshared
            l (hallowed _ hLA) hret.2.1 hret.2.2 v hfv hv hvd
        have hvl : OnLine (prescribedPoint P a bits M v) l :=
          (Finset.mem_filter.mp (f.covered v _ hfv).2).2
        have heq : joiningLine (prescribedPoint P a bits M x)
            (prescribedPoint P a bits M y) = l :=
          (eq_of_two_common_points _ _ hpoints l _ hxl hyl
            (onLine_joiningLine_left _ _) (onLine_joiningLine_right _ _)).symm
        refine ⟨Sum.inr (Sum.inl (x, y)), ?_, ?_⟩
        · change _ ∧ _ ∧ _
          rw [heq]
          exact ⟨hpoints, hvl, ordinary_ne_target a p M l (hallowed _ hLA) v⟩
        · simpa [underlyingAnchors, anchors, eq_comm] using And.intro hnx hny
      · by_cases hd : d ∈ FourEvents.usedDirections a
        · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
          obtain ⟨t, x, hxp, hxv, hvt, hxt, hnx⟩ :=
            used_marked_anchor P a bits p M f R (fun L hL => (hR L hL).1)
              ha hadm root child r s hshared c v hfv hv hvd
          have heq : lineThrough (a.2 c) (prescribedPoint P a bits M x) =
              constituent M (a.2 c) t := (line_eq_lineThrough _ _ hxt).symm
          refine ⟨Sum.inr (Sum.inr (Sum.inr (c, x))), ?_, ?_⟩
          · change _ ∧ _
            rw [heq]
            exact ⟨hvt, constituent_ne_target P a bits p M hadm (a.2 c) t v⟩
          · simpa [underlyingAnchors, anchors, eq_comm] using hnx
        · obtain ⟨x, hx, hxv, hxm, hnx⟩ :=
            unused_marked_anchor P a bits p M f R root child r s d hd
              hret.2.1 hret.2.2 v hfv hv
          have hvm : prescribedPoint P a bits M v ∈ mergedPoints M d :=
            (f.covered v _ hfv).2
          have ht : ∃ t : Bool,
              OnLine (prescribedPoint P a bits M v) (constituent M d t) := by
            simpa only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
              Finset.mem_univ, true_and, Bool.exists_bool] using hvm
          obtain ⟨t, hvt⟩ := ht
          refine ⟨Sum.inr (Sum.inr (Sum.inl x)), ?_, ?_⟩
          · exact ⟨d, hd, hxm, t, hvt, constituent_ne_target P a bits p M hadm d t v⟩
          · simpa [underlyingAnchors, anchors, eq_comm] using hnx

theorem underlying_diagonal (i : Fin b) (s : Fin 4) (t : Bool) (x : Position b) :
    ParentMap.underlying i i s s t t x = x := by
  cases t <;> simp only [ParentMap.underlying, ParentMap.endpointIndex,
    Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, Bool.true_eq_false, ite_false]
  all_goals split_ifs <;> simp_all

theorem marked_exists_identity_spec {A : Finset (LocalPiece F)}
    (f : CoverAssignment P a bits p M A)
    (R : LocalPiece F → Finset (Position b))
    (hallowed : ∀ L ∈ A, AllowedPiece a p M L)
    (hR : ∀ L ∈ A, protectedFibre P a bits p M f L ⊆ R L ∧
      R L ⊆ assignmentFibre P a bits p M f L ∧
      (R L).card = min
        (pieceCapacity (fun d => (FourEvents.usingTuples P a d).card) L)
        (assignmentFibre P a bits p M f L).card)
    (hb : 3 ≤ b) (ha : Eligible P a) (hadm : Admissible P a bits p M)
    (v : Position b) (hv : v ∈ Finset.univ \ A.biUnion R) :
    ∃ z : Code b κ, Holds P a bits p M v z ∧ v ∉ anchors z := by
  obtain ⟨i, hi, _⟩ := Fin.exists_ne_and_ne_of_two_lt v.1 v.1 (by omega)
  have hvd : v ∉ ParentMap.dependent i 0 := by
    simp [ParentMap.dependent, Prod.ext_iff, hi.symm]
  obtain ⟨z, hz, hn⟩ := marked_exists_spec P a bits p M f R hallowed hR ha hadm
    i i 0 0 rfl v hv hvd
  refine ⟨z, hz, ?_⟩
  simpa [underlyingAnchors, underlying_diagonal] using hn

end
end Balanced.Local.ConditionSpec

end OAI
