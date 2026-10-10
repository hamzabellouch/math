import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Probability.ConfigurationStructure

namespace OAI

namespace Balanced.Local.ConfigurationPattern
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F) (hV : C.Valid) (hC : C.Compatible) (p : Point F)

def slots : Finset (Slot F) :=
  Finset.univ.filter (fun s => OnLine p (C.choice s).line)

def slotEquiv : Fin (C.splitMultiplicity p) ≃ {s // s ∈ slots C p} :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact (ConfigurationStructure.split_multiplicity_eq_slots C hV hC p).symm)).symm

def slot (i : Fin (C.splitMultiplicity p)) : Slot F :=
  (slotEquiv C hV hC p i).val

theorem slot_injective : Function.Injective (slot C hV hC p) :=
  Subtype.val_injective.comp (slotEquiv C hV hC p).injective

theorem slot_onLine (i : Fin (C.splitMultiplicity p)) :
    OnLine p (C.choice (slot C hV hC p i)).line :=
  (Finset.mem_filter.mp (slotEquiv C hV hC p i).property).2

theorem exists_slot {s : Slot F} (hs : OnLine p (C.choice s).line) :
    ∃ i, slot C hV hC p i = s := by
  let t : {s // s ∈ slots C p} := ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
  refine ⟨(slotEquiv C hV hC p).symm t, ?_⟩
  exact congrArg Subtype.val ((slotEquiv C hV hC p).apply_symm_apply t)

theorem slot_direction_injective :
    Function.Injective (fun i => (slot C hV hC p i).1) := by
  intro i j hij
  apply slot_injective C hV hC p
  apply ConfigurationStructure.choice_line_injective C hV hC
  apply eq_of_onLine_same_direction p
  · exact (hV.2 _).1.trans (hij.trans (hV.2 _).1.symm)
  · exact slot_onLine C hV hC p i
  · exact slot_onLine C hV hC p j

theorem slot_line_eq (i : Fin (C.splitMultiplicity p)) :
    (C.choice (slot C hV hC p i)).line =
      lineThrough (slot C hV hC p i).1 p := by
  apply eq_of_onLine_same_direction p
  · exact (hV.2 _).1
  · exact slot_onLine C hV hC p i
  · exact onLine_lineThrough _ _

def point (ij : Fin (C.splitMultiplicity p) × Fin 4) : Point F :=
  tuplePoint C.merged (C.choice (slot C hV hC p ij.1)).tuple ij.2

theorem point_injective : Function.Injective (point C hV hC p) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  have hi : slot C hV hC p i = slot C hV hC p j := by
    apply ConfigurationStructure.designated_slot_unique C hC
      (p := point C hV hC p (i, a))
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    · rw [he]
      exact (hV.2 _).2.2.2.2.2.1 b
  have hij := slot_injective C hV hC p hi
  subst j
  have hab : a = b := (hV.2 _).2.2.2.2.1 he
  exact Prod.ext rfl hab

theorem point_ne_center (hb : 2 ≤ C.splitMultiplicity p)
    (ij : Fin (C.splitMultiplicity p) × Fin 4) : point C hV hC p ij ≠ p := by
  intro he
  apply ConfigurationStructure.center_not_designated C hC hb (slot C hV hC p ij.1)
  have hx : point C hV hC p ij ∈
      designated C.merged (C.choice (slot C hV hC p ij.1)) :=
    Finset.mem_image.mpr ⟨ij.2, Finset.mem_univ _, rfl⟩
  simpa only [he] using hx

theorem point_image : Finset.univ.image (point C hV hC p) = C.designatedAt p := by
  ext x
  constructor
  · rintro hx
    obtain ⟨⟨i, a⟩, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨slot C hV hC p i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, slot_onLine C hV hC p i⟩,
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i, rfl⟩ := exists_slot C hV hC p (Finset.mem_filter.mp hs).2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨(i, a), Finset.mem_univ _, rfl⟩

def generator (ij : Fin (C.splitMultiplicity p) × Fin 4) : Direction F :=
  (C.choice (slot C hV hC p ij.1)).tuple.generator ij.2

theorem generator_image :
    Finset.univ.image (generator C hV hC p) = generatorUnionAt C p := by
  ext d
  constructor
  · intro hd
    obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_biUnion.mpr ⟨slot C hV hC p i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, slot_onLine C hV hC p i⟩,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  · intro hd
    obtain ⟨s, hs, hd⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨i, rfl⟩ := exists_slot C hV hC p (Finset.mem_filter.mp hs).2
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

include hV hC

theorem generator_card_le :
    (generatorUnionAt C p).card ≤ 4 * C.splitMultiplicity p := by
  rw [← generator_image C hV hC p]
  simpa [Nat.mul_comm] using
    (Finset.card_image_le (s := Finset.univ) (f := generator C hV hC p))

theorem generator_card_eq :
    (generatorUnionAt C p).card = 4 * C.splitMultiplicity p - reuseCount C p := by
  exact (Nat.sub_sub_self (generator_card_le C hV hC p)).symm

def generatorEquiv : {d // d ∈ generatorUnionAt C p} ≃
    Fin (4 * C.splitMultiplicity p - reuseCount C p) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact generator_card_eq C hV hC p)

theorem generator_mem (ij : Fin (C.splitMultiplicity p) × Fin 4) :
    generator C hV hC p ij ∈ generatorUnionAt C p := by
  rw [← generator_image C hV hC p]
  exact Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩

def classOf (i : Fin (C.splitMultiplicity p)) (j : Fin 4) :
    Fin (4 * C.splitMultiplicity p - reuseCount C p) :=
  generatorEquiv C hV hC p ⟨generator C hV hC p (i, j), generator_mem C hV hC p (i, j)⟩

def assignedGenerator (k : Fin (4 * C.splitMultiplicity p - reuseCount C p)) :
    Direction F := ((generatorEquiv C hV hC p).symm k).val

theorem assignedGenerator_injective : Function.Injective (assignedGenerator C hV hC p) :=
  Subtype.val_injective.comp (generatorEquiv C hV hC p).symm.injective

theorem assigned_class (i : Fin (C.splitMultiplicity p)) (j : Fin 4) :
    assignedGenerator C hV hC p (classOf C hV hC p i j) =
      (C.choice (slot C hV hC p i)).tuple.generator j := by
  exact congrArg Subtype.val ((generatorEquiv C hV hC p).symm_apply_apply _)

theorem class_surjective :
    Function.Surjective (fun ij : Fin (C.splitMultiplicity p) × Fin 4 =>
      classOf C hV hC p ij.1 ij.2) := by
  intro k
  have hd := ((generatorEquiv C hV hC p).symm k).property
  have hd' : assignedGenerator C hV hC p k ∈ Finset.univ.image (generator C hV hC p) := by
    rw [generator_image]
    exact hd
  obtain ⟨⟨i, j⟩, _, he⟩ := Finset.mem_image.mp hd'
  refine ⟨(i, j), ?_⟩
  apply assignedGenerator_injective C hV hC p
  exact (assigned_class C hV hC p i j).trans he

theorem class_injective (i : Fin (C.splitMultiplicity p)) :
    Function.Injective (classOf C hV hC p i) := by
  intro j k h
  apply (hV.2 (slot C hV hC p i)).2.2.1
  simpa only [assigned_class] using congrArg (assignedGenerator C hV hC p) h

theorem assigned_mem_generators {i : Fin (C.splitMultiplicity p)}
    {k : Fin (4 * C.splitMultiplicity p - reuseCount C p)}
    (hk : k ∈ Finset.univ.image (classOf C hV hC p i)) :
    assignedGenerator C hV hC p k ∈ generatorSet (C.choice (slot C hV hC p i)).tuple := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
  rw [assigned_class]
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem class_pair_overlap (i j : Fin (C.splitMultiplicity p)) (hne : i ≠ j) :
    ((Finset.univ.image (classOf C hV hC p i)) ∩
      (Finset.univ.image (classOf C hV hC p j))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  apply assignedGenerator_injective C hV hC p
  have hc := hC.2.1 (slot C hV hC p i) (slot C hV hC p j)
    (fun he => hne (slot_injective C hV hC p he))
  apply Finset.card_le_one.mp hc
  · exact Finset.mem_inter.mpr ⟨assigned_mem_generators C hV hC p (Finset.mem_inter.mp hx).1,
      assigned_mem_generators C hV hC p (Finset.mem_inter.mp hx).2⟩
  · exact Finset.mem_inter.mpr ⟨assigned_mem_generators C hV hC p (Finset.mem_inter.mp hy).1,
      assigned_mem_generators C hV hC p (Finset.mem_inter.mp hy).2⟩

def pattern : EqualityPattern (C.splitMultiplicity p) (reuseCount C p) where
  classOf := classOf C hV hC p
  everyClass := class_surjective C hV hC p
  withinTuple := class_injective C hV hC p
  pairOverlap := class_pair_overlap C hV hC p

def assignment : DirectionAssignment F (C.splitMultiplicity p) (reuseCount C p) :=
  (fun i => (slot C hV hC p i).1, assignedGenerator C hV hC p)

def bits : Bits (C.splitMultiplicity p) :=
  fun i => (C.choice (slot C hV hC p i)).tuple.side

theorem assignment_eligible : Eligible (pattern C hV hC p) (assignment C hV hC p) := by
  refine ⟨slot_direction_injective C hV hC p, assignedGenerator_injective C hV hC p, ?_⟩
  intro i j
  change assignedGenerator C hV hC p (classOf C hV hC p i j) ≠ (slot C hV hC p i).1
  rw [assigned_class]
  exact (hV.2 _).2.2.2.1 j

theorem prescribedTuple_eq (i : Fin (C.splitMultiplicity p)) :
    prescribedTuple (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) i =
      (C.choice (slot C hV hC p i)).tuple := by
  apply (show ∀ s t : FourTuple F, s.generator = t.generator → s.side = t.side → s = t from by
    intro s t hg hs
    cases s
    cases t
    cases hg
    cases hs
    rfl)
  · funext j
    exact assigned_class C hV hC p i j
  · rfl

theorem prescribedPoint_eq (ij : Fin (C.splitMultiplicity p) × Fin 4) :
    prescribedPoint (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) C.merged ij =
      point C hV hC p ij := by
  unfold prescribedPoint
  rw [prescribedTuple_eq]
  rfl

theorem aligned :
    Aligned (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) p C.merged := by
  intro ij
  rw [prescribedPoint_eq]
  change OnLine (point C hV hC p ij) (lineThrough (slot C hV hC p ij.1).1 p)
  rw [← slot_line_eq C hV hC p ij.1]
  exact (hV.2 _).2.2.2.2.2.1 ij.2

theorem admissible (hb : 2 ≤ C.splitMultiplicity p)
    (hcap : ∀ x, constituentMultiplicity C.merged x ≤ logBudget F) :
    Admissible (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) p C.merged := by
  refine ⟨aligned C hV hC p, ?_, ?_, ?_, hcap⟩
  · intro ij kl h
    apply point_injective C hV hC p
    simpa only [prescribedPoint_eq] using h
  · intro ij
    rw [prescribedPoint_eq]
    exact point_ne_center C hV hC p hb ij
  · intro i
    change lineThrough (slot C hV hC p i).1 p ∉ constituentLines C.merged
    rw [← slot_line_eq C hV hC p i]
    exact (hV.2 _).2.1

theorem prescribedDesignated_eq :
    prescribedDesignated (pattern C hV hC p) (assignment C hV hC p)
      (bits C hV hC p) C.merged = C.designatedAt p := by
  have he : prescribedPoint (pattern C hV hC p) (assignment C hV hC p)
      (bits C hV hC p) C.merged = point C hV hC p :=
    funext (prescribedPoint_eq C hV hC p)
  unfold prescribedDesignated
  rw [he]
  exact point_image C hV hC p

theorem prescribedPartners_eq :
    prescribedPartners (pattern C hV hC p) (assignment C hV hC p)
      (bits C hV hC p) p C.merged = C.partnerSet p := by
  unfold prescribedPartners Configuration.partnerSet
  rw [prescribedDesignated_eq]

theorem target_line_image :
    (Finset.univ.image (fun i => lineThrough ((assignment C hV hC p).1 i) p)) =
      C.splitLinesAt p := by
  ext l
  constructor
  · intro hl
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
    change lineThrough (slot C hV hC p i).1 p ∈ C.splitLinesAt p
    rw [← slot_line_eq C hV hC p i]
    exact Finset.mem_filter.mpr ⟨ConfigurationStructure.choice_line_mem_split C _,
      slot_onLine C hV hC p i⟩
  · intro hl
    obtain ⟨hl, hp⟩ := Finset.mem_filter.mp hl
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨i, rfl⟩ := exists_slot C hV hC p hp
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (slot_line_eq C hV hC p i).symm⟩

theorem allowedPiece_iff (A : LocalPiece F) :
    AllowedPiece (assignment C hV hC p) p C.merged A ↔ C.AllowedLocalPiece p A := by
  rcases A with U | l | d
  · rfl
  · change l ∉ (Finset.univ.image (fun i => lineThrough ((assignment C hV hC p).1 i) p)) ∪
      constituentLines C.merged ↔ l ∉ C.splitLinesAt p ∪ constituentLines C.merged
    rw [target_line_image]
  · rfl

theorem badCover_iff :
    BadCover (pattern C hV hC p) (assignment C hV hC p) (bits C hV hC p) p C.merged ↔
      ∃ A : Finset (LocalPiece F), A.card ≤ C.splitMultiplicity p - 1 ∧
        (∀ a ∈ A, C.AllowedLocalPiece p a) ∧
        C.designatedAt p ⊆ C.partnerSet p ∪ A.biUnion C.localPiecePoints := by
  unfold BadCover
  rw [prescribedDesignated_eq, prescribedPartners_eq]
  simp only [allowedPiece_iff]
  rfl

theorem exists_pattern_of_not_local
    (hcap : ∀ x, constituentMultiplicity C.merged x ≤ logBudget F)
    (hbad : ¬ C.LocalCondition) :
    ∃ p : Point F, 3 ≤ C.splitMultiplicity p ∧
      ∃ (P : EqualityPattern (C.splitMultiplicity p) (reuseCount C p))
        (a : DirectionAssignment F (C.splitMultiplicity p) (reuseCount C p))
        (side : Bits (C.splitMultiplicity p)),
        Eligible P a ∧ AdmissibleBadCover P a side p C.merged := by
  unfold Configuration.LocalCondition at hbad
  push Not at hbad
  obtain ⟨p, hb, hA⟩ := hbad
  exact ⟨p, hb, pattern C hV hC p, assignment C hV hC p, bits C hV hC p,
    assignment_eligible C hV hC p,
    admissible C hV hC p (by omega) hcap, (badCover_iff C hV hC p).mpr hA⟩

end
end Balanced.Local.ConfigurationPattern

end OAI
