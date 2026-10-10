import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredArrays
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationArrayInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredRestriction
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredParentExecution

namespace OAI

/-! # Preparing one shared-array reader context

Generation and sorting execute once. Row initialization captures the returned
right array, and the context retains that same immutable array with its
measured tournament state. Proof transports do not regenerate either array.
-/

namespace LowSpaceSubsetSum.PreparedReaderContext

variable {n : ℕ}

structure Context (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode) where
  right : Array (LeafRecord n)
  depth : ℕ
  state : CountedParentJoin.State I F P mode right depth

private theorem context_ext {I : Instance n} {F : IndexedMask n} {P : ℤ}
    {mode : FilteredStream.Mode} {a b : Context I F P mode}
    (hr : a.right = b.right) (hd : a.depth = b.depth) (hs : HEq a.state b.state) : a = b := by
  cases a
  cases b
  cases hr
  cases hd
  cases hs
  rfl

private theorem rekey_tree {α σ : Type*} {key key' : α → ℤ} {view : σ → List α}
    {d : ℕ} (h : key = key') (s : MergedReader.State key view d) :
    (MergedReader.rekey h s).tree = s.tree := by
  cases h
  rfl

private theorem key_eq (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) :
    FilteredStream.key (fun x => (RepresentationKeys.leafWeight I F x).1)
      (fun x => (RepresentationKeys.leafWeight I F x).1) P mode =
      (fun x => (RepresentationKeys.pairKey I F P mode x).1) := by
  funext x
  cases mode <;> rfl

/-- The initializer takes array values, so every row closure shares `right`. -/
def fromArrays (I : Instance n) (F : IndexedMask n) (left right : Array (LeafRecord n))
    (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) : Context I F P mode × ℕ :=
  let out := RepresentationArrayInitialization.start I F left right p P c hs ht hP mode
  (⟨right, Nat.clog 2 left.size, MergedReader.rekey (key_eq I F P mode) out.1⟩, out.2)

private theorem fromArrays_tree (I : Instance n) (F : IndexedMask n)
    (left right : Array (LeafRecord n)) (p P c : ℤ)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight I F x).1) p P)
    (hP : 0 < P) (mode : FilteredStream.Mode) :
    (fromArrays I F left right p P c hs ht hP mode).1.state.tree =
      (FilteredStream.start left right (fun x => (RepresentationKeys.leafWeight I F x).1)
        (fun x => (RepresentationKeys.leafWeight I F x).1) p P c hs ht hP mode).tree := by
  simp only [fromArrays, rekey_tree, RepresentationArrayInitialization.start_value]

private theorem dep_heq {β : ℕ → Sort*} (f : ∀ d, β d) {d e : ℕ} (h : d = e) :
    HEq (f d) (f e) := by
  cases h
  rfl

private theorem state_heq {α σ : Type*} {key : α → ℤ} {view : σ → List α} {d e : ℕ}
    (s : MergedReader.State key view d) (t : MergedReader.State key view e)
    (hd : d = e) (ht : HEq s.tree t.tree) : HEq s t := by
  cases hd
  have he := eq_of_heq ht
  cases s
  cases t
  cases he
  rfl

def source (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    Context D.input F D.modulus (D.pair j).mode :=
  ⟨(D.pair j).rightRecords, Nat.clog 2 (D.pair j).leftArray.size,
    StoredParentExecution.start D F hF j⟩

private theorem record_key_eq (D : RepresentationPairData n) :
    FilteredStream.key (fun x : LeafRecord n => D.wl x.semantic)
      (fun x : LeafRecord n => D.wl x.semantic) D.modulus D.mode =
      RepresentationStoredReader.key D := by
  funext x
  dsimp only [RepresentationStoredReader.key, RepresentationStoredReader.sourceKey,
    RepresentationKeys.pairSemantic]
  cases D.mode <;> rfl

private theorem fromArrays_source (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (left right : Array (LeafRecord n))
    (hl : left = (D.pair j).leftRecords) (hr : right = (D.pair j).rightRecords)
    (hs : FilteredRow.PrimarySorted right (fun x => (RepresentationKeys.leafWeight D.input F x).1)
      D.lowModulus)
    (ht : FilteredRow.SecondarySorted right (fun x => (RepresentationKeys.leafWeight D.input F x).1)
      D.lowModulus D.modulus) :
    (fromArrays D.input F left right D.lowModulus D.modulus (D.pair j).residue
      hs ht D.positive (D.pair j).mode).1 = source D F hF j := by
  subst left
  subst right
  have hd := congrArg (Nat.clog 2) (D.pair j).leftRecords_size
  refine context_ext
    (a := (fromArrays D.input F (D.pair j).leftRecords (D.pair j).rightRecords
      D.lowModulus D.modulus (D.pair j).residue hs ht D.positive (D.pair j).mode).1)
    (b := source D F hF j) rfl hd ?_
  apply state_heq _ _ hd
  rw [fromArrays_tree]
  dsimp only [source, StoredParentExecution.start]
  rw [rekey_tree]
  simp only [FilteredStream.start, MergedReader.start, RepresentationStoredReader.start,
    RepresentationStoredReader.rows, RepresentationKeys.parent_leafWeight_value D F hF j]
  let family := fun d => RowMerge.start (RepresentationStoredReader.key (D.pair j))
    (FilteredStream.read (D.pair j).rightRecords)
    (PaddedRows.rows (FilteredStream.rowArray (D.pair j).leftRecords (D.pair j).rightRecords
      (fun x => (D.pair j).wl x.semantic) (fun x => (D.pair j).wl x.semantic)
      D.lowModulus D.modulus (D.pair j).residue
      (by simpa only [RepresentationPairData.rightRecords, RepresentationParentData.pair] using
        (ResidueSort.primary (D.pair j).rawRightRecords (fun x => (D.pair j).wl x.semantic)
          D.lowModulus D.modulus)) (D.pair j).mode) d)
  have hk : FilteredStream.key (fun x : LeafRecord n => (D.pair j).wl x.semantic)
      (fun x : LeafRecord n => (D.pair j).wl x.semantic) D.modulus (D.pair j).mode =
      RepresentationStoredReader.key (D.pair j) := record_key_eq (D.pair j)
  rw [hk]
  change HEq (family (Nat.clog 2 (D.pair j).leftRecords.size))
    (family (Nat.clog 2 (D.pair j).leftArray.size))
  exact dep_heq family hd

private theorem parent_primary (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    FilteredRow.PrimarySorted (D.pair j).rightRecords
      (fun x => (RepresentationKeys.leafWeight D.input F x).1) D.lowModulus := by
  have hw : (fun x : LeafRecord n => (RepresentationKeys.leafWeight D.input F x).1) =
      (fun x => (D.pair j).wl x.semantic) :=
    funext (RepresentationKeys.parent_leafWeight_value D F hF j)
  rw [hw]
  change FilteredRow.PrimarySorted
    (ResidueSort.sort (D.pair j).rawRightRecords (fun x => (D.pair j).wl x.semantic)
      D.lowModulus D.modulus) _ _
  exact ResidueSort.primary _ _ _ _

private theorem parent_secondary (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    FilteredRow.SecondarySorted (D.pair j).rightRecords
      (fun x => (RepresentationKeys.leafWeight D.input F x).1) D.lowModulus D.modulus := by
  have hw : (fun x : LeafRecord n => (RepresentationKeys.leafWeight D.input F x).1) =
      (fun x => (D.pair j).wl x.semantic) :=
    funext (RepresentationKeys.parent_leafWeight_value D F hF j)
  rw [hw]
  change FilteredRow.SecondarySorted
    (ResidueSort.sort (D.pair j).rawRightRecords (fun x => (D.pair j).wl x.semantic)
      D.lowModulus D.modulus) _ _ _
  exact ResidueSort.secondary _ _ _ _

private theorem prepared_primary (D : RepresentationParentData n) (F : IndexedMask n)
    (P : StoredRestriction n) (hF : F.semantic = D.signs) (j : Fin 2) :
    FilteredRow.PrimarySorted
      (RepresentationStoredArrays.prepare {D with maskRestriction := P.semantic} F P.ones P.zeros j).1.2
      (fun x => (RepresentationKeys.leafWeight D.input F x).1) D.lowModulus := by
  rw [RepresentationStoredArrays.prepare_value {D with maskRestriction := P.semantic}
    F P.ones P.zeros hF rfl rfl j]
  exact parent_primary {D with maskRestriction := P.semantic} F hF j

private theorem prepared_secondary (D : RepresentationParentData n) (F : IndexedMask n)
    (P : StoredRestriction n) (hF : F.semantic = D.signs) (j : Fin 2) :
    FilteredRow.SecondarySorted
      (RepresentationStoredArrays.prepare {D with maskRestriction := P.semantic} F P.ones P.zeros j).1.2
      (fun x => (RepresentationKeys.leafWeight D.input F x).1) D.lowModulus D.modulus := by
  rw [RepresentationStoredArrays.prepare_value {D with maskRestriction := P.semantic}
    F P.ones P.zeros hF rfl rfl j]
  exact parent_secondary {D with maskRestriction := P.semantic} F hF j

/-- One complete preparation and initialization; `a` is evaluated once. -/
def build (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (j : Fin 2) : Context D.input F D.modulus (D.pair j).mode × ℕ :=
  let a := RepresentationStoredArrays.prepare {D with maskRestriction := P.semantic} F P.ones P.zeros j
  let out := fromArrays D.input F a.1.1 a.1.2 D.lowModulus D.modulus (D.pair j).residue
    (prepared_primary D F P hF j) (prepared_secondary D F P hF j) D.positive (D.pair j).mode
  (out.1, a.2 + out.2)

theorem build_value (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    (build D F P hF j).1 = source {D with maskRestriction := P.semantic} F hF j := by
  have ha := RepresentationStoredArrays.prepare_value
    {D with maskRestriction := P.semantic} F P.ones P.zeros hF rfl rfl j
  exact fromArrays_source {D with maskRestriction := P.semantic} F hF j _ _
    (congrArg Prod.fst ha) (congrArg Prod.snd ha) _ _

theorem build_work (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (j : Fin 2) (C : ℕ) (hn : 10000 ≤ n)
    (hl : (D.pair j).left.occurrences.card ≤ C)
    (hr : (D.pair j).right.occurrences.card ≤ C) (hC : C ≤ 2 ^ n) :
    (build D F P hF j).2 ≤ inputScale D.input ^ 9 * (C + 1) := by
  let a := RepresentationStoredArrays.prepare {D with maskRestriction := P.semantic} F P.ones P.zeros j
  have ha := RepresentationStoredArrays.prepare_work
    {D with maskRestriction := P.semantic} F P.ones P.zeros j C hn hl hr hC
  have hsize := RepresentationStoredArrays.prepare_sizes
    {D with maskRestriction := P.semantic} F P.ones P.zeros j
  have hi := RepresentationArrayInitialization.start_work D.input F a.1.1 a.1.2
    D.lowModulus D.modulus (D.pair j).residue
    (prepared_primary D F P hF j) (prepared_secondary D F P hF j) D.positive (D.pair j).mode
    hn ((hsize.1.trans hl).trans hC) ((hsize.2.trans hr).trans hC)
  have hi' := hi.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hsize.1.trans hl) 1))
  have hu : 10000 ≤ inputScale D.input := by unfold inputScale; omega
  have h68 : inputScale D.input ^ 6 ≤ inputScale D.input ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h89 : 2 * inputScale D.input ^ 8 ≤ inputScale D.input ^ 9 := by
    calc
      _ ≤ inputScale D.input * inputScale D.input ^ 8 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hlow := Nat.mul_le_mul_right (C + 1) h68
  have htotal := Nat.mul_le_mul_right (C + 1) h89
  change a.2 + (RepresentationArrayInitialization.start D.input F a.1.1 a.1.2
    D.lowModulus D.modulus (D.pair j).residue
    (prepared_primary D F P hF j) (prepared_secondary D F P hF j)
    D.positive (D.pair j).mode).2 ≤ _
  change a.2 ≤ inputScale D.input ^ 6 * (C + 1) at ha
  simp only [Nat.mul_assoc] at htotal
  omega

end LowSpaceSubsetSum.PreparedReaderContext

end OAI
