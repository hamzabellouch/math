import Mathlib.Data.List.ProdSigma
import OAI.Computability.UniqueGames.PCP.CloudRoundingLemmas
import OAI.Computability.UniqueGames.PCP.ExpanderRowControlLemmas
import OAI.Computability.UniqueGames.PCP.OverlayLemmas

namespace OAI

/-!
# Executable degree replacement on the actual finite constraint rows

Vertices are numbered by first listing the original darts, then the dummy
darts in original-vertex order. Each local cloud uses its explicit filtered
dart list. Internal ports carry equality; the final port retains the original
constraint, or an always-accepting loop at a dummy dart. The constructor is
total, including inputs with no darts. The fixed base expander is supplied
once; every input-dependent operation is an explicit finite calculation.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

/-- Dummy coordinates, in increasing original vertex and local index order. -/
def paddingList {n : Nat} (padding : Fin n → Nat) :
    List (Σ v : Fin n, Fin (padding v)) :=
  (List.finRange n).sigma (fun v => List.finRange (padding v))

theorem paddingList_nodup {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).Nodup :=
  (List.nodup_finRange n).sigma (fun v => List.nodup_finRange (padding v))

theorem mem_paddingList {n : Nat} (padding : Fin n → Nat)
    (z : Σ v : Fin n, Fin (padding v)) : z ∈ paddingList padding := by
  rcases z with ⟨v, k⟩
  simp only [paddingList, List.mem_sigma, List.mem_finRange, and_self]

def paddingListOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (paddingList padding).length :=
  PreprocessingCloudIndex.listEquiv (paddingList padding)
    (paddingList_nodup padding) (mem_paddingList padding)

theorem paddingList_length {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).length = ∑ v, padding v := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    (Fintype.card_congr (paddingListOrder padding)).symm

/-- Explicit list search/get indexing, with an erased cardinality cast. -/
def paddingOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (∑ v, padding v) :=
  (paddingListOrder padding).trans (finCongr (paddingList_length padding))

abbrev Vertex (t : GraphTables.Table) (padding : Fin t.vertices → Nat) :=
  PaddedDart (GraphTables.semantics t) (fun v => Fin (padding v))

def vertexCount (t : GraphTables.Table) (padding : Fin t.vertices → Nat) : Nat :=
  t.darts + ∑ v, padding v

/-- The original darts precede all the newly added dummy darts. -/
def vertexOrder (t : GraphTables.Table) (padding : Fin t.vertices → Nat) :
    Vertex t padding ≃ Fin (vertexCount t padding) :=
  (Equiv.sumCongr (Equiv.refl _) (paddingOrder padding)).trans finSumFinEquiv

@[simp] theorem vertexOrder_original (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (e : Fin t.darts) :
    (vertexOrder t padding (Sum.inl e)).val = e.val := rfl

@[simp] theorem vertexOrder_dummy (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (z : Σ v, Fin (padding v)) :
    (vertexOrder t padding (Sum.inr z)).val =
      t.darts + (paddingOrder padding z).val := rfl

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := ⟨0, Nat.zero_lt_one⟩
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv k := Subsingleton.elim _ _

/-- Internal cloud ports precede the one inherited-constraint port. -/
def portOrder (q : Nat) : (Fin q ⊕ Unit) ≃ Fin (q + 1) :=
  (Equiv.sumCongr (Equiv.refl _) unitOrder).trans finSumFinEquiv

@[simp] theorem portOrder_internal (q : Nat) (p : Fin q) :
    (portOrder q (Sum.inl p)).val = p.val := rfl

@[simp] theorem portOrder_inherited (q : Nat) :
    (portOrder q (Sum.inr ())).val = q := rfl

/-- A supplied finite cloud rotation is transported by the explicit cloud list. -/
def cloudGraphs (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) (v : Fin t.vertices) :
    PortGraph (Cloud (paddedGraph (GraphTables.semantics t)
      (fun w => Fin (padding w))) v) (Fin q) :=
  GraphTransport.reindex (ExpanderTables.graph (tables v))
    (PreprocessingCloudIndex.paddedCloudEquiv t padding v).symm (Equiv.refl _)

def sourcePortGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortGraph (Vertex t padding) (Fin q ⊕ Unit) :=
  paddedReplacementPortGraph (GraphTables.semantics t) (fun v => Fin (padding v))
    (cloudGraphs t padding tables)

def sourceGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    ConstraintGraph (Vertex t padding) (Vertex t padding × (Fin q ⊕ Unit))
      GraphTables.Label :=
  paddedReplacementGraph (GraphTables.semantics t) (fun v => Fin (padding v))
    (cloudGraphs t padding tables)

def numberedPortGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortGraph (Fin (vertexCount t padding)) (Fin (q + 1)) :=
  GraphTransport.reindex (sourcePortGraph t padding tables)
    (vertexOrder t padding) (portOrder q)

def numberedAccepts (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin (vertexCount t padding) × Fin (q + 1))
    (a b : GraphTables.Label) : Bool :=
  (sourceGraph t padding tables).accepts
    ((vertexOrder t padding).symm e.1, (portOrder q).symm e.2) a b

theorem numberedAccepts_transpose (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin (vertexCount t padding) × Fin (q + 1)) (a b : GraphTables.Label) :
    numberedAccepts t padding tables ((numberedPortGraph t padding tables).rot e) b a =
      numberedAccepts t padding tables e a b := by
  obtain ⟨z, rfl⟩ := (Equiv.prodCongr (vertexOrder t padding) (portOrder q)).surjective e
  rcases z with ⟨v, p⟩
  simp only [numberedPortGraph, Equiv.prodCongr_apply, Prod.map_apply,
    GraphTransport.reindex_rot, numberedAccepts, Equiv.symm_apply_apply]
  exact (sourceGraph t padding tables).reverse_accepts (v, p) a b

/-- Materialize every reverse index and every 4096-bit constraint row. -/
def ofCloudTables (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortTables.Table (vertexCount t padding) (q + 1) :=
  PortTables.ofPortGraph (numberedPortGraph t padding tables)
    (numberedAccepts t padding tables) (numberedAccepts_transpose t padding tables)

@[simp] theorem rotation_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    PortTables.rotation (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q p) =
      (vertexOrder t padding ((sourcePortGraph t padding tables).rot (v, p)).1,
        portOrder q ((sourcePortGraph t padding tables).rot (v, p)).2) := by
  rw [ofCloudTables, PortTables.rotation_ofPortGraph]
  exact GraphTransport.reindex_rot _ _ _ _ _

@[simp] theorem accepts_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q p) a b =
      (sourceGraph t padding tables).accepts (v, p) a b := by
  simp only [ofCloudTables, PortTables.accepts_ofPortGraph,
    numberedAccepts, Equiv.symm_apply_apply]

@[simp] theorem accepts_internal (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q (Sum.inl p)) a b = decide (a = b) := by
  rw [accepts_ofCloudTables]
  rfl

@[simp] theorem accepts_original (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin t.darts) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding (Sum.inl e), portOrder q (Sum.inr ())) a b =
      GraphTables.acceptsAt t.rows e a b := by
  rw [accepts_ofCloudTables]
  rfl

@[simp] theorem accepts_dummy (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (z : Σ v, Fin (padding v)) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding (Sum.inr z), portOrder q (Sum.inr ())) a b = true := by
  rw [accepts_ofCloudTables]
  rfl

theorem edgeSatisfied_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).edgeSatisfied labels
        (vertexOrder t padding v, portOrder q p) =
      (sourceGraph t padding tables).edgeSatisfied
        (fun z => labels (vertexOrder t padding z)) (v, p) := by
  change PortTables.accepts (ofCloudTables t padding tables)
    (vertexOrder t padding v, portOrder q p) (labels (vertexOrder t padding v))
    (labels (PortTables.rotation (ofCloudTables t padding tables)
      (vertexOrder t padding v, portOrder q p)).1) = _
  rw [rotation_ofCloudTables, accepts_ofCloudTables]
  rfl

/-- Numbering preserves the rejection count for every labeling. -/
theorem rejectionCount_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).rejectionCount labels =
      (sourceGraph t padding tables).rejectionCount
        (fun z => labels (vertexOrder t padding z)) := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv (Equiv.prodCongr (vertexOrder t padding) (portOrder q))
  rintro ⟨v, p⟩
  simp only [ConstraintGraph.mem_rejectedDarts, Equiv.prodCongr_apply,
    Prod.map_apply, edgeSatisfied_ofCloudTables]

def liftedLabel (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (labels : Fin t.vertices → GraphTables.Label) :
    Fin (vertexCount t padding) → GraphTables.Label :=
  fun z => labels (paddedOwner (GraphTables.semantics t) (fun v => Fin (padding v))
    ((vertexOrder t padding).symm z))

theorem rejectionCount_liftedLabel (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin t.vertices → GraphTables.Label) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).rejectionCount
        (liftedLabel t padding labels) = (GraphTables.semantics t).rejectionCount labels := by
  rw [rejectionCount_ofCloudTables]
  simp only [liftedLabel, Equiv.symm_apply_apply]
  convert paddedReplacement_rejectionCount (GraphTables.semantics t)
    (fun v => Fin (padding v)) (cloudGraphs t padding tables) labels using 1
  rfl

/-- An empty cloud has a total, vacuous rotation table. -/
def emptyTable (q : Nat) : ExpanderTables.Table 0 q :=
  ExpanderTables.ofGraph { rot := Equiv.refl _, rot_involutive := fun _ => rfl }

/-- Change only a proof-equal size index, without selecting any new numbering. -/
def resizeTable {n m q : Nat} (h : n = m) (table : ExpanderTables.Table n q) :
    ExpanderTables.Table m q := h ▸ table

abbrev BaseTable := ExpanderTables.Table
  ((Expanders.baseDegree * Expanders.baseDegree) *
    (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree

def internalDegree : Nat := Expanders.baseDegree * Expanders.baseDegree

def padding (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) -
    PreprocessingCloudIndex.cloudSize t v

theorem cloudSize_add_padding (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingCloudIndex.cloudSize t v + padding t v =
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) :=
  Nat.add_sub_of_le (PreprocessingLevels.cloudPaddedSize_bounds _).1

theorem vertexCount_eq_sum_cloudPaddedSize (t : GraphTables.Table) :
    vertexCount t (padding t) = ∑ v,
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) := by
  unfold vertexCount
  rw [← PreprocessingCloudIndex.sum_cloudSize t, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => cloudSize_add_padding t v)

theorem vertexCount_le (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * t.darts := by
  rw [vertexCount_eq_sum_cloudPaddedSize, ← PreprocessingCloudIndex.sum_cloudSize t,
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _ => (PreprocessingLevels.cloudPaddedSize_bounds _).2)

theorem vertexCount_eq_zero_of_no_darts (t : GraphTables.Table) (h : t.darts = 0) :
    vertexCount t (padding t) = 0 := by
  have hle := vertexCount_le t
  rw [h, Nat.mul_zero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Select the family level by the bounded multiplication search. -/
def familyCloudTable (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) :
    ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding t v)
      internalDegree :=
  if hk : PreprocessingCloudIndex.cloudSize t v = 0 then
    resizeTable (by rw [cloudSize_add_padding, hk]; rfl) (emptyTable internalDegree)
  else
    resizeTable (by
      rw [cloudSize_add_padding,
        PreprocessingLevels.cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
      exact PreprocessingLevels.table_vertexCount_eq_paddedSize _)
      (ExpanderTables.family H
        (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))

/-- The actual regularized output rows; no runtime proof or positivity input. -/
def regularize (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertexCount t (padding t)) (internalDegree + 1) :=
  ofCloudTables t (padding t) (familyCloudTable H t)

def regularizeInput (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Input (internalDegree + 1) :=
  ⟨vertexCount t (padding t), regularize H t⟩

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables

/-!
# Exact serialized family tables at actual regularization vertices

The geometric family maps request zero to a one-vertex table. Empty clouds in
regularization instead remain empty. The bridge therefore requires positive
cloud size, derived here from each actual original or dummy vertex.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingFamilyBridge

open PreprocessingCloudIndex PreprocessingRegularTables ExpanderTableWords
open UniqueGamesTheorem.Foundations.Complexity (encodeWords)

/-- Transporting only the size equality leaves every serialized rotor entry
unchanged; no relabeling or alternative numbering is introduced. -/
theorem rotationWords_resizeTable {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) :
    rotationWords (resizeTable h table) = rotationWords table := by
  cases h
  rfl

/-- This left side is definitionally the output `MachineRegularFamily.rotor`
for the request on its physical core tape 4. The right side is exactly the
archive expected on core tape 7 by the internal-row machine. -/
theorem familyRotor_eq_familyCloudTable (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (hk : 0 < cloudSize t v) :
    encodeWords (rotationWords (ExpanderTables.family H
      (PreprocessingLevels.boundedLevel (cloudSize t v)))) =
      encodeWords (rotationWords (familyCloudTable H t v)) := by
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  erw [rotationWords_resizeTable]
  rfl

/-- An actual original dart supplies a member of its owner's cloud. -/
theorem cloudSize_pos_of_dart (t : GraphTables.Table) (e : Fin t.darts) :
    0 < cloudSize t t.rows[e].tail := by
  have h := (oldCloudIndex t e).isLt
  omega

/-- An empty cloud has no padding vertices either. -/
theorem padding_zero_of_cloudSize_zero (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : cloudSize t v = 0) : padding t v = 0 := by
  simp only [padding, hk, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero]

/-- Every actual dummy vertex also belongs to a positive original cloud. -/
theorem cloudSize_pos_of_dummy (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hj := j.isLt
  omega

/-- The same positivity fact for the common local coordinate interface. -/
theorem cloudSize_pos_of_paddedCloud (t : GraphTables.Table) (v : Fin t.vertices)
    (x : PaddedCloud t (padding t) v) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hx := (paddedCloudRank t (padding t) v x).isLt
  omega

/-- The zero-cloud branch remains genuinely empty, including its serialized
rotor archive. It is not replaced by the geometric family at request zero. -/
theorem familyCloudWords_of_zero (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (hk : cloudSize t v = 0) :
    encodeWords (rotationWords (familyCloudTable H t v)) = [] := by
  have hl : (rotationWords (familyCloudTable H t v)).length = 0 := by
    rw [rotationWords_length, cloudSize_add_padding, hk,
      PreprocessingLevels.cloudPaddedSize_zero, Nat.zero_mul]
  rw [List.length_eq_zero_iff.mp hl]
  rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingFamilyBridge

end OAI
