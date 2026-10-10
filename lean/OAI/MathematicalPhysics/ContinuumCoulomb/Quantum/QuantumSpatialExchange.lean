import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourSpatial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockRational
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumChosenSlots

namespace OAI

/-! The actual rational four-spin simulator retains bounded spatial density. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaXZFieldData_mem {n : ℕ} (t : QMAXZTerm n) (h : t.IsField) :
    (t.asField h).site ∈ qmaPauliSupport t.word := by
  cases t with
  | scalar => exact h.elim
  | field i a =>
    change i ∈ qmaPauliSupport (QMAXZTerm.field i a).word
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simpa only [QMAXZTerm.word,ite_true] using qmaXZLabel_ne_zero a
  | pair => exact h.elim

structure QMASpatialExchangeModel (A B : ℕ) where
  n : ℕ
  Term : Type
  [termFinite : Fintype Term]
  left : Term → Fin n
  right : Term → Fin n
  distinct : ∀ e, left e ≠ right e
  weight : Term → ℚ
  constant : ℚ
  rows : ℕ
  width : ℕ
  cell : Fin n → QMAGridCell rows width
  anchor : Term → QMAGridCell rows width
  geometry : ∀ e, QMAGridCellsNear (cell (left e)) (anchor e) ∧
    QMAGridCellsNear (cell (right e)) (anchor e)
  qubitDensity : ∀ p, (Finset.univ.filter (fun i => cell i = p)).card ≤ A
  termDensity : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B
  qubitSlots : QMACellSlots cell A := QMACellSlots.ofDensity qubitDensity
  termSlots : QMACellSlots anchor B := QMACellSlots.ofDensity termDensity

attribute [instance] QMASpatialExchangeModel.termFinite

def QMASpatialExchangeModel.energy {A B : ℕ} (M : QMASpatialExchangeModel A B) : ℝ :=
  MediatorGraph.normalizedBottom (qmaExchangeMatrix M.left M.right (fun e => (M.weight e:ℝ)) M.constant)

theorem qmaSubtype_filter_card_le {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (f : α → Prop) [DecidablePred f] :
    (Finset.univ.filter (fun a : {a // P a} => f a.val)).card ≤ (Finset.univ.filter f).card := by
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ h
    exact Subtype.ext h

theorem qmaSpatialXZTerms_exchange {κ : Type} [Fintype κ] {n rows width A B : ℕ}
    (t : κ → QMAXZTerm n) (J : κ → ℝ)
    (cell : Fin n → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    (hlocal : ∀ e, ∀ q ∈ qmaPauliSupport (t e).word, QMAGridCellsNear (cell q) (anchor e))
    (hq : ∀ p, (Finset.univ.filter (fun i => cell i = p)).card ≤ A)
    (ht : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f)
    (N : ℕ) (hN : 0 < N) :
    ∃ G : QMASpatialExchangeModel (4*A) (6*A+25*B),
      G.rows = rows ∧ G.width = width ∧
      |G.energy-MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 2/(N:ℝ) := by
  let left := fun e => (qmaXZPairData t e).left
  let right := fun e => (qmaXZPairData t e).right
  let a := fun e => (qmaXZPairData t e).axisLeft
  let b := fun e => (qmaXZPairData t e).axisRight
  let site := fun e => (qmaXZFieldData t e).site
  let axis := fun e => (qmaXZFieldData t e).axis
  let pa := fun e : QMAXZPairIndex t => anchor e.val
  let fa := fun e : QMAXZFieldIndex t => anchor e.val
  let r := 9*(qmaXZBlockBudget t J)^3*N
  let m := (3*Fintype.card (QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t))+1)*N
  have hp (p : QMAGridCell rows width) :
      (Finset.univ.filter (fun e : QMAXZPairIndex t => pa e = p)).card ≤ B :=
    (qmaSubtype_filter_card_le (fun e => (t e).IsPair) (fun e => anchor e = p)).trans (ht p)
  have hf (p : QMAGridCell rows width) :
      (Finset.univ.filter (fun e : QMAXZFieldIndex t => fa e = p)).card ≤ B :=
    (qmaSubtype_filter_card_le (fun e => (t e).IsField) (fun e => anchor e = p)).trans (ht p)
  have hleft (e : QMAXZPairIndex t) : QMAGridCellsNear (cell (left e)) (pa e) := by
    apply hlocal e.val
    rw [(t e.val).pair_support e.property]
    exact Finset.mem_insert_self _ _
  have hright (e : QMAXZPairIndex t) : QMAGridCellsNear (cell (right e)) (pa e) := by
    apply hlocal e.val
    rw [(t e.val).pair_support e.property]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hsite (e : QMAXZFieldIndex t) : QMAGridCellsNear (cell (site e)) (fa e) :=
    hlocal e.val _ (qmaXZFieldData_mem (t e.val) e.property)
  let G : QMASpatialExchangeModel (4*A) (6*A+25*B) := {
    n := n*4
    Term := QMAFourExchangeIndex n (QMAXZPairIndex t) (QMAXZFieldIndex t)
    left := qmaFourExchangeLeft left right site
    right := qmaFourExchangeRight left right site
    distinct := qmaFourExchange_distinct left right site (fun e => (qmaXZPairData t e).distinct)
    weight := fun x => qmaRationalRound m (qmaFourExchangeWeight r a b (fun e => J e.val) axis (fun e => J e.val) x)
    constant := qmaRationalRound m (qmaFourExchangeScalar n r axis (fun e => J e.val) (qmaXZFamilyConstant t J))
    rows := rows
    width := width
    cell := qmaFourBlockCell cell
    anchor := qmaFourExchangeAnchor cell pa fa
    geometry := qmaFourExchange_spatial cell pa fa left right site hleft hright hsite
    qubitDensity := qmaFourBlockCell_density cell hq
    termDensity := by
      intro p
      exact (qmaFourExchangeAnchor_density cell pa fa hq hp hf p).trans (by omega) }
  refine ⟨G,rfl,rfl,?_⟩
  have h := qmaBlock_rational_accuracy left right a b (fun e => J e.val)
    (fun e => (qmaXZPairData t e).distinct)
    (fun e f hef => qmaXZPairData_distinct t hprivate e f hef)
    site axis (fun e => J e.val) (qmaXZFamilyConstant t J) N hN
  change |G.energy-MediatorGraph.normalizedBottom (qmaFourTensorFullTarget left right a b
    (fun e => J e.val) site axis (fun e => J e.val) (qmaXZFamilyConstant t J))| ≤ _ at h
  rw [qmaXZFamily_target] at h
  exact h

end ContinuumCoulomb

end

end OAI
