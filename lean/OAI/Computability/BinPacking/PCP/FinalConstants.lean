import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.BinPacking.Computation.MachineRegularDummyRow
import OAI.Computability.BinPacking.Expanders.PreprocessingTableSpectral

namespace OAI

namespace BinPackingGames.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

def reverseFunction (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (V ⊕ Fin extra) × D → (V ⊕ Fin extra) × D
  | (Sum.inl v, d) => (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2)
  | (Sum.inr w, d) => (Sum.inr w, d)

theorem reverseFunction_involutive (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    Function.Involutive (reverseFunction G extra) := by
  rintro ⟨v | w, d⟩
  · change (Sum.inl (G.reverse (G.reverse (v, d))).1,
      (G.reverse (G.reverse (v, d))).2) = (Sum.inl v, d)
    rw [G.reverse_involutive]
  · rfl

def pad (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    ConstraintGraph (V ⊕ Fin extra) ((V ⊕ Fin extra) × D) A where
  reverse := {
    toFun := reverseFunction G extra
    invFun := reverseFunction G extra
    left_inv := reverseFunction_involutive G extra
    right_inv := reverseFunction_involutive G extra }
  reverse_involutive := reverseFunction_involutive G extra
  tail := Prod.fst
  accepts := fun e a b => match e.1 with
    | Sum.inl v => G.accepts (v, e.2) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v | w, d⟩ a b
    · change G.accepts (G.reverse (v, d)) b a = G.accepts (v, d) a b
      exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem pad_tail (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (pad G extra).tail = Prod.fst := rfl

@[simp] theorem pad_reverse_inl (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (v : V) (d : D) :
    (pad G extra).reverse (Sum.inl v, d) =
      (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2) := rfl

@[simp] theorem pad_reverse_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (w : Fin extra) (d : D) :
    (pad G extra).reverse (Sum.inr w, d) = (Sum.inr w, d) := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (extra : ℕ) (labeling : V ⊕ Fin extra → A)
    (v : V) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inl v, d) =
      G.edgeSatisfied (fun v => labeling (Sum.inl v)) (v, d) := by
  change G.accepts (v, d) (labeling (Sum.inl v))
      (labeling (Sum.inl (G.reverse (v, d)).1)) =
    G.accepts (v, d) (labeling (Sum.inl (G.tail (v, d))))
      (labeling (Sum.inl (G.tail (G.reverse (v, d)))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) (w : Fin extra) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inr w, d) = true := rfl

def extendLabeling (extra : ℕ) (defaultA : A) (labeling : V → A) : V ⊕ Fin extra → A :=
  Sum.elim labeling (fun _ => defaultA)

@[simp] theorem extendLabeling_inl (extra : ℕ) (defaultA : A) (labeling : V → A)
    (v : V) : extendLabeling extra defaultA labeling (Sum.inl v) = labeling v := rfl

@[simp] theorem extendLabeling_inr (extra : ℕ) (defaultA : A) (labeling : V → A)
    (w : Fin extra) : extendLabeling extra defaultA labeling (Sum.inr w) = defaultA := rfl

theorem pad_satisfiable (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (extra : ℕ) (defaultA : A) (hG : G.Satisfiable) : (pad G extra).Satisfiable := by
  obtain ⟨labeling, hlabeling⟩ := hG
  refine ⟨extendLabeling extra defaultA labeling, ?_⟩
  rintro ⟨v | w, d⟩
  · simpa only [edgeSatisfied_inl G htail, extendLabeling_inl] using hlabeling (v, d)
  · rfl

theorem satisfiable_of_pad (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (extra : ℕ) (hG : (pad G extra).Satisfiable) : G.Satisfiable := by
  obtain ⟨labeling, hlabeling⟩ := hG
  refine ⟨fun v => labeling (Sum.inl v), ?_⟩
  rintro ⟨v, d⟩
  simpa only [edgeSatisfied_inl G htail] using hlabeling (Sum.inl v, d)

private theorem rejectionCount_eq_sum {U E : Type*} [Fintype E]
    (G : ConstraintGraph U E A) (labeling : U → A) :
    G.rejectionCount labeling = ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]

theorem pad_rejectionCount [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) :
    (pad G extra).rejectionCount labeling =
      G.rejectionCount (fun v => labeling (Sum.inl v)) := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [edgeSatisfied_inl G htail, edgeSatisfied_inr]
  simp

variable (V : Type*) [Fintype V]

def extraVertices : ℕ := ExpanderFamily.size (Fintype.card V) - Fintype.card V

abbrev Vertex := V ⊕ Fin (extraVertices V)

theorem card_vertex : Fintype.card (Vertex V) = ExpanderFamily.size (Fintype.card V) := by
  rw [Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_sub_of_le (ExpanderFamily.le_size _)

theorem le_card_vertex : Fintype.card V ≤ Fintype.card (Vertex V) := by
  rw [card_vertex]
  exact ExpanderFamily.le_size _

theorem card_vertex_le [Nonempty V] :
    Fintype.card (Vertex V) ≤ ExpanderFamily.growth * Fintype.card V := by
  rw [card_vertex]
  exact ExpanderFamily.size_le_mul Fintype.card_pos

noncomputable def familyVertexEquiv :
    Vertex V ≃ ExpanderFamily.Vertex (ExpanderFamily.level (Fintype.card V)) :=
  Fintype.equivOfCardEq (by
    rw [card_vertex, ExpanderFamily.card_vertex]
    rfl)

variable {V}

def paddedG (G : ConstraintGraph V (V × D) A) : ConstraintGraph (Vertex V) (Vertex V × D) A :=
  pad G (extraVertices V)

@[simp] theorem paddedG_tail (G : ConstraintGraph V (V × D) A) :
    (paddedG G).tail = Prod.fst := rfl

theorem paddedG_rejectionCount [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : Vertex V → A) :
    (paddedG G).rejectionCount labeling =
      G.rejectionCount (fun v => labeling (Sum.inl v)) :=
  pad_rejectionCount G htail (extraVertices V) labeling

theorem rejectionCount_eq [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : Vertex V → A) :
    (paddedG G).rejectionCount labeling =
      G.rejectionCount (fun v => labeling (Sum.inl v)) :=
  paddedG_rejectionCount G htail labeling

def liftLabel (defaultA : A) (labeling : V → A) : Vertex V → A :=
  extendLabeling (extraVertices V) defaultA labeling

@[simp] theorem liftLabel_inl (defaultA : A) (labeling : V → A) (v : V) :
    liftLabel defaultA labeling (Sum.inl v) = labeling v := rfl

@[simp] theorem liftLabel_inr (defaultA : A) (labeling : V → A)
    (w : Fin (extraVertices V)) :
    liftLabel defaultA labeling (Sum.inr w) = defaultA := rfl

theorem rejectionCount_liftLabel [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (defaultA : A) (labeling : V → A) :
    (paddedG G).rejectionCount (liftLabel defaultA labeling) = G.rejectionCount labeling := by
  simpa only [liftLabel_inl] using
    paddedG_rejectionCount G htail (liftLabel defaultA labeling)

theorem paddedG_satisfiable (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (defaultA : A) (hG : G.Satisfiable) : (paddedG G).Satisfiable :=
  pad_satisfiable G htail (extraVertices V) defaultA hG

theorem card_padded_darts [Fintype D] :
    Fintype.card (Vertex V × D) = ExpanderFamily.size (Fintype.card V) * Fintype.card D := by
  rw [Fintype.card_prod, card_vertex]

theorem card_padded_darts_le [Fintype D] [Nonempty V] :
    Fintype.card (Vertex V × D) ≤ ExpanderFamily.growth * Fintype.card (V × D) := by
  rw [Fintype.card_prod, Fintype.card_prod, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_right (Fintype.card D) (card_vertex_le V)

end BinPackingGames.Foundations.PCP.VertexPadding

namespace BinPackingGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

def vertexEquiv (h : n ≤ m) : Fin n ⊕ Fin (m - n) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

@[simp] theorem vertexEquiv_inl (h : n ≤ m) (v : Fin n) :
    vertexEquiv h (Sum.inl v) = v.castLE h := rfl

@[simp] theorem vertexEquiv_inr_val (h : n ≤ m) (v : Fin (m - n)) :
    (vertexEquiv h (Sum.inr v)).val = n + v.val := rfl

@[simp] theorem vertexEquiv_symm_old (h : n ≤ m) (v : Fin n) :
    (vertexEquiv h).symm (v.castLE h) = Sum.inl v :=
  (vertexEquiv h).symm_apply_apply (Sum.inl v)

def dartEquiv (h : n ≤ m) :
    (Fin n ⊕ Fin (m - n)) × Fin d ≃ Fin m × Fin d :=
  Equiv.prodCongr (vertexEquiv h) (Equiv.refl _)

@[simp] theorem dartEquiv_apply (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    dartEquiv h (v, p) = (vertexEquiv h v, p) := rfl

def sumGraph (table : Table n d) (m : Nat) :
    ConstraintGraph (Fin n ⊕ Fin (m - n))
      ((Fin n ⊕ Fin (m - n)) × Fin d) Label :=
  VertexPadding.pad (baseGraph table) (m - n)

def paddedGraph (table : Table n d) (h : n ≤ m) :
    ConstraintGraph (Fin m) (Fin m × Fin d) Label where
  reverse := ((dartEquiv h).symm.trans (sumGraph table m).reverse).trans (dartEquiv h)
  reverse_involutive e := by
    change dartEquiv h ((sumGraph table m).reverse
      ((dartEquiv h).symm (dartEquiv h ((sumGraph table m).reverse
        ((dartEquiv h).symm e))))) = e
    rw [Equiv.symm_apply_apply, (sumGraph table m).reverse_involutive,
      Equiv.apply_symm_apply]
  tail := Prod.fst
  accepts e a b := (sumGraph table m).accepts ((dartEquiv h).symm e) a b
  reverse_accepts e a b := by
    change (sumGraph table m).accepts ((dartEquiv h).symm
      (dartEquiv h ((sumGraph table m).reverse ((dartEquiv h).symm e)))) b a = _
    rw [Equiv.symm_apply_apply]
    exact (sumGraph table m).reverse_accepts _ _ _

theorem paddedGraph_reverse_equiv (table : Table n d) (h : n ≤ m)
    (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (paddedGraph table h).reverse (dartEquiv h e) =
      dartEquiv h ((sumGraph table m).reverse e) := by
  change dartEquiv h ((sumGraph table m).reverse
    ((dartEquiv h).symm (dartEquiv h e))) = _
  rw [Equiv.symm_apply_apply]

theorem paddedGraph_accepts_equiv (table : Table n d) (h : n ≤ m)
    (e : (Fin n ⊕ Fin (m - n)) × Fin d) (a b : Label) :
    (paddedGraph table h).accepts (dartEquiv h e) a b =
      (sumGraph table m).accepts e a b := by
  change (sumGraph table m).accepts ((dartEquiv h).symm (dartEquiv h e)) a b = _
  rw [Equiv.symm_apply_apply]

def pad (table : Table n d) (h : n ≤ m) : Table m d :=
  ofPortGraph
    { rot := (paddedGraph table h).reverse
      rot_involutive := (paddedGraph table h).reverse_involutive }
    (paddedGraph table h).accepts (paddedGraph table h).reverse_accepts

@[simp] theorem rotation_pad (table : Table n d) (h : n ≤ m) (e : Fin m × Fin d) :
    rotation (pad table h) e = (paddedGraph table h).reverse e := by
  exact rotation_ofPortGraph _ _ _ e

@[simp] theorem accepts_pad (table : Table n d) (h : n ≤ m)
    (e : Fin m × Fin d) (a b : Label) :
    PortTables.accepts (pad table h) e a b = (paddedGraph table h).accepts e a b := by
  exact accepts_ofPortGraph _ _ _ e a b

theorem pad_valid (table : Table n d) (h : n ≤ m) :
    Function.Involutive (rotation (pad table h)) ∧
      ∀ e a b, PortTables.accepts (pad table h) (rotation (pad table h) e) b a =
        PortTables.accepts (pad table h) e a b :=
  ⟨rotation_involutive (pad table h), accepts_rotation (pad table h)⟩

private theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem baseGraph_pad (table : Table n d) (h : n ≤ m) :
    baseGraph (pad table h) = paddedGraph table h := by
  apply constraintGraph_ext
  · exact rotation_pad table h
  · rfl
  · funext e a b
    exact accepts_pad table h e a b

theorem rotation_pad_equiv (table : Table n d) (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    rotation (pad table h) (vertexEquiv h v, p) =
      (vertexEquiv h ((sumGraph table m).reverse (v, p)).1,
        ((sumGraph table m).reverse (v, p)).2) := by
  rw [rotation_pad]
  exact paddedGraph_reverse_equiv table h (v, p)

@[simp] theorem rotation_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    rotation (pad table h) (v.castLE h, p) =
      ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  simpa only [sumGraph, VertexPadding.pad_reverse_inl, baseGraph_reverse,
    vertexEquiv_inl] using rotation_pad_equiv table h (Sum.inl v) p

@[simp] theorem rotation_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    rotation (pad table h) (vertexEquiv h (Sum.inr v), p) =
      (vertexEquiv h (Sum.inr v), p) := by
  simpa only [sumGraph, VertexPadding.pad_reverse_inr] using
    rotation_pad_equiv table h (Sum.inr v) p

@[simp] theorem accepts_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) (a b : Label) :
    PortTables.accepts (pad table h) (v.castLE h, p) a b =
      PortTables.accepts table (v, p) a b := by
  rw [accepts_pad]
  exact paddedGraph_accepts_equiv table h (Sum.inl v, p) a b

@[simp] theorem accepts_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) (a b : Label) :
    PortTables.accepts (pad table h) (vertexEquiv h (Sum.inr v), p) a b = true := by
  rw [accepts_pad]
  exact paddedGraph_accepts_equiv table h (Sum.inr v, p) a b

theorem reverseIndex_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (v.castLE h, p)] =
      rowIndex m d ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  rw [← rowIndex_rotation, rotation_pad_old]

theorem reverseIndex_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (vertexEquiv h (Sum.inr v), p)] =
      rowIndex m d (vertexEquiv h (Sum.inr v), p) := by
  rw [← rowIndex_rotation, rotation_pad_new]

private theorem relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

theorem relations_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).relations[rowIndex m d (v.castLE h, p)] =
      table.relations[rowIndex n d (v, p)] := by
  apply relation_ext
  intro a b
  exact accepts_pad_old table h v p a b

theorem relations_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    (pad table h).relations[rowIndex m d (vertexEquiv h (Sum.inr v), p)] =
      Vector.replicate 4096 true := by
  apply relation_ext
  intro a b
  simpa only [PortTables.accepts, GraphTables.relationAt, Fin.getElem_fin,
    Vector.getElem_replicate] using
    accepts_pad_new table h v p a b

theorem paddedGraph_edgeSatisfied_equiv (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (paddedGraph table h).edgeSatisfied labeling (dartEquiv h e) =
      (sumGraph table m).edgeSatisfied (fun v => labeling (vertexEquiv h v)) e := by
  change (sumGraph table m).accepts ((dartEquiv h).symm (dartEquiv h e))
    (labeling (dartEquiv h e).1)
    (labeling (dartEquiv h ((sumGraph table m).reverse
      ((dartEquiv h).symm (dartEquiv h e)))).1) =
    (sumGraph table m).accepts e (labeling (vertexEquiv h e.1))
      (labeling (vertexEquiv h ((sumGraph table m).reverse e).1))
  simp only [Equiv.symm_apply_apply]
  rfl

theorem edgeSatisfied_pad_equiv (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (dartEquiv h e) =
      (sumGraph table m).edgeSatisfied (fun v => labeling (vertexEquiv h v)) e := by
  rw [baseGraph_pad]
  exact paddedGraph_edgeSatisfied_equiv table h labeling e

@[simp] theorem edgeSatisfied_pad_old (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (v : Fin n) (p : Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (v.castLE h, p) =
      (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) (v, p) := by
  simpa only [dartEquiv_apply, vertexEquiv_inl, sumGraph,
    VertexPadding.edgeSatisfied_inl (baseGraph table) rfl] using
    edgeSatisfied_pad_equiv table h labeling (Sum.inl v, p)

@[simp] theorem edgeSatisfied_pad_new (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (v : Fin (m - n)) (p : Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (vertexEquiv h (Sum.inr v), p) = true := by
  simpa only [dartEquiv_apply, sumGraph, VertexPadding.edgeSatisfied_inr] using
    edgeSatisfied_pad_equiv table h labeling (Sum.inr v, p)

theorem pad_rejectionCount (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (baseGraph (pad table h)).rejectionCount labeling =
      (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
  classical
  calc
    (baseGraph (pad table h)).rejectionCount labeling =
        (sumGraph table m).rejectionCount (fun v => labeling (vertexEquiv h v)) := by
      unfold ConstraintGraph.rejectionCount
      symm
      apply Finset.card_equiv (dartEquiv h)
      intro e
      simp only [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_pad_equiv]
    _ = (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
      simpa only [sumGraph, vertexEquiv_inl] using
        VertexPadding.pad_rejectionCount (baseGraph table) rfl (m - n)
          (fun v => labeling (vertexEquiv h v))

theorem pad_labeling_satisfies_iff (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (∀ e, (baseGraph (pad table h)).edgeSatisfied labeling e = true) ↔
      ∀ e, (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) e = true := by
  constructor
  · intro hs e
    simpa only [edgeSatisfied_pad_old] using hs (e.1.castLE h, e.2)
  · intro hs e
    obtain ⟨v, hv⟩ := (vertexEquiv h).surjective e.1
    have he : e = (vertexEquiv h v, e.2) := Prod.ext hv.symm rfl
    rw [he]
    cases v with
    | inl v => simpa only [vertexEquiv_inl, edgeSatisfied_pad_old] using hs (v, e.2)
    | inr v => exact edgeSatisfied_pad_new table h labeling v e.2

def extendLabeling (h : n ≤ m) (labeling : Fin n → Label) : Fin m → Label :=
  fun v => Sum.elim labeling (fun _ => 0) ((vertexEquiv h).symm v)

@[simp] theorem extendLabeling_old (h : n ≤ m) (labeling : Fin n → Label) (v : Fin n) :
    extendLabeling h labeling (v.castLE h) = labeling v := by
  simp only [extendLabeling, vertexEquiv_symm_old, Sum.elim_inl]

theorem pad_satisfiable_iff (table : Table n d) (h : n ≤ m) :
    (baseGraph (pad table h)).Satisfiable ↔ (baseGraph table).Satisfiable := by
  constructor
  · rintro ⟨labeling, hs⟩
    exact ⟨fun v => labeling (v.castLE h), (pad_labeling_satisfies_iff table h labeling).1 hs⟩
  · rintro ⟨labeling, hs⟩
    refine ⟨extendLabeling h labeling, (pad_labeling_satisfies_iff table h _).2 ?_⟩
    simpa only [extendLabeling_old] using hs

end BinPackingGames.Foundations.PCP.PreprocessingPaddingTables

noncomputable section

namespace BinPackingGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

abbrev Vertex (G : ConstraintGraph V E A) := VertexPadding.Vertex (Regularization.Vertex G)
abbrev OverlayPort := Regularization.Port ⊕ ExpanderFamily.Port
abbrev Port := Bool × OverlayPort

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

private theorem card_lazy_sum {X Y : Type*} [Fintype X] [Fintype Y]
    (a b : Nat) (hX : Fintype.card X = a) (hY : Fintype.card Y = b) :
    Fintype.card (Bool × (X ⊕ Y)) = 2 * (a + b) := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_sum, hX, hY]

private theorem doubled_add (a : Nat) : 2 * (2 * a + 1) = 2 * ((a + 1) + a) := by omega

theorem degree_eq_card : degree = Fintype.card Port := by
  have hr : Fintype.card Regularization.Port = Expanders.baseDegree ^ 2 + 1 :=
    Regularization.degree_eq.trans
      (congrArg (fun n : Nat => n + 1) ExpanderFamily.card_port)
  have hp : Fintype.card Port =
      2 * ((Expanders.baseDegree ^ 2 + 1) + Expanders.baseDegree ^ 2) :=
    card_lazy_sum _ _ hr ExpanderFamily.card_port
  exact (doubled_add _).trans hp.symm

theorem degree_positive : 0 < degree := by
  unfold degree
  omega

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hg : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  exact Nat.mul_pos (Nat.pow_pos hg) degree_positive

def paddedGraph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Regularization.Port) A :=
  VertexPadding.paddedG (Regularization.graph G)

def overlayExpander (G : ConstraintGraph V E A) :
    PortGraph (Vertex G) ExpanderFamily.Port :=
  GraphTransport.reindex
    (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Regularization.Vertex G))))
    (VertexPadding.familyVertexEquiv (Regularization.Vertex G)).symm (Equiv.refl _)

omit [Fintype A] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A] in
theorem overlayExpander_certificate (G : ConstraintGraph V E A) :
    SpectralCertificate (overlayExpander G) (1 / 2 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (ExpanderFamily.family_certificate _)

def overlayGraph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × OverlayPort) A :=
  Overlay.constraintGraph (paddedGraph G) (overlayExpander G)

def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  LazyConstraint.constraintGraph (overlayGraph G)

def portGraph (G : ConstraintGraph V E A) : PortGraph (Vertex G) Port :=
  Overlay.originalPortGraph (graph G)

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) : (graph G).tail = Prod.fst := rfl

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
@[simp] theorem graph_reverse (G : ConstraintGraph V E A) :
    (graph G).reverse = (portGraph G).rot := rfl

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
theorem accepts_reverse (G : ConstraintGraph V E A) (e : Vertex G × Port) (a b : A) :
    (graph G).accepts ((portGraph G).rot e) b a = (graph G).accepts e a b :=
  (graph G).reverse_accepts e a b

omit [Fintype A] [DecidableEq E] [Nonempty E] [Nonempty A] in
theorem portGraph_eq_lazyGraph (G : ConstraintGraph V E A) :
    portGraph G = lazyGraph (Overlay.originalPortGraph (overlayGraph G)) := rfl

omit [Fintype A] [DecidableEq E] [Nonempty A] in
theorem overlayGraph_certificate (G : ConstraintGraph V E A) :
    SpectralCertificate (Overlay.originalPortGraph (overlayGraph G)) (7 / 8 : ℝ) := by
  apply Overlay.constraintGraph_spectralCertificate
  · exact Regularization.degree_eq
  · have h := ExpanderFamily.port_degree_ge_eight
    omega
  · exact overlayExpander_certificate G

omit [Fintype A] [DecidableEq E] [Nonempty A] in
theorem spectral_certificate (G : ConstraintGraph V E A) :
    SpectralCertificate (portGraph G) (31 / 32 : ℝ) := by
  rw [portGraph_eq_lazyGraph]
  exact LazySpectral.lazy_certificate_31_32 _ (overlayGraph_certificate G)

omit [Fintype A] [DecidableEq E] [DecidableEq A] [Nonempty A] in
theorem vertex_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G) ≤ ExpanderFamily.growth ^ 2 * Fintype.card E := by
  calc
    _ ≤ ExpanderFamily.growth * Fintype.card (Regularization.Vertex G) :=
      VertexPadding.card_vertex_le _
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * Fintype.card E) :=
      Nat.mul_le_mul_left _ (Regularization.vertex_count_le G)
    _ = _ := by ring

omit [Fintype A] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A] in
theorem dart_count (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) = Fintype.card (Vertex G) * degree := by
  rw [Fintype.card_prod, ← degree_eq_card]

omit [Fintype A] [DecidableEq E] [DecidableEq A] [Nonempty A] in
theorem dart_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) ≤ sizeFactor * Fintype.card E := by
  rw [dart_count]
  calc
    _ ≤ (ExpanderFamily.growth ^ 2 * Fintype.card E) * degree :=
      Nat.mul_le_mul_right degree (vertex_count_le G)
    _ = _ := Nat.mul_right_comm _ _ _

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : Vertex G → A :=
  VertexPadding.liftLabel (Classical.choice ‹Nonempty A›) (Regularization.liftLabel G labeling)

omit [Fintype A] [DecidableEq E] [Nonempty E] in
theorem lift_rejectionCount (G : ConstraintGraph V E A) (labeling : V → A) :
    (graph G).rejectionCount (liftLabel G labeling) = G.rejectionCount labeling := by
  unfold graph
  rw [LazyConstraint.rejectionCount_eq _ rfl]
  unfold overlayGraph
  rw [Overlay.rejectionCount_eq _ _ rfl]
  unfold paddedGraph liftLabel
  rw [VertexPadding.rejectionCount_liftLabel _ rfl]
  exact Regularization.lift_rejectionCount G labeling

omit [Fintype A] [DecidableEq E] [Nonempty E] in
theorem completeness (G : ConstraintGraph V E A) (hG : G.Satisfiable) :
    (graph G).Satisfiable := by
  apply (LazyConstraint.satisfiable_iff _ rfl).mpr
  apply (Overlay.satisfiable_iff _ _ rfl).mpr
  exact VertexPadding.paddedG_satisfiable (Regularization.graph G) rfl
    (Classical.choice ‹Nonempty A›) (Regularization.completeness G hG)

def roundLabels (G : ConstraintGraph V E A) (labeling : Vertex G → A) : V → A :=
  Regularization.roundLabels G (fun v => labeling (Sum.inl v))

omit [Nonempty E] in
theorem soundness (G : ConstraintGraph V E A) (labeling : Vertex G → A) :
    G.rejectionCount (roundLabels G labeling) ≤ (graph G).rejectionCount labeling := by
  calc
    _ ≤ (Regularization.graph G).rejectionCount (fun v => labeling (Sum.inl v)) :=
      Regularization.soundness G _
    _ = (paddedGraph G).rejectionCount labeling :=
      (VertexPadding.paddedG_rejectionCount (Regularization.graph G) rfl labeling).symm
    _ = (overlayGraph G).rejectionCount labeling :=
      (Overlay.rejectionCount_eq (paddedGraph G) (overlayExpander G) rfl labeling).symm
    _ = (graph G).rejectionCount labeling :=
      (LazyConstraint.rejectionCount_eq (overlayGraph G) rfl labeling).symm

omit [Nonempty E] in
theorem satisfiable_iff (G : ConstraintGraph V E A) :
    (graph G).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, hlabel⟩
    by_contra hG
    have hpositive := G.rejectionCount_positive hG (roundLabels G labeling)
    have hzero : (graph G).rejectionCount labeling = 0 := by
      simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts, hlabel]
    have hsound := soundness G labeling
    omega
  · exact completeness G

theorem gap_transfer (G : ConstraintGraph V E A) (epsilon : ℚ) (he : 0 ≤ epsilon)
    (lower : ∀ labeling : V → A,
      epsilon * Fintype.card E ≤ (G.rejectionCount labeling : ℚ))
    (labeling : Vertex G → A) :
    (epsilon / sizeFactor) * Fintype.card (Vertex G × Port) ≤
      ((graph G).rejectionCount labeling : ℚ) := by
  have hfactor : (0 : ℚ) < sizeFactor := by exact_mod_cast sizeFactor_positive
  have hcard : (Fintype.card (Vertex G × Port) : ℚ) ≤
      sizeFactor * Fintype.card E := by exact_mod_cast dart_count_le G
  calc
    _ ≤ (epsilon / sizeFactor) * (sizeFactor * Fintype.card E) :=
      mul_le_mul_of_nonneg_left hcard (div_nonneg he hfactor.le)
    _ = epsilon * Fintype.card E := by field_simp
    _ ≤ (G.rejectionCount (roundLabels G labeling) : ℚ) := lower _
    _ ≤ ((graph G).rejectionCount labeling : ℚ) := by exact_mod_cast soundness G labeling

theorem gap_transfer_real (G : ConstraintGraph V E A) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (lower : ∀ labeling : V → A,
      epsilon * Fintype.card E ≤ (G.rejectionCount labeling : ℝ))
    (labeling : Vertex G → A) :
    (epsilon / sizeFactor) * Fintype.card (Vertex G × Port) ≤
      ((graph G).rejectionCount labeling : ℝ) := by
  have hfactor : (0 : ℝ) < sizeFactor := by exact_mod_cast sizeFactor_positive
  have hcard : (Fintype.card (Vertex G × Port) : ℝ) ≤
      sizeFactor * Fintype.card E := by exact_mod_cast dart_count_le G
  calc
    _ ≤ (epsilon / sizeFactor) * (sizeFactor * Fintype.card E) :=
      mul_le_mul_of_nonneg_left hcard (div_nonneg he hfactor.le)
    _ = epsilon * Fintype.card E := by field_simp
    _ ≤ (G.rejectionCount (roundLabels G labeling) : ℝ) := lower _
    _ ≤ ((graph G).rejectionCount labeling : ℝ) := by exact_mod_cast soundness G labeling

end BinPackingGames.Foundations.PCP.Preprocessing

end

namespace BinPackingGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

private theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem ofFn_split {α : Type*} (h : n ≤ m) (f : Fin m → α) :
    List.ofFn f =
      List.ofFn (fun v : Fin n => f (v.castLE h)) ++
        List.ofFn (fun v : Fin (m - n) => f (PreprocessingPaddingTables.vertexEquiv h (.inr v))) := by
  calc
    List.ofFn f = List.ofFn
        (fun v : Fin (n + (m - n)) => f (Fin.cast (Nat.add_sub_of_le h) v)) :=
      List.ofFn_congr (Nat.add_sub_of_le h).symm f
    _ = _ := by rw [List.ofFn_add]; rfl

theorem flatten_ofFn_rowIndex {α : Type*} (f : Fin (n * d) → List α) :
    (List.ofFn f).flatten =
      (List.ofFn (fun v : Fin n =>
        (List.ofFn (fun p : Fin d => f (rowIndex n d (v, p)))).flatten)).flatten := by
  rw [List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val, Nat.mul_comm, Nat.add_comm]

def rowBits (table : Table n d) (v : Fin n) (p : Fin d) : List Bool :=
  encodeWord v.val ++ encodeWord (table.reverseIndex[rowIndex n d (v, p)]).val ++
    encodeWords (GraphTables.relationWords table.relations[rowIndex n d (v, p)])

def vertexBits (table : Table n d) (v : Fin n) : List Bool :=
  (List.ofFn (fun p : Fin d => rowBits table v p)).flatten

def rowsBits (table : Table n d) : List Bool :=
  encodeWords ((flatRows table).toList.flatMap GraphTables.rowWords)

theorem rowBits_flat (table : Table n d) (i : Fin (n * d)) :
    encodeWords (GraphTables.rowWords ((flatRows table)[i])) =
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2 := by
  simp only [flatRows, Vector.getElem_ofFn, Fin.getElem_fin,
    MachineTableRows.rowBits_eq, rowBits, Prod.eta, Equiv.apply_symm_apply]

theorem rowsBits_eq_vertices (table : Table n d) :
    rowsBits table = (List.ofFn (fun v : Fin n => vertexBits table v)).flatten := by
  have hflat : (flatRows table).toList =
      List.ofFn (fun i : Fin (n * d) => (flatRows table)[i]) := by
    simp only [flatRows, Vector.toList_ofFn, Vector.getElem_ofFn, Fin.getElem_fin]
  unfold rowsBits
  rw [hflat, encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun i : Fin (n * d) =>
    encodeWords (GraphTables.rowWords ((flatRows table)[i])))).flatten = _
  simp_rw [rowBits_flat]
  simpa only [Equiv.symm_apply_apply, vertexBits] using
    flatten_ofFn_rowIndex (fun i : Fin (n * d) =>
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2)

theorem rowBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h) (v.castLE h) p = rowBits table v p := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_old,
    PreprocessingPaddingTables.relations_pad_old]
  have he : (rowIndex m d ((rotation table (v, p)).1.castLE h,
      (rotation table (v, p)).2)).val = (table.reverseIndex[rowIndex n d (v, p)]).val := by
    rw [← rowIndex_rotation]
    rfl
  rw [he]
  rfl

theorem rowBits_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) p =
      MachineDummyRows.rowBits (n + v.val) (p.val + d * (n + v.val)) := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_new,
    PreprocessingPaddingTables.relations_pad_new]
  rfl

theorem dummy_rowsBits_eq_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn (fun p : Fin count => MachineDummyRows.rowBits v (e + p.val))).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext p
    congr 1
    omega

theorem paddingBits_eq_ofFn (d v e count : Nat) :
    MachinePaddingRows.paddingBits d v e count =
      (List.ofFn (fun k : Fin count =>
        MachineDummyRows.rowsBits (v + k.val) (e + k.val * d) d)).flatten := by
  induction count generalizing v e with
  | zero => rfl
  | succ count ih =>
    rw [MachinePaddingRows.paddingBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Fin.val_succ, Nat.add_mul, Nat.one_mul]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext k
    congr 1 <;> omega

@[simp] theorem vertexBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) :
    vertexBits (PreprocessingPaddingTables.pad table h) (v.castLE h) = vertexBits table v := by
  simp only [vertexBits, rowBits_pad_old]

theorem vertexBits_pad_new (table : Table n d) (h : n ≤ m) (v : Fin (m - n)) :
    vertexBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) =
      MachineDummyRows.rowsBits (n + v.val) (n * d + v.val * d) d := by
  unfold vertexBits
  simp_rw [rowBits_pad_new]
  rw [dummy_rowsBits_eq_ofFn]
  apply congrArg (fun f : Fin d → List Bool => (List.ofFn f).flatten)
  funext p
  congr 1
  ring

theorem rowsBits_pad (table : Table n d) (h : n ≤ m) :
    rowsBits (PreprocessingPaddingTables.pad table h) =
      rowsBits table ++ MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  rw [rowsBits_eq_vertices, ofFn_split h, List.flatten_append]
  simp_rw [vertexBits_pad_old, vertexBits_pad_new]
  rw [← rowsBits_eq_vertices, ← paddingBits_eq_ofFn]

theorem tableBits_pad (table : Table n d) (h : n ≤ m) :
    tableBits (PreprocessingPaddingTables.pad table h) =
      encodeWords [m, m * d] ++ rowsBits table ++
        MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  change encodeWords (PortTables.tableWords (PreprocessingPaddingTables.pad table h)) = _
  rw [tableWords_eq, encodeWords_append]
  change encodeWords [m, m * d] ++ rowsBits (PreprocessingPaddingTables.pad table h) = _
  rw [rowsBits_pad, List.append_assoc]

end BinPackingGames.Foundations.PCP.PreprocessingPaddingWords

namespace BinPackingGames.Foundations.PCP.FinalConstants

def alphabet : Nat := 64
def compositionLoss : Nat := 12288
def denominator : Nat := 16 * alphabet ^ 4 * 66 * compositionLoss
def windowHalf : Nat := denominator * Preprocessing.sizeFactor
def windowSize : Nat := 2 * windowHalf + 1
def smoothingScale : Nat := 4 * alphabet * windowHalf
def endpointLength : Nat := smoothingScale ^ 2
def walkLength : Nat := 2 * endpointLength + 1

noncomputable def gain : ℝ := (windowSize : ℝ) / denominator
noncomputable def cap : ℝ := 1 / (walkLength : ℝ)

theorem denominator_positive : 0 < denominator := by
  norm_num [denominator, alphabet, compositionLoss]

theorem windowHalf_positive : 0 < windowHalf :=
  Nat.mul_pos denominator_positive Preprocessing.sizeFactor_positive

theorem walkLength_positive : 0 < walkLength := by
  simp [walkLength]

theorem gain_large : 2 * (Preprocessing.sizeFactor : ℝ) ≤ gain := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  apply (le_div_iff₀ hd).2
  simp only [windowSize, windowHalf, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  nlinarith

theorem cap_positive : 0 < cap := by
  exact one_div_pos.mpr (by exact_mod_cast walkLength_positive)

theorem cap_le_one : cap ≤ 1 := by
  apply (div_le_one (by exact_mod_cast walkLength_positive)).2
  exact_mod_cast walkLength_positive

theorem composed_gap (epsilon : ℝ) (he : 0 ≤ epsilon) :
    min (2 * epsilon) cap ≤
      gain * min (epsilon / (Preprocessing.sizeFactor : ℝ))
        (1 / (walkLength : ℝ)) := by
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hs1 : (1 : ℝ) ≤ Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hg : 0 ≤ gain := le_trans (by positivity) gain_large
  rw [mul_min_of_nonneg _ _ hg]
  apply min_le_min
  · calc
      2 * epsilon = (2 * (Preprocessing.sizeFactor : ℝ)) *
          (epsilon / (Preprocessing.sizeFactor : ℝ)) := by field_simp
      _ ≤ gain * (epsilon / (Preprocessing.sizeFactor : ℝ)) :=
        mul_le_mul_of_nonneg_right gain_large (div_nonneg he hs.le)
  · change cap ≤ gain * cap
    have hgain : 1 ≤ gain := by linarith [gain_large]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hgain cap_positive.le

end BinPackingGames.Foundations.PCP.FinalConstants

end OAI
