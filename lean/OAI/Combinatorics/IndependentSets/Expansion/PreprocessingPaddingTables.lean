import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PortTables
import OAI.Combinatorics.IndependentSets.PCP.VertexPadding

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingPaddingTables

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
    accepts (pad table h) e a b = (paddedGraph table h).accepts e a b := by
  exact accepts_ofPortGraph _ _ _ e a b

theorem pad_valid (table : Table n d) (h : n ≤ m) :
    Function.Involutive (rotation (pad table h)) ∧
      ∀ e a b, accepts (pad table h) (rotation (pad table h) e) b a =
        accepts (pad table h) e a b :=
  ⟨rotation_involutive (pad table h), accepts_rotation (pad table h)⟩

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
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
    accepts (pad table h) (v.castLE h, p) a b = accepts table (v, p) a b := by
  rw [accepts_pad]
  exact paddedGraph_accepts_equiv table h (Sum.inl v, p) a b

@[simp] theorem accepts_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) (a b : Label) :
    accepts (pad table h) (vertexEquiv h (Sum.inr v), p) a b = true := by
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

theorem relation_ext {r s : GraphTables.RelationTable}
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

end IndependentSetsGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
