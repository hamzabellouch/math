import OAI.Combinatorics.ParityLifts.UniformVertices

namespace OAI

namespace ParityWL.Complexity
open Classical

lemma rawIndexed_adj {t : ℕ} (D : ChoiceData t) (odd : Bool)
    (i j : Fin (rawVertices D.raw (rawTags t odd)).length) :
    (rawIndexedGraph D odd).Adj i j ↔ rawEdgeTest D.raw
      ((rawVertices D.raw (rawTags t odd)).get i) ((rawVertices D.raw (rawTags t odd)).get j)=true := by
  let E := List.Nodup.getEquiv _ (rawVertices_nodup D.raw _ (rawTags_nodup t odd))
  let a := (rawVertexEquiv D odd).symm (E i)
  let b := (rawVertexEquiv D odd).symm (E j)
  have ha : rawVertexEncode D odd a=(rawVertices D.raw (rawTags t odd)).get i :=
    congrArg Subtype.val ((rawVertexEquiv D odd).apply_symm_apply (E i))
  have hb : rawVertexEncode D odd b=(rawVertices D.raw (rawTags t odd)).get j :=
    congrArg Subtype.val ((rawVertexEquiv D odd).apply_symm_apply (E j))
  have hh := rawEdgeTest_encode D odd a b
  rw [ha,hb] at hh
  exact hh.symm

def rawMatrix (D : RawChoiceData) (ts : List RawTag) : List Bool :=
  (rawVertices D ts).flatMap (fun x => (rawVertices D ts).map (rawEdgeTest D x))

def rawOutput (D : RawChoiceData) (ts : List RawTag × List RawTag) : List Bool :=
  encodeNat (rawVertices D ts.1).length ++ rawMatrix D ts.1 ++ rawMatrix D ts.2

lemma rawMatrix_eq {t : ℕ} (D : ChoiceData t) (odd : Bool) :
    rawMatrix D.raw (rawTags t odd) =
      (List.ofFn (fun i : Fin (rawVertices D.raw (rawTags t odd)).length =>
        List.ofFn (fun j : Fin (rawVertices D.raw (rawTags t odd)).length =>
          decide ((rawIndexedGraph D odd).Adj i j)))).flatten := by
  have he (i j : Fin (rawVertices D.raw (rawTags t odd)).length) :
      decide ((rawIndexedGraph D odd).Adj i j) =
        rawEdgeTest D.raw ((rawVertices D.raw (rawTags t odd)).get i)
          ((rawVertices D.raw (rawTags t odd)).get j) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using rawIndexed_adj D odd i j
  simp only [he,List.get_eq_getElem,List.ofFn_getElem_eq_map]
  simp only [rawMatrix,List.flatMap_def]
  congr 1
  exact (List.ofFn_getElem_eq_map _ _).symm

lemma rawVertices_length_eq {t : ℕ} (D : ChoiceData t) (ht : 2≤t) :
    (rawVertices D.raw (rawTags t false)).length = (rawVertices D.raw (rawTags t true)).length := by
  have h0 := Fintype.card_congr (rawIndexEquiv D false)
  have h1 := Fintype.card_congr (rawIndexEquiv D true)
  simp only [Fintype.card_fin,tagCharge_false,tagCharge_true] at h0 h1
  exact h0.trans ((choice_lifts_equal_order ht D.system).trans h1.symm)

noncomputable def liftChargeIso {t : ℕ} (D : ChoiceData t) (b b' : TemplateVertex t → Bit) (h : b=b') :
    liftGraph (template t) (baseGraph D.system) (baseProjection D.system) b ≃g
      liftGraph (template t) (baseGraph D.system) (baseProjection D.system) b' := by
  subst b'
  exact RelIso.refl _

theorem rawOutput_spec (k : ℕ) (hk : 4≤k) (c : Convention)
    (D : ChoiceData (bagParameter c k)) :
    ∃ (n : ℕ) (G H : SimpleGraph (Fin n)),
      rawOutput D.raw (rawTags (bagParameter c k) false,rawTags (bagParameter c k) true)=encodeGraphs G H ∧
      (∀ i : Implementation, Equivalent G H c i k ↔ ¬D.system.Successful) ∧
      n = (rawVertices D.raw (rawTags (bagParameter c k) false)).length := by
  let t := bagParameter c k
  have ht : 2≤t := by cases c <;> simp only [t,bagParameter] <;> omega
  let n := (rawVertices D.raw (rawTags t false)).length
  let m := (rawVertices D.raw (rawTags t true)).length
  have he : n=m := rawVertices_length_eq D ht
  let G := rawIndexedGraph D false
  let H := (rawIndexedGraph D true).comap (Fin.cast he)
  have Gi : G ≃g zeroLift D.system := (rawIndexedIso D false).trans
    (liftChargeIso D _ _ (tagCharge_false t))
  have Hi : H ≃g starLift D.system :=
    ((SimpleGraph.Iso.comap (finCongr he) (rawIndexedGraph D true)).trans (rawIndexedIso D true)).trans
      (liftChargeIso D _ _ (tagCharge_true t))
  refine ⟨n,G,H,?_,?_,rfl⟩
  · unfold rawOutput encodeGraphs
    rw [rawMatrix_eq,rawMatrix_eq]
    apply congrArg (fun z => encodeNat n ++ (List.ofFn (fun i : Fin n =>
      List.ofFn (fun j : Fin n => decide (G.Adj i j)))).flatten ++ z)
    exact (matrix_cast he (rawIndexedGraph D true)).symm
  · intro i
    have hp := parity_reduction k hk c D.system
    cases i with
    | commonColors => exact (iso_WLEquivalent G _ H _ Gi Hi c k).trans hp.2.2.1
    | pureUnion => exact (iso_PureWLEquivalent G _ H _ Gi Hi c k).trans hp.2.2.2.1

end ParityWL.Complexity

end OAI
