import OAI.Combinatorics.ParityLifts.BitGrouping

namespace OAI

namespace ParityWL.Complexity

open Classical

lemma ChoiceData.matrix_eq {t : ℕ} (D : ChoiceData t) (b : TemplateVertex t → Bit) :
    D.matrix b = (List.ofFn (fun i : Fin (D.vertices b).length =>
      List.ofFn (fun j : Fin (D.vertices b).length => decide ((D.indexedGraph b).Adj i j)))).flatten := by
  classical
  have he (i j : Fin (D.vertices b).length) : decide ((D.indexedGraph b).Adj i j) =
      D.edgeTest b ((D.vertices b).get i) ((D.vertices b).get j) := by
    apply Bool.eq_iff_iff.mpr
    simpa using D.indexed_adj b i j
  simp only [he]
  simp only [List.get_eq_getElem, List.ofFn_getElem_eq_map]
  simp only [ChoiceData.matrix, List.flatMap_def]
  congr 1
  exact (List.ofFn_getElem_eq_map _ _).symm

lemma ChoiceData.vertices_length_eq {t : ℕ} (D : ChoiceData t) (ht : 2≤t) :
    (D.vertices (fun _ => 0)).length = (D.vertices (starParity t)).length := by
  have h0 := Fintype.card_congr (D.vertexEquiv (fun _ => 0))
  have h1 := Fintype.card_congr (D.vertexEquiv (starParity t))
  simp only [Fintype.card_fin] at h0 h1
  exact h0.trans ((choice_lifts_equal_order ht D.system).trans h1.symm)

noncomputable def ChoiceData.output {t : ℕ} (D : ChoiceData t) : List Bool :=
  encodeNat (D.vertices (fun _ => 0)).length ++ D.matrix (fun _ => 0) ++ D.matrix (starParity t)

noncomputable def PolyProgram.vertexCount (t : ℕ) [NeZero t] :
    PolyProgram (ChoiceData t) ℕ (fun D => (D.vertices (fun _ => 0)).length) := by
  exact (PolyProgram.vertices t (fun _ => 0)).comp
    (PolyProgram.length (TagIndex t (fun _ => 0) × ℕ))

noncomputable def PolyProgram.orderPrefix (t : ℕ) [NeZero t] :
    PolyProgram (ChoiceData t) (List Bool)
      (fun D => Complexity.encodeNat (D.vertices (fun _ => 0)).length) := by
  refine ((PolyProgram.vertexCount t).comp PolyProgram.encodeNat).congr ?_
  intro D
  rfl

noncomputable def PolyProgram.leftOutput (t : ℕ) [NeZero t] :
    PolyProgram (ChoiceData t) (List Bool)
      (fun D => Complexity.encodeNat (D.vertices (fun _ => 0)).length ++ D.matrix (fun _ => 0)) := by
  refine (((PolyProgram.orderPrefix t).pair (PolyProgram.matrix t (fun _ => 0))).comp
    (PolyProgram.append Bool)).congr ?_
  intro D
  rfl

noncomputable def PolyProgram.graphOutput (t : ℕ) [NeZero t] :
    PolyProgram (ChoiceData t) (List Bool) (fun D => D.output) := by
  refine (((PolyProgram.leftOutput t).pair (PolyProgram.matrix t (starParity t))).comp
    (PolyProgram.append Bool)).congr ?_
  intro D
  rfl

lemma matrix_cast {n m : ℕ} (e : n=m) (G : SimpleGraph (Fin m)) :
    (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n =>
      decide ((G.comap (Fin.cast e)).Adj i j)))).flatten =
    (List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin m => decide (G.Adj i j)))).flatten := by
  classical
  subst m
  rfl

/-- The actual generated bit string is the two full adjacency matrices of the
uncolored simple graphs in the parity reduction, up to proved finite indexing. -/
theorem ChoiceData.output_spec (k : ℕ) (hk : 4≤k) (c : Convention)
    (D : ChoiceData (bagParameter c k)) :
    ∃ (n : ℕ) (G H : SimpleGraph (Fin n)),
      D.output = encodeGraphs G H ∧
      (∀ i : Implementation, Equivalent G H c i k ↔ ¬ D.system.Successful) ∧
      n = (D.vertices (fun _ => 0)).length := by
  classical
  let t := bagParameter c k
  have ht : 2≤t := by cases c <;> simp only [t,bagParameter] <;> omega
  let n := (D.vertices (fun _ => 0)).length
  let m := (D.vertices (starParity t)).length
  have he : n=m := D.vertices_length_eq ht
  let G := D.indexedGraph (fun _ => 0)
  let H := (D.indexedGraph (starParity t)).comap (Fin.cast he)
  have Hiso : H ≃g starLift D.system :=
    (SimpleGraph.Iso.comap (finCongr he) (D.indexedGraph (starParity t))).trans (D.indexedIso (starParity t))
  refine ⟨n,G,H,?_,?_,rfl⟩
  · unfold ChoiceData.output encodeGraphs
    rw [D.matrix_eq, D.matrix_eq]
    apply congrArg (fun z => encodeNat n ++ (List.ofFn (fun i : Fin n =>
      List.ofFn (fun j : Fin n => decide (G.Adj i j)))).flatten ++ z)
    exact (matrix_cast he (D.indexedGraph (starParity t))).symm
  · intro i
    have hp := parity_reduction k hk c D.system
    cases i with
    | commonColors => exact
      (iso_WLEquivalent G (zeroLift D.system) H (starLift D.system) (D.indexedIso _) Hiso c k).trans hp.2.2.1
    | pureUnion => exact
      (iso_PureWLEquivalent G (zeroLift D.system) H (starLift D.system) (D.indexedIso _) Hiso c k).trans hp.2.2.2.1

end ParityWL.Complexity

end OAI
