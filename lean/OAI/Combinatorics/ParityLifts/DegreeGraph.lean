import OAI.Combinatorics.ParityLifts.DegreeForm

namespace OAI

namespace ParityWL.Complexity
attribute [local simp] PolyProgram.congr_degree PolyProgram.comp_degree PolyProgram.pair_degree
  PolyProgram.ite_degree PolyProgram.const_degree PolyProgram.id_degree PolyProgram.fst_degree
  PolyProgram.snd_degree PolyProgram.equal_degree PolyProgram.foldlGrowing_degree
  PolyProgram.foldlBounded_degree PolyProgram.map_degree PolyProgram.reverse_degree
  PolyProgram.mapWith_degree PolyProgram.filter_degree PolyProgram.any_degree
  PolyProgram.expr PolyProgram.of_linear

lemma PolyProgram.finite_degree {n : ℕ} {α : Type} [TreeCodec α] (f : Fin n → α) :
    (PolyProgram.finite f).degree=1 := rfl
lemma PolyProgram.finite2_degree {n m : ℕ} {α : Type} [TreeCodec α] (f : Fin n → Fin m → α) :
    (PolyProgram.finite2 f).degree=1 := rfl
lemma PolyProgram.evalFin_degree (n : ℕ) (α : Type) [TreeCodec α] :
    (PolyProgram.evalFin n α).degree=1 := rfl
lemma PolyProgram.length_degree (α : Type) [TreeCodec α] :
    (PolyProgram.length α).degree=(PolyProgram.length Bool).degree := by
  simp only [PolyProgram.length]; simp
lemma PolyProgram.listShift_degree (α : Type) [TreeCodec α] :
    (PolyProgram.listShift α).degree=1 := rfl
attribute [local simp] PolyProgram.finite_degree PolyProgram.finite2_degree PolyProgram.evalFin_degree
  PolyProgram.length_degree PolyProgram.listShift_degree
lemma PolyProgram.splitAt_degree (α : Type) [TreeCodec α] :
    (PolyProgram.splitAt α).degree=(PolyProgram.splitAt Bool).degree := by
  simp only [PolyProgram.splitAt]; simp
attribute [local simp] PolyProgram.splitAt_degree
lemma PolyProgram.getD_degree (α : Type) [TreeCodec α] (a : α) :
    (PolyProgram.getD α a).degree=(PolyProgram.getD Bool false).degree := by
  simp only [PolyProgram.getD,PolyProgram.drop,PolyProgram.head]; simp
lemma PolyProgram.append_degree (α : Type) [TreeCodec α] :
    (PolyProgram.append α).degree=(PolyProgram.append Bool).degree := by
  simp only [PolyProgram.append,PolyProgram.cons]; simp
attribute [local simp] PolyProgram.getD_degree PolyProgram.append_degree
lemma PolyProgram.flatten_degree (α : Type) [TreeCodec α] :
    (PolyProgram.flatten α).degree=(PolyProgram.flatten Bool).degree := by
  simp only [PolyProgram.flatten]; simp
attribute [local simp] PolyProgram.flatten_degree

lemma PolyProgram.choiceEntry_degree (t : ℕ) :
    (PolyProgram.choiceEntry t).degree=(PolyProgram.choiceEntry 1).degree := by
  simp only [PolyProgram.choiceEntry]; simp
lemma PolyProgram.choiceBound_degree (t : ℕ) :
    (PolyProgram.choiceBound t).degree=(PolyProgram.choiceBound 1).degree := by
  simp only [PolyProgram.choiceBound]; simp
attribute [local simp] PolyProgram.choiceEntry_degree PolyProgram.choiceBound_degree
lemma PolyProgram.choiceLabel_degree (t : ℕ) :
    (PolyProgram.choiceLabel t).degree=(PolyProgram.choiceLabel 1).degree := by
  simp only [PolyProgram.choiceLabel]; simp
attribute [local simp] PolyProgram.choiceLabel_degree
lemma PolyProgram.indexSize_degree (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    (PolyProgram.indexSize t b).degree=(PolyProgram.indexSize 1 (fun _ => 0)).degree := by
  simp only [PolyProgram.indexSize]; simp
attribute [local simp] PolyProgram.indexSize_degree
lemma PolyProgram.vertices_degree (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    (PolyProgram.vertices t b).degree=(PolyProgram.vertices 1 (fun _ => 0)).degree := by
  unfold PolyProgram.vertices
  simp only [_root_.id]
  simp
attribute [local simp] PolyProgram.vertices_degree
lemma PolyProgram.evalRule_degree (t : ℕ) :
    (PolyProgram.evalRule t).degree=(PolyProgram.evalRule 1).degree := by
  simp only [PolyProgram.evalRule]; simp
attribute [local simp] PolyProgram.evalRule_degree
lemma PolyProgram.edgeTest_degree (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    (PolyProgram.edgeTest t b).degree=(PolyProgram.edgeTest 1 (fun _ => 0)).degree := by
  simp only [PolyProgram.edgeTest]; simp
attribute [local simp] PolyProgram.edgeTest_degree
lemma PolyProgram.matrixRow_degree (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    (PolyProgram.matrixRow t b).degree=(PolyProgram.matrixRow 1 (fun _ => 0)).degree := by
  simp only [PolyProgram.matrixRow]; simp
attribute [local simp] PolyProgram.matrixRow_degree
lemma PolyProgram.matrixRows_degree (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    (PolyProgram.matrixRows t b).degree=(PolyProgram.matrixRows 1 (fun _ => 0)).degree := by
  simp only [PolyProgram.matrixRows]; simp
attribute [local simp] PolyProgram.matrixRows_degree
lemma PolyProgram.rowMatrix_degree (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    (PolyProgram.rowMatrix t b).degree=(PolyProgram.rowMatrix 1 (fun _ => 0)).degree := by
  simp only [PolyProgram.rowMatrix]; simp
attribute [local simp] PolyProgram.rowMatrix_degree
lemma PolyProgram.matrix_degree_form (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    (PolyProgram.matrix t b).degree=
      ((PolyProgram.rowMatrix t b).comp (PolyProgram.flatten Bool)).degree := by
  unfold PolyProgram.matrix
  exact PolyProgram.congr_degree _ _
lemma PolyProgram.matrix_degree (t : ℕ) [NeZero t] (b : TemplateVertex t → Bit) :
    (PolyProgram.matrix t b).degree=(PolyProgram.matrix 1 (fun _ => 0)).degree := by
  rw [PolyProgram.matrix_degree_form,PolyProgram.matrix_degree_form]
  simp
attribute [local simp] PolyProgram.matrix_degree
lemma PolyProgram.vertexCount_degree (t : ℕ) [NeZero t] :
    (PolyProgram.vertexCount t).degree=(PolyProgram.vertexCount 1).degree := by
  simp only [PolyProgram.vertexCount]; simp
attribute [local simp] PolyProgram.vertexCount_degree
lemma PolyProgram.orderPrefix_degree (t : ℕ) [NeZero t] :
    (PolyProgram.orderPrefix t).degree=(PolyProgram.orderPrefix 1).degree := by
  simp only [PolyProgram.orderPrefix]; simp
attribute [local simp] PolyProgram.orderPrefix_degree
lemma PolyProgram.leftOutput_degree (t : ℕ) [NeZero t] :
    (PolyProgram.leftOutput t).degree=(PolyProgram.leftOutput 1).degree := by
  simp only [PolyProgram.leftOutput]; simp
attribute [local simp] PolyProgram.leftOutput_degree
lemma PolyProgram.graphOutput_degree_form (t : ℕ) [NeZero t] :
    (PolyProgram.graphOutput t).degree=
      (((PolyProgram.leftOutput t).pair (PolyProgram.matrix t (starParity t))).comp
        (PolyProgram.append Bool)).degree := by
  unfold PolyProgram.graphOutput
  exact PolyProgram.congr_degree _ _
lemma PolyProgram.graphOutput_degree (t : ℕ) [NeZero t] :
    (PolyProgram.graphOutput t).degree=(PolyProgram.graphOutput 1).degree := by
  rw [PolyProgram.graphOutput_degree_form,PolyProgram.graphOutput_degree_form]
  simp

end ParityWL.Complexity

end OAI
