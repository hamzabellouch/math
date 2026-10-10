import OAI.Combinatorics.ContingencyTables.Sampling.ExactEntryBoxBound
import OAI.Combinatorics.ContingencyTables.Sampling.ExactResidualInput

namespace OAI

/-! # A single exponential scale for the executed rare-branch measure -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms CompletionCounts Polynomial
open scoped BigOperators Classical
noncomputable section

lemma originalEnumeration_scale {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    gridStateCount (originalEnumerationData (List.ofFn r,List.ofFn c)) ≤ exactBoxScale r c := by
  apply (originalEnumeration_count_bound r c).trans
  have hd : 1 ≤ dimensionAllowance (I := Fin m) (J := Fin n) := by unfold dimensionAllowance; omega
  have hp := Nat.le_self_pow (by decide : 3 ≠ 0) (dimensionAllowance (I := Fin m) (J := Fin n))
  apply Nat.pow_le_pow_right (by decide)
  nlinarith

lemma initialProfile_scale {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) :
    gridStateCount (profileEnumerationData (initialCheck (List.ofFn r,List.ofFn c))) ≤ exactBoxScale r c := by
  rw [initialCheck_code r c htotal]
  apply (profileEnumeration_count_bound r c _ _).trans
  have hp := Nat.le_self_pow (by decide : 3 ≠ 0) (dimensionAllowance (I := Fin m) (J := Fin n))
  apply Nat.pow_le_pow_right (by decide)
  nlinarith

theorem exact_rare_measure_bound : ∃ p a : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
    exactRareMeasure (List.ofFn r,List.ofFn c) ≤
      p.eval (a.eval (Algorithms.samplingSize n r 0)*exactBoxScale r c) := by
  obtain ⟨a,ha⟩ := exact_count_input_measure_polynomial
  obtain ⟨b,hb⟩ := tabulation_preparation_polynomial
  obtain ⟨c,hc⟩ := exact_entry_box_bound
  obtain ⟨d,hd⟩ := exact_parameter_polynomial
  obtain ⟨e,he⟩ := work_exactResidualInput
  obtain ⟨q,hq⟩ := matrixEntryMeasure_polynomial
  let base : Polynomial ℕ := a+b.comp a+c+d+e.comp d+1
  let Q : Polynomial ℕ := q+X
  refine ⟨8*X+2*vectorMeasurePolynomial.comp Q,base,?_⟩
  intro m n r cols htotal
  let z := exactSamplingParameters (List.ofFn r,List.ofFn cols)
  let E := exactBoxScale r cols
  let S := Algorithms.samplingSize n r 0
  let W := base.eval S*E
  let M := Q.eval W
  have hE : 1 ≤ E := exactBoxScale_pos r cols
  have hbase : 1 ≤ base.eval S := by simp only [base,eval_add,eval_one]; omega
  have hEW : E ≤ W := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right E hbase
  have hbaseW : base.eval S ≤ W := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (base.eval S) hE
  have hWM : W ≤ M := by unfold M Q; simp only [eval_add,eval_X]; omega
  have haW : a.eval S ≤ W := (by simp only [base,eval_add,eval_one]; omega : a.eval S ≤ base.eval S).trans hbaseW
  have hbW : (b.comp a).eval S ≤ W :=
    (by simp only [base,eval_add,eval_one]; omega : (b.comp a).eval S ≤ base.eval S).trans hbaseW
  have hcW : c.eval S*E ≤ W := Nat.mul_le_mul_right E (by simp only [base,eval_add,eval_one]; omega)
  have hdW : d.eval S ≤ W := (by simp only [base,eval_add,eval_one]; omega : d.eval S ≤ base.eval S).trans hbaseW
  have heW : (e.comp d).eval S ≤ W :=
    (by simp only [base,eval_add,eval_one]; omega : (e.comp d).eval S ≤ base.eval S).trans hbaseW
  have hcount : scheduledCountInputMeasure z ≤ W := (ha m n r cols htotal).trans haW
  have hparam : exactParameterMeasure (List.ofFn r,List.ofFn cols) ≤ W := (hd m n r cols htotal).trans hdW
  have hres : weight (exactResidualInput (List.ofFn r,List.ofFn cols)) ≤ W := by
    have ht : weight (exactResidualInput (List.ofFn r,List.ofFn cols)) ≤
        e.eval (d.eval S) :=
      (Nat.le_add_left _ _).trans ((he _).trans (polynomial_eval_monotone e (hd m n r cols htotal)))
    exact ht.trans (by simpa only [eval_comp] using heW)
  have hz : weight (List.ofFn r,List.ofFn cols) ≤ W := by
    have hz' : weight z ≤ scheduledCountInputMeasure z := by
      simpa only [eval_X] using weight_le_scheduledCountInputMeasure z
    exact ((weight_fst z).trans hz').trans hcount
  have hprep := hb z
  have hprep_bound : b.eval (scheduledCountInputMeasure z) ≤ W :=
    (polynomial_eval_monotone b (ha m n r cols htotal)).trans (by simpa only [eval_comp] using hbW)
  have houter : weight (scheduledOuterInput z) ≤ M := (hprep.1.trans hprep_bound).trans hWM
  have hN : gridStateCount (profileEnumerationData (initialCheck (List.ofFn r,List.ofFn cols))) ≤ M :=
    (initialProfile_scale r cols htotal).trans (hEW.trans hWM)
  have hO : gridStateCount (originalEnumerationData (List.ofFn r,List.ofFn cols)) ≤ W :=
    (originalEnumeration_scale r cols).trans hEW
  have hv : ∀ v∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn cols)),weight v ≤ M := by
    intro v hv
    exact ((hprep.2.2.1 v hv).trans hprep_bound).trans hWM
  have ho : ∀ o∈originalCandidates (List.ofFn r,List.ofFn cols),weight o ≤ M ∧ weight (o.getD []) ≤ M := by
    intro o ho
    exact ⟨((hprep.2.2.2.1 o ho).1.trans hprep_bound).trans hWM,
      ((hprep.2.2.2.1 o ho).2.trans hprep_bound).trans hWM⟩
  have hentry : ∀ u∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn cols)),
      ∀ v∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn cols)),
      matrixEntryMeasure (scheduledMatrixParameters z,(u,v)) ≤ M := by
    intro u hu v hv
    have hx := (hc m n r cols htotal u hu v hv).trans hcW
    have ht := (hq (scheduledMatrixParameters z,(u,v))).trans (polynomial_eval_monotone q hx)
    apply ht.trans
    unfold M Q
    simp only [eval_add,eval_X]
    omega
  have hsteps : parameterSteps z ≤ M := by
    have hs : parameterSteps z ≤ scheduledCountInputMeasure z := by unfold scheduledCountInputMeasure; omega
    exact hs.trans (hcount.trans hWM)
  have hvector : outerVectorMeasure (scheduledOuterInput z) ≤ vectorMeasurePolynomial.eval M :=
    outerVectorMeasure_bound _ M houter hsteps (hO.trans hWM) hN hv ho hentry
  have hunit := (unit_outerVectorMeasure_le (scheduledOuterInput z)).trans hvector
  have hen : originalEnumerationMeasure (List.ofFn r,List.ofFn cols) ≤ 2*W := by
    unfold originalEnumerationMeasure
    omega
  change _ ≤ (8*X+2*vectorMeasurePolynomial.comp Q).eval W
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_comp]
  change exactParameterMeasure (List.ofFn r,List.ofFn cols)+
    (scheduledCountInputMeasure z+outerVectorMeasure (scheduledOuterInput z)+
      UnitCountPrograms.outerVectorMeasure (scheduledOuterInput z)+
      originalEnumerationMeasure (List.ofFn r,List.ofFn cols)+
      weight (exactResidualInput (List.ofFn r,List.ofFn cols)))+
    originalEnumerationMeasure (List.ofFn r,List.ofFn cols)+weight (List.ofFn r,List.ofFn cols) ≤ _
  change _ ≤ 8*W+2*vectorMeasurePolynomial.eval M
  omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
