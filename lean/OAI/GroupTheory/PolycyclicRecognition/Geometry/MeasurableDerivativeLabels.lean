import OAI.GroupTheory.PolycyclicRecognition.Geometry.DenseDerivativeLabels

namespace OAI

/-! # Measurable selection of the derivative's finite label -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Module

theorem exists_measurable_countable_choice
    {Z J : Type*} [MeasurableSpace Z] [MeasurableSpace J] [Countable J] [Nonempty J]
    (P : J → Z → Prop) (hP : ∀ j, MeasurableSet {z | P j z}) :
    ∃ label : Z → J, Measurable label ∧ ∀ z, (∃ j, P j z) → P (label z) z := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat J
  have hnone : MeasurableSet {z | ¬ ∃ j, P j z} := by
    have hh : MeasurableSet (⋃ j, {z | P j z}) := MeasurableSet.iUnion hP
    convert hh.compl using 1
    ext z
    simp only [mem_iUnion, mem_ofPred_eq, mem_compl_iff]
  let Q : ℕ → Z → Prop := fun n z => P (e n) z ∨ ¬ ∃ j, P j z
  have hQ (n : ℕ) : MeasurableSet {z | Q n z} := (hP (e n)).union hnone
  have hex (z : Z) : ∃ n, Q n z := by
    by_cases hz : ∃ j, P j z
    · obtain ⟨j, hj⟩ := hz
      obtain ⟨n, hn⟩ := he j
      exact ⟨n, Or.inl (hn ▸ hj)⟩
    · exact ⟨0, Or.inr hz⟩
  refine ⟨fun z => e (Nat.find (hex z)), Measurable.find
    (fun _ => measurable_const) hQ hex, ?_⟩
  intro z hz
  exact (Nat.find_spec (hex z)).resolve_right (not_not.mpr hz)

theorem exists_measurable_basis_derivative_label
    {I H W Z J : Type*} [Fintype I] [Countable J] [Nonempty J]
    [AddCommGroup H] [Module ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    [MeasurableSpace Z] [MeasurableSpace J]
    (b : Basis I ℝ H) (q : H → Z → W) (hq : ∀ i, Measurable (q (b i)))
    (A : J → H →ₗ[ℝ] W) :
    ∃ label : Z → J, Measurable label ∧ ∀ z,
      (∃ j, basisDerivativeField b q z = A j) → basisDerivativeField b q z = A (label z) := by
  classical
  let P : J → Z → Prop := fun j z => ∀ i, q (b i) z = A j (b i)
  have hP (j : J) : MeasurableSet {z | P j z} := by
    have h : MeasurableSet (⋂ i, {z | q (b i) z = A j (b i)}) :=
      MeasurableSet.iInter (fun i => measurableSet_eq_fun (hq i) measurable_const)
    convert h using 1
    ext z
    simp only [mem_iInter, mem_ofPred_eq, P]
  obtain ⟨label, hlabel, hchoose⟩ := exists_measurable_countable_choice P hP
  refine ⟨label, hlabel, ?_⟩
  intro z hz
  have hex : ∃ j, P j z := by
    obtain ⟨j, hj⟩ := hz
    refine ⟨j, fun i => ?_⟩
    have h := LinearMap.congr_fun hj (b i)
    simpa only [basisDerivativeField, Basis.constr_basis] using h
  apply b.ext
  intro i
  simpa only [basisDerivativeField, Basis.constr_basis] using hchoose z hex i

end PolycyclicRecognition

end

end OAI
