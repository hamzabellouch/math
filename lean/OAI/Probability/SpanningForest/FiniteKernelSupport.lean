import OAI.Probability.SpanningForest.GraphFreeKernel

namespace OAI

noncomputable section

namespace Problem336.FreeKernel

open CoordinateTruncation

theorem finiteKernel_minor_eq_zero_of_absent
    (K : FiniteSubgraphCode) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → EdgeCode) (i : ι) (hi : (e i).1 ∉ K.2) :
    Matrix.det (fun a b => inner ℝ (edgeVector (e a))
      (finiteKernel K (edgeVector (e b)))) = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero i fun j =>
    finiteKernel_inner_edge_eq_zero_of_not_mem K (e i) (edgeVector (e j)) hi

theorem graphKernel_minor_eq_zero_of_nonedge
    (G : GraphCode) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → EdgeCode) (i : ι) (hi : ¬ Adj G (e i).1.1 (e i).1.2) :
    Matrix.det (fun a b => kernelEntry G (e a) (e b)) = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero i fun j =>
    kernelEntry_eq_zero_of_not_adj G (e i) (e j) hi

theorem ustCylinder_eq_zero_of_required_absent (K : FiniteSubgraphCode)
    (A B : Finset EdgeCode) (e : EdgeCode) (he : e ∈ A) (habs : e.1 ∉ K.2) :
    ustCylinder K A B = 0 := by
  classical
  have hz : ∀ T ∈ spanningTrees K,
      ¬ ((∀ a ∈ A, a.1 ∈ T) ∧ (∀ b ∈ B, b.1 ∉ T)) := by
    intro T hT hc
    have hsub : T ⊆ K.2 := (Finset.mem_filter.mp hT).2.1
    exact habs (hsub (hc.1 e he))
  simp only [ustCylinder, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero,
    Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact Or.inl hz

theorem inclusion_identity_of_contained_identity (K : FiniteSubgraphCode)
    (hinside : ∀ A : Finset EdgeCode, (∀ e ∈ A, e.1 ∈ K.2) →
      ustCylinder K A ∅ = ENNReal.ofReal
        (Matrix.det (fun e f : A => inner ℝ (edgeVector e.1)
          (finiteKernel K (edgeVector f.1))))) :
    ∀ A : Finset EdgeCode, ustCylinder K A ∅ = ENNReal.ofReal
      (Matrix.det (fun e f : A => inner ℝ (edgeVector e.1)
        (finiteKernel K (edgeVector f.1)))) := by
  classical
  intro A
  by_cases hA : ∀ e ∈ A, e.1 ∈ K.2
  · exact hinside A hA
  · push Not at hA
    obtain ⟨e, he, habs⟩ := hA
    rw [ustCylinder_eq_zero_of_required_absent K A ∅ e he habs,
      finiteKernel_minor_eq_zero_of_absent K (fun e : A => e.1) ⟨e, he⟩ habs]
    simp

end Problem336.FreeKernel

end

end OAI
