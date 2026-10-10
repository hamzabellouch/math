import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitRebase

namespace OAI

/-! # Intrinsic atomicity characterized by a full-measure root transversal -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem intrinsicRootLeaf_dirac_of_nullset_transversal {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t)=x → t=0)
    (N : Set (X n)) (hNzero : μ N=0)
    (htrans : ∀ x ∉ N, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N → t=0) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x=Measure.dirac 0 := by
  have hN : ∀ᵐ x ∂μ, x ∉ N := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hNzero
  have hleaf := ae_intrinsicRootLeaf_of_ambient hij μ hfree hN
  filter_upwards [hN,hleaf,ae_intrinsicRootLeaf_spec hij μ hfree] with x hx hl hs
  let ν := intrinsicRootLeaf hij μ x
  have hz : ∀ᵐ t ∂ν, t=0 := hl.mono (fun t ht => htrans x hx t ht)
  have hunit : ν {0}=1 := by
    calc
      ν {0}=ν (Metric.ball 0 1) := measure_congr (hz.mono (by
        intro t ht
        subst t
        simp))
      _=1 := hs.2
  apply Measure.ext
  intro S hS
  by_cases hzero : (0:ℝ) ∈ S
  · have he : ν S=ν {0} := measure_congr (hz.mono (by
      intro t ht
      subst t
      simp only [hzero,mem_singleton_iff]))
    simp only [ν,he,hunit,Measure.dirac_apply_of_mem hzero]
  · have he : ν S=ν ∅ := measure_congr (hz.mono (by
      intro t ht
      subst t
      simp only [hzero,mem_empty_iff_false]))
    simp only [ν,he,measure_empty,Measure.dirac_apply' _ hS,indicator_of_notMem hzero]

/-- For diagonal-invariant finite measures, atomicity is exactly the
existence of a measurable conull set meeting each root orbit once. -/
theorem intrinsicRootLeaf_dirac_iff_transversal (d : ℕ)
    {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    (∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x=Measure.dirac 0) ↔
      ∃ N : Set (X (d+1)), MeasurableSet N ∧ μ N=0 ∧
        ∀ x ∉ N, ∀ t : ℝ,
          rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N → t=0 := by
  constructor
  · exact exists_nullset_atomic_root_transversal d hij μ hA
  · rintro ⟨N,_,hz,ht⟩
    exact intrinsicRootLeaf_dirac_of_nullset_transversal hij μ
      ((ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij) N hz ht

end DukePrimeDegree

end

end OAI
