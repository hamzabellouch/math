import OAI.Analysis.CircleDomains.Probability.MarkedFusionSmallSets
import Mathlib.Topology.Bases

namespace OAI

/-! Removing all basis neighborhoods whose intersection with a closed candidate
set is test-small leaves a closed nonsmall kernel. Every neighborhood of every
remaining point meets the kernel nonsmally, as needed by the finite fusion split. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity.MarkedHit

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] (ι : C(X, Y))
  [TopologicalSpace Z] [SecondCountableTopology Z]

omit [SecondCountableTopology X] in
theorem exists_closed_hit_test_kernel
    (law : Z → ProbabilityMeasure C(PathTime, Y)) (C : ℝ)
    {A : Set Z} (hA : IsClosed A) (hAn : ¬HitTestSmall ι law C A) :
    ∃ K : Set Z, K ⊆ A ∧ IsClosed K ∧ ¬HitTestSmall ι law C K ∧
      K.Nonempty ∧ ∀ z ∈ K, ∀ V : Set Z, IsOpen V → z ∈ V →
        ¬HitTestSmall ι law C (K ∩ V) := by
  classical
  obtain ⟨B, hB⟩ := TopologicalSpace.exists_seq_basis Z
  let V : ℕ → Set Z := fun n => if HitTestSmall ι law C (A ∩ B n) then B n else ∅
  let U : Set Z := ⋃ n, V n
  let K : Set Z := A \ U
  have hVo (n : ℕ) : IsOpen (V n) := by
    dsimp only [V]
    split
    · exact hB.isOpen (mem_range_self n)
    · exact isOpen_empty
  have hUo : IsOpen U := isOpen_iUnion hVo
  have hdel : HitTestSmall ι law C (A ∩ U) := by
    rw [show A ∩ U = ⋃ n, A ∩ V n from inter_iUnion A V]
    apply hitTestSmall_iUnion ι
    intro n
    dsimp only [V]
    split
    · assumption
    · simpa using hitTestSmall_empty ι law C
  have hKsub : K ⊆ A := sdiff_subset
  have hKn : ¬HitTestSmall ι law C K := by
    intro hK
    apply hAn
    apply HitTestSmall.mono ι (HitTestSmall.union ι hK hdel)
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inr ⟨hz, hzU⟩
    · exact Or.inl ⟨hz, hzU⟩
  have hKne : K.Nonempty := by
    by_contra h
    exact hKn ((not_nonempty_iff_eq_empty.mp h).symm ▸ hitTestSmall_empty ι law C)
  refine ⟨K, hKsub, hA.sdiff hUo, hKn, hKne, ?_⟩
  intro z hz W hWo hzW hsmall
  have hAW : HitTestSmall ι law C (A ∩ W) := by
    apply HitTestSmall.mono ι (HitTestSmall.union ι hsmall hdel)
    intro y hy
    by_cases hyU : y ∈ U
    · exact Or.inr ⟨hy.1, hyU⟩
    · exact Or.inl ⟨⟨hy.1, hyU⟩, hy.2⟩
  obtain ⟨B', hB', hzB', hB'W⟩ := hB.exists_subset_of_mem_open hzW hWo
  obtain ⟨n, rfl⟩ := hB'
  have hn : HitTestSmall ι law C (A ∩ B n) :=
    HitTestSmall.mono ι hAW (inter_subset_inter_right _ hB'W)
  apply hz.2
  exact mem_iUnion.mpr ⟨n, by simpa only [V, ite_eq_left hn] using hzB'⟩

end CircleDomainRigidity.MarkedHit

end

end OAI
