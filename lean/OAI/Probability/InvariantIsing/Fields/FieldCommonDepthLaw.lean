import OAI.Probability.InvariantIsing.Fields.FieldMagnetization
import OAI.Probability.IsingPerceptron.CascadePair

namespace OAI

/-! The common-prefix depth of the actual finite cascade has the field
partition's interval lengths. The statement allows arbitrary tied values. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma fieldLevelIndex_tail_iff (h : FieldStep) (i : Fin h.depth) (s : ℝ) :
    i.val + 1 ≤ (fieldLevelIndex h s).val ↔ h.cut i.succ.castSucc ≤ s := by
  constructor
  · intro hi
    by_contra hs
    have hb : fieldLevelIndex h s ≤ i.castSucc := by
      apply Finset.sup_le
      intro j _
      split_ifs with hj
      · by_contra hji
        have hij : i.succ.castSucc ≤ j.castSucc := by
          change i.val + 1 ≤ j.val
          have hh : i.val < j.val := lt_of_not_ge hji
          omega
        exact hs ((h.ordered_cut.monotone hij).trans hj)
      · exact bot_le
    change (fieldLevelIndex h s).val ≤ i.val at hb
    omega
  · intro hs
    have hi := Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin (h.depth + 1) => if h.cut j.castSucc ≤ s then j else 0)
      (Finset.mem_univ i.succ)
    have hh : i.succ ≤ fieldLevelIndex h s := by
      simpa only [hs, ite_true, fieldLevelIndex] using hi
    exact hh

def fieldCommonLevel (h : FieldStep) (σ : ℕ → LabeledLeaf h.depth) : Fin (h.depth + 1) :=
  ⟨labeledCommonDepth h.depth (σ 0) (σ 1),
    Nat.lt_succ_of_le (labeledCommonDepth_le h.depth (σ 0) (σ 1))⟩

theorem fieldCommonLevel_integral (h : FieldStep) (a : Fin (h.depth + 1) → ℝ) :
    (∫ σ, a (fieldCommonLevel h σ)
      ∂cascadeReplicaLaw h.depth (chainExponent h.cut)) =
        ∫ s, a (fieldLevelIndex h s) ∂pathMeasure := by
  let L := fun s => (fieldLevelIndex h s).val
  have hLm : Measurable L :=
    (measurable_of_countable (Fin.val : Fin (h.depth + 1) → ℕ)).comp
      (fieldLevelIndex_monotone h).measurable
  have hLn : ∀ᵐ s ∂pathMeasure, L s ≤ h.depth :=
    ae_of_all _ fun s => Nat.le_of_lt_succ (fieldLevelIndex h s).isLt
  have hT (i : Fin h.depth) : pathMeasure.real {s | i.val + 1 ≤ L s} =
      1 - chainExponent h.cut i := by
    have he : {s | i.val + 1 ≤ L s} = Ici (h.cut i.succ.castSucc) := by
      ext s
      exact fieldLevelIndex_tail_iff h i s
    rw [he]
    have hc : h.cut i.succ.castSucc ∈ Icc (0 : ℝ) 1 := by
      constructor
      · rw [← h.first]
        exact h.ordered_cut.monotone (Fin.zero_le _)
      · rw [← h.last]
        exact h.ordered_cut.monotone (Fin.le_last _)
    have hb : chainExponent h.cut i = h.cut i.succ.castSucc := by
      rw [chainExponent_apply h.cut i.isLt]
      rfl
    rw [hb]
    exact unitUniform_Ici_real hc
  let a' := fun k : ℕ => a ⟨min k h.depth, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hlaw := cascade_pair_law_of_tails pathMeasure h.depth (chainExponent h.cut)
    (chainExponent_admissible h.ordered_cut h.first h.last) a' hLm hLn hT
  have hmleft : Measurable (fun s => a' (L s)) := (measurable_of_countable a').comp hLm
  have hmright : Measurable (fun σ : ℕ → LabeledLeaf h.depth =>
      cascadeScalarArray h.depth a' σ 0 1) := by
    exact (measurable_pi_apply 1).comp
      ((measurable_pi_apply 0).comp (measurable_cascadeScalarArray h.depth a'))
  have he := congrArg (fun μ : Measure ℝ => ∫ x, x ∂μ) hlaw
  rw [integral_map hmleft.aemeasurable (by fun_prop),
    integral_map hmright.aemeasurable (by fun_prop)] at he
  have hleft (s : ℝ) : a' (L s) = a (fieldLevelIndex h s) := by
    dsimp only [a', L]
    congr 1
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt_succ (fieldLevelIndex h s).isLt)
  have hright (σ : ℕ → LabeledLeaf h.depth) :
      cascadeScalarArray h.depth a' σ 0 1 = a (fieldCommonLevel h σ) := by
    dsimp only [cascadeScalarArray, a', fieldCommonLevel]
    congr 1
    apply Fin.ext
    exact min_eq_left (labeledCommonDepth_le h.depth (σ 0) (σ 1))
  simpa only [hleft, hright] using he.symm

end InvariantIsing

end

end OAI
