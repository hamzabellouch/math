import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBudgetSampling

namespace OAI

/-! # The surviving representation and the resource event in the same trial -/

noncomputable section

namespace LowSpaceSubsetSum

/-- Combine each adjacent pair of leaves into its parent child. -/
def backgroundChild (b : Fin 2 × Fin 4) : Fin 4 :=
  ⟨2 * b.1.val + b.2.val / 2, by omega⟩

theorem backgroundChild_eq_iff (b : Fin 2 × Fin 4) (j k : Fin 2) :
    backgroundChild b = ⟨2 * j.val + k.val, by omega⟩ ↔
      b = (j, ⟨2 * k.val, by omega⟩) ∨ b = (j, ⟨2 * k.val + 1, by omega⟩) := by
  simp only [backgroundChild, Prod.ext_iff, Fin.ext_iff]
  omega

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- The four-child assignment used in the survival proof is obtained from
the same computed eight-leaf assignment used for the resource counts. -/
def allocatedChildAssignment (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    BackgroundAssignment n :=
  fun z g x => backgroundChild (R.allocatedBackground z g hn hlog x)

theorem allocated_child_background (z : Layout n) (g : Guesses n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (j k : Fin 2) :
    R.background (R.allocatedChildAssignment hn hlog) z g ⟨2 * j.val + k.val, by omega⟩ =
      (z.2 ∩ R.rawBackground z (R.allocatedBackground z g hn hlog) j ⟨2 * k.val, by omega⟩) ∪
      (z.2 ∩ R.rawBackground z (R.allocatedBackground z g hn hlog) j ⟨2 * k.val + 1, by omega⟩) := by
  classical
  ext x
  simp only [background, outside, allocatedChildAssignment, rawBackground,
    Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_inter, backgroundChild_eq_iff]
  tauto

/-- The concrete computed allocation retains a representation and the
unconditional ambient resource event with probability at least `.9 u^-100`. -/
theorem allocated_representation_with_resources (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    (9 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      R.trialLaw.probability (fun h =>
        R.ActualRepresentation (R.allocatedChildAssignment (by omega) hlog) h ∧
        R.AllocatedResourceGood (by omega) hlog h) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  have hu : 256 ≤ inputScale R.input := by unfold inputScale; omega
  have hfail := R.actual_joint_resource_failure (by omega) hlog hu (fun _ => True)
  have hfail' : R.trialLaw.probability
      (fun h => ¬R.AllocatedResourceGood (by omega) hlog h) ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 := by
    simpa only [true_and] using hfail
  have h := R.actualRepresentation_with_resources
    (R.allocatedChildAssignment (by omega) hlog) hn hmean hden
    (R.AllocatedResourceGood (by omega) hlog) hfail'
  convert h using 1
  ring

end RepresentationSetup

end LowSpaceSubsetSum

end

end OAI
