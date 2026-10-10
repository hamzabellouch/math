import OAI.Probability.FreeIsing.Posterior.Fields

namespace OAI

noncomputable section

open scoped BigOperators ContDiff

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Fintype V]

omit [Fintype S] in

theorem contDiff_fieldEnergy (energy : S → ℝ) (spin : S → V → ℝ)
    (s : S) (n : ℕ∞ω) : ContDiff ℝ n (fun x => fieldEnergy energy spin x s) := by
  unfold fieldEnergy
  fun_prop

theorem contDiff_fieldPartition (energy : S → ℝ) (spin : S → V → ℝ)
    (n : ℕ∞ω) : ContDiff ℝ n (fun x => ∑ s, Real.exp (fieldEnergy energy spin x s)) := by
  apply ContDiff.sum
  intro s _
  exact (contDiff_fieldEnergy energy spin s n).exp

theorem contDiff_fieldMean_all [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (n : ℕ∞ω) : ContDiff ℝ n (fieldMean energy spin observable) := by
  unfold fieldMean
  apply ContDiff.div
  · apply ContDiff.sum
    intro s _
    exact contDiff_const.mul (contDiff_fieldEnergy energy spin s n).exp
  · exact contDiff_fieldPartition energy spin n
  · intro x
    exact ne_of_gt (fieldPartition_pos energy spin x)

theorem contDiff_fieldMass [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (s : S) (n : ℕ∞ω) : ContDiff ℝ n (fun x => fieldMass energy spin x s) := by
  exact (contDiff_fieldEnergy energy spin s n).exp.div
    (contDiff_fieldPartition energy spin n) (fun x => ne_of_gt (fieldPartition_pos energy spin x))

theorem fderiv_fieldMean_apply [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) :
    fderiv ℝ (fieldMean energy spin observable) x direction =
      fieldMean energy spin (fun s => observable s * ∑ v, direction v * spin s v) x -
        fieldMean energy spin observable x *
          fieldMean energy spin (fun s => ∑ v, direction v * spin s v) x := by
  have hd := ((contDiff_fieldMean_all energy spin observable 1).differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • direction) direction 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add x
  have hc := hd.comp_hasDerivAt_of_eq 0 hl (by simp)
  have he := hasDerivAt_fieldMean energy spin observable x direction
  exact (show HasDerivAt
    (fun t => fieldMean energy spin observable (fun v => x v + t * direction v))
      (fderiv ℝ (fieldMean energy spin observable) x direction) 0 from hc).unique he

end Problem367.FinitePosterior

end

end OAI
