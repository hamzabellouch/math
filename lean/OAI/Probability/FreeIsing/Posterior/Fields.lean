import OAI.Probability.FreeIsing.Posterior.FinitePosterior

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Fintype V]

def fieldEnergy (energy : S → ℝ) (spin : S → V → ℝ) (x : V → ℝ) (s : S) : ℝ :=
  energy s + ∑ v, x v * spin s v

def fieldMean (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (x : V → ℝ) : ℝ :=
  (∑ s, observable s * Real.exp (fieldEnergy energy spin x s)) /
    (∑ s, Real.exp (fieldEnergy energy spin x s))

def fieldMass (energy : S → ℝ) (spin : S → V → ℝ) (x : V → ℝ) (s : S) : ℝ :=
  Real.exp (fieldEnergy energy spin x s) / (∑ r, Real.exp (fieldEnergy energy spin x r))

lemma fieldMean_eq_sum_fieldMass (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) :
    fieldMean energy spin observable x = ∑ s, observable s * fieldMass energy spin x s := by
  simp only [fieldMean, fieldMass, ← mul_div_assoc, ← Finset.sum_div]

lemma fieldMean_along_line (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) (t : ℝ) :
    fieldMean energy spin observable (fun v => x v + t * direction v) =
      mean (fieldEnergy energy spin x) (fun s => ∑ v, direction v * spin s v)
        observable t := by
  have heq (s : S) :
      fieldEnergy energy spin (fun v => x v + t * direction v) s =
        fieldEnergy energy spin x s + t * ∑ v, direction v * spin s v := by
    simp only [fieldEnergy, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
    ring
  simp only [fieldMean, heq, mean, partition, weight]

lemma mean_fieldEnergy_zero (energy : S → ℝ) (spin : S → V → ℝ)
    (signal observable : S → ℝ) (x : V → ℝ) :
    mean (fieldEnergy energy spin x) signal observable 0 =
      fieldMean energy spin observable x := by
  simp only [mean, partition, weight, zero_mul, add_zero, fieldMean]

lemma fieldPartition_pos [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (x : V → ℝ) : 0 < ∑ s, Real.exp (fieldEnergy energy spin x s) := by
  exact Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty

lemma fieldMass_pos [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (x : V → ℝ) (s : S) : 0 < fieldMass energy spin x s :=
  div_pos (Real.exp_pos _) (fieldPartition_pos energy spin x)

theorem continuous_fieldMean [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) : Continuous (fieldMean energy spin observable) := by
  unfold fieldMean
  apply Continuous.div
  · unfold fieldEnergy
    fun_prop
  · unfold fieldEnergy
    fun_prop
  · intro x
    exact ne_of_gt (fieldPartition_pos energy spin x)

lemma fieldMean_const [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (x : V → ℝ) (c : ℝ) : fieldMean energy spin (fun _ => c) x = c := by
  rw [← mean_fieldEnergy_zero energy spin (fun _ => 0), mean_const]

lemma fieldMean_spin_mem_Ioo [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hs : ∀ s, observable s = -1 ∨ observable s = 1)
    (hn : ∃ s, observable s = -1) (hp : ∃ s, observable s = 1) :
    fieldMean energy spin observable x ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [← mean_fieldEnergy_zero energy spin (fun _ => 0)]
  exact spin_mean_mem_Ioo _ _ _ _ hs hn hp

theorem hasDerivAt_fieldMean [Nonempty S] (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) :
    HasDerivAt (fun t => fieldMean energy spin observable (fun v => x v + t * direction v))
      (fieldMean energy spin (fun s => observable s * ∑ v, direction v * spin s v) x -
        fieldMean energy spin observable x *
          fieldMean energy spin (fun s => ∑ v, direction v * spin s v) x) 0 := by
  simp_rw [fieldMean_along_line]
  simpa only [mean_fieldEnergy_zero] using
    hasDerivAt_mean (fieldEnergy energy spin x)
      (fun s => ∑ v, direction v * spin s v) observable 0

theorem hasDerivAt_fieldMean_coordinate [Nonempty S] [DecidableEq V]
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (x : V → ℝ) (u : V) :
    HasDerivAt
      (fun t => fieldMean energy spin observable (fun v => x v + if v = u then t else 0))
      (fieldMean energy spin (fun s => observable s * spin s u) x -
        fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s u) x) 0 := by
  have h := hasDerivAt_fieldMean energy spin observable x (fun v => if v = u then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

end Problem367.FinitePosterior

end

end OAI
