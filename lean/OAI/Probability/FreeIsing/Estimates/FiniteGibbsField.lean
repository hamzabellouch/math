import OAI.Probability.FreeIsing.Estimates.PairedFiniteField
import OAI.Probability.FreeIsing.Posterior.Fields

namespace OAI

noncomputable section

namespace Problem367

variable {V : Type*} [Fintype V] [DecidableEq V]

def finiteInteractionEnergy (edges : Finset (V × V)) (beta : ℝ)
    (s : V → IsingSpin) : ℝ :=
  beta * ∑ e ∈ edges, spinSign (s e.1) * spinSign (s e.2)

def siteResidualEnergy (edges : Finset (V × V)) (beta : ℝ) (y : V → ℝ)
    (v : V) (s : V → IsingSpin) : ℝ :=
  finiteInteractionEnergy edges beta s +
    ∑ w ∈ Finset.univ.erase v, y w * spinSign (s w)

theorem siteResidualEnergy_flip_bound (edges : Finset (V × V)) {beta : ℝ}
    (hbeta : 0 ≤ beta) (y : V → ℝ) (v : V)
    (r : {w : V // w ≠ v} → IsingSpin) :
    |siteResidualEnergy edges beta y v ((Equiv.funSplitAt v IsingSpin).symm (.pos, r)) -
      siteResidualEnergy edges beta y v ((Equiv.funSplitAt v IsingSpin).symm (.neg, r))| ≤
      2 * ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * beta := by
  let sp := (Equiv.funSplitAt v IsingSpin).symm (.pos, r)
  let sm := (Equiv.funSplitAt v IsingSpin).symm (.neg, r)
  have hsame (w : V) (hw : w ≠ v) : sp w = sm w := by
    simp [sp, sm, Equiv.funSplitAt_symm_apply, hw]
  have hfield : (∑ w ∈ Finset.univ.erase v, y w * spinSign (sp w)) =
      ∑ w ∈ Finset.univ.erase v, y w * spinSign (sm w) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [hsame w (Finset.mem_erase.mp hw).1]
  have habs (a b : IsingSpin) : |spinSign a * spinSign b| = 1 := by
    cases a <;> cases b <;> norm_num [spinSign]
  have hterm (e : V × V) :
      |spinSign (sp e.1) * spinSign (sp e.2) - spinSign (sm e.1) * spinSign (sm e.2)| ≤
        if e.1 = v ∨ e.2 = v then 2 else 0 := by
    split_ifs with he
    · calc
        _ ≤ |spinSign (sp e.1) * spinSign (sp e.2)| +
            |spinSign (sm e.1) * spinSign (sm e.2)| := by
          simpa using abs_sub_le (spinSign (sp e.1) * spinSign (sp e.2)) 0
            (spinSign (sm e.1) * spinSign (sm e.2))
        _ = 2 := by rw [habs, habs]; norm_num
    · rw [hsame e.1 (not_or.mp he).1, hsame e.2 (not_or.mp he).2]
      simp
  have hsum : |∑ e ∈ edges, (spinSign (sp e.1) * spinSign (sp e.2) -
      spinSign (sm e.1) * spinSign (sm e.2))| ≤
      ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * 2 := by
    calc
      _ ≤ ∑ e ∈ edges, |spinSign (sp e.1) * spinSign (sp e.2) -
          spinSign (sm e.1) * spinSign (sm e.2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ edges, if e.1 = v ∨ e.2 = v then (2 : ℝ) else 0 :=
        Finset.sum_le_sum (fun e _ => hterm e)
      _ = _ := by rw [← Finset.sum_filter]; simp
  change |siteResidualEnergy edges beta y v sp - siteResidualEnergy edges beta y v sm| ≤ _
  unfold siteResidualEnergy finiteInteractionEnergy
  rw [hfield, add_sub_add_right_eq_sub, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul, abs_of_nonneg hbeta]
  nlinarith [mul_le_mul_of_nonneg_left hsum hbeta]

theorem finite_gibbs_site_field_bound (edges : Finset (V × V)) {beta : ℝ}
    (hbeta : 0 ≤ beta) (y : V → ℝ) (v : V) :
    |Real.artanh (FinitePosterior.mean (siteResidualEnergy edges beta y v)
      (fun s => spinSign (s v)) (fun s => spinSign (s v)) (y v)) - y v| ≤
      ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * beta := by
  apply finite_site_posterior_field_bound
  intro r
  simpa only [mul_assoc] using siteResidualEnergy_flip_bound edges hbeta y v r

theorem finite_gibbs_fieldMean_eq (edges : Finset (V × V)) (beta : ℝ)
    (y : V → ℝ) (v : V) :
    FinitePosterior.fieldMean (finiteInteractionEnergy edges beta)
      (fun s w => spinSign (s w)) (fun s => spinSign (s v)) y =
      FinitePosterior.mean (siteResidualEnergy edges beta y v)
        (fun s => spinSign (s v)) (fun s => spinSign (s v)) (y v) := by
  have he (s : V → IsingSpin) :
      FinitePosterior.fieldEnergy (finiteInteractionEnergy edges beta)
        (fun s w => spinSign (s w)) y s =
        siteResidualEnergy edges beta y v s + y v * spinSign (s v) := by
    unfold FinitePosterior.fieldEnergy siteResidualEnergy
    rw [← Finset.sum_erase_add Finset.univ (fun w => y w * spinSign (s w))
      (Finset.mem_univ v)]
    ring
  simp only [FinitePosterior.fieldMean, FinitePosterior.mean, FinitePosterior.partition,
    FinitePosterior.weight, he]

theorem finite_gibbs_posterior_field_bound (edges : Finset (V × V)) {beta : ℝ}
    (hbeta : 0 ≤ beta) (y : V → ℝ) (v : V) :
    |Real.artanh (FinitePosterior.fieldMean (finiteInteractionEnergy edges beta)
      (fun s w => spinSign (s w)) (fun s => spinSign (s v)) y) - y v| ≤
      ((edges.filter (fun e => e.1 = v ∨ e.2 = v)).card : ℝ) * beta := by
  rw [finite_gibbs_fieldMean_eq]
  exact finite_gibbs_site_field_bound edges hbeta y v

end Problem367

end

end OAI
