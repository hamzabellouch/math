import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.FreshTrial
import OAI.Probability.CriticalPercolation.Criticality.BlockIndependence

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E V : Type*}

theorem disjoint_trials_no_success [Countable E] (q : E → unitInterval) (F : V → Set E)
    (U : Finset V) (hdis : (U : Set V).Pairwise (fun v w => Disjoint (F v) (F w))) :
    (law q).real (⋂ v∈U, (allOpen (F v))ᶜ)=
      ∏ v∈U, (1-(law q).real (allOpen (F v))) := by
  have hpair : Pairwise (fun v w : U => Disjoint (F v) (F w)) := by
    intro v w hvw
    exact hdis v.2 w.2 (fun h => hvw (Subtype.ext h))
  have he : (⋂ v∈U, (allOpen (F v))ᶜ)=⋂ v : U, (allOpen (F v))ᶜ := by
    ext ω
    simp
  have hi := (independent_block_family q (fun v : U => F v) hpair).meas_iInter
    (fun v => (measurable_allOpen_block (F v)).compl)
  rw [he,measureReal_def,hi,ENNReal.toReal_prod]
  change (∏ v : U, (law q).real ((allOpen (F v))ᶜ))=_
  rw [Finset.prod_coe_sort U (fun v => (law q).real ((allOpen (F v))ᶜ))]
  apply Finset.prod_congr rfl
  intro v _hv
  exact probReal_compl_eq_one_sub ((blockSigma_le _) _ (measurable_allOpen_block (F v)))

theorem disjoint_trials_no_success_le [Countable E] (q : E → unitInterval) (F : V → Set E)
    (U : Finset V) (hdis : (U : Set V).Pairwise (fun v w => Disjoint (F v) (F w)))
    (K : ℝ) (hK : K ≤ ∑ v∈U, (law q).real (allOpen (F v))) :
    (law q).real (⋂ v∈U, (allOpen (F v))ᶜ) ≤ Real.exp (-K) := by
  rw [disjoint_trials_no_success q F U hdis]
  calc
    _ ≤ ∏ v∈U, Real.exp (-(law q).real (allOpen (F v))) := by
      apply Finset.prod_le_prod₀
      · intro v _hv
        exact sub_nonneg.mpr measureReal_le_one
      · intro v _hv
        simpa only [sub_eq_add_neg,add_comm] using
          Real.add_one_le_exp (-(law q).real (allOpen (F v)))
    _ = Real.exp (-(∑ v∈U, (law q).real (allOpen (F v)))) := by
      rw [← Real.exp_sum,Finset.sum_neg_distrib]
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg hK)

lemma bad_trial_union_bound (q : E → unitInterval) (U : Finset V)
    (Bad : V → Set (Set E)) (s : V → ℝ) (K a : ℝ) (ha : 0 ≤ a)
    (hb : ∀ v∈U, (law q).real (Bad v) ≤ s v*a)
    (hs : (∑ v∈U, s v) ≤ K+1) :
    (law q).real (⋃ v∈U, Bad v) ≤ (K+1)*a := by
  calc
    _ ≤ ∑ v∈U, (law q).real (Bad v) := measureReal_biUnion_finset_le U Bad
    _ ≤ ∑ v∈U, s v*a := Finset.sum_le_sum hb
    _ = (∑ v∈U, s v)*a := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hs ha

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
