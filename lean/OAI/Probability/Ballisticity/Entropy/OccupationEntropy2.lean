import Mathlib
import OAI.Probability.Ballisticity.Geometry.WindowProjection
import OAI.Probability.Ballisticity.Estimates.OwnMarginalOccupation

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

lemma rawCurrentWindow_probability {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (τ σ : Environment d → ℕ) (hτm : Measurable τ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    IsProbabilityMeasure (rawCurrentWindow e ν Q τ σ hτm filler) := by
  unfold rawCurrentWindow
  exact (Measure.isProbabilityMeasure_map_iff
    (rawCurrentWindow_measurable e τ σ hτ hσ filler).aemeasurable).2 inferInstance

noncomputable def rawCurrentOccupation {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) (Q : Measure (Environment d))
    (t : ℕ → Environment d → ℕ) (ht : ∀ i, Measurable (t i))
    (filler : Environment d) (N m : ℕ) : Measure (RawCurrentData e × LocalUpperField e) :=
  Entropy.activeSum (Finset.range N)
    (fun i => rawCurrentWindow e ν Q (t i) (t (i+m)) (ht i) filler)
    (fun _ => {p | p.1.1 < N})

instance rawCurrentOccupation_finite {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : ℕ → Environment d → ℕ) (ht : ∀ i, Measurable (t i))
    (filler : Environment d) (N m : ℕ) :
    IsFiniteMeasure (rawCurrentOccupation e ν Q t ht filler N m) := by
  unfold rawCurrentOccupation rawCurrentWindow
  infer_instance

theorem rawCurrentOccupation_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν) ≠ ∞)
    (t : ℕ → Environment d → ℕ) (htm : ∀ i, Measurable (t i))
    (ht : ∀ i n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t i ω=n})
    (hmono : ∀ ω, Monotone (fun i => t i ω))
    (filler : Environment d) (N m : ℕ)
    (hpos : 0 < (rawCurrentOccupation e ν Q t htm filler N m).real Set.univ) :
    haveI : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
    let μs : FiniteMeasure (RawCurrentData e × LocalUpperField e) :=
      ⟨rawCurrentOccupation e ν Q t htm filler N m,inferInstance⟩
    klDiv (μs.normalize : Measure (RawCurrentData e × LocalUpperField e))
      ((μs.normalize : Measure (RawCurrentData e × LocalUpperField e)).fst.prod
        (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))) ≤
      ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal /
        (rawCurrentOccupation e ν Q t htm filler N m).real Set.univ) := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let μ : ℕ → Measure (RawCurrentData e × LocalUpperField e) :=
    fun i => rawCurrentWindow e ν Q (t i) (t (i+m)) (htm i) filler
  let π := Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)
  let A : ℕ → Set (RawCurrentData e) := fun _ => {z | z.1 < N}
  have (i : ℕ) : IsProbabilityMeasure (μ i) :=
    rawCurrentWindow_probability e ν Q (t i) (t (i+m)) (htm i) (ht i) (ht (i+m)) filler
  have hle (i : ℕ) : klDiv (μ i) ((μ i).fst.prod π) ≤
      ownedWindowEntropy e ν Q (t i) (t (i+m)) filler :=
    rawCurrentWindow_kl_le e ν Q (t i) (t (i+m))
      (fun ω => hmono ω (Nat.le_add_right i m)) (ht i) (ht (i+m)) filler
  have hf (i : ℕ) := (ownedWindowEntropy_finite_budget e ν Q hfin (t i) (t (i+m))
    (fun ω => hmono ω (Nat.le_add_right i m)) (ht i) (ht (i+m)) filler).1
  have hkl (i : ℕ) : klDiv (μ i) ((μ i).fst.prod π) ≠ ∞ := ne_top_of_le_ne_top (hf i) (hle i)
  have h := Entropy.own_normalized_activeSum_kl_le (Finset.range N) μ π A
    (fun _ _ => measurableSet_lt measurable_fst measurable_const) (fun i _ => hkl i) hpos
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  apply div_le_div_of_nonneg_right _ hpos.le
  calc
    _ ≤ ∑ i ∈ Finset.range N, (ownedWindowEntropy e ν Q (t i) (t (i+m)) filler).toReal :=
      Finset.sum_le_sum fun i _ => ENNReal.toReal_mono (hf i) (hle i)
    _ ≤ _ := sum_actual_stopped_window_entropy e ν Q hfin t ht hmono filler N m

theorem currentOccupation_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (hfin : klDiv Q (environmentLaw ν) ≠ ∞)
    (t : ℕ → Environment d → ℕ) (htm : ∀ i, Measurable (t i))
    (ht : ∀ i n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t i ω=n})
    (hmono : ∀ ω, Monotone (fun i => t i ω))
    (filler : Environment d) (N m : ℕ)
    (hpos : 0 < (rawCurrentOccupation e ν Q t htm filler N m).real Set.univ) :
    let μs : FiniteMeasure (RawCurrentData e × LocalUpperField e) :=
      ⟨rawCurrentOccupation e ν Q t htm filler N m,inferInstance⟩
    haveI : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
    let out := (μs.normalize : Measure (RawCurrentData e × LocalUpperField e)).map (rawCurrentProjection e)
    klDiv out (out.fst.compProd (currentWindowReference e ν)) ≤
      ENNReal.ofReal ((m:ℝ)*(klDiv Q (environmentLaw ν)).toReal /
        (rawCurrentOccupation e ν Q t htm filler N m).real Set.univ) := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let μs : FiniteMeasure (RawCurrentData e × LocalUpperField e) :=
    ⟨rawCurrentOccupation e ν Q t htm filler N m,inferInstance⟩
  exact (rawCurrentProjection_kl_le e ν (μs.normalize : Measure _)).trans
    (rawCurrentOccupation_kl_le e ν Q hfin t htm ht hmono filler N m hpos)

end DirectionalTransience

end

end OAI
