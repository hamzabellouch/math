import OAI.NumberTheory.JointDickman.Arithmetic.OrderedSimplex
import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicMeasureScaling

namespace OAI

/-! # Normalizing the sum cutoff in the ordered logarithmic simplex -/
namespace JointDickman
open Finset MeasureTheory Filter

 theorem orderedSimplexMass_restrict_upper (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (n : ℕ) (u : ℝ) :
    orderedSimplexMass (μ.restrict (Set.Iic u)) n u = orderedSimplexMass μ n u := by
  unfold orderedSimplexMass
  rw [← Measure.restrict_pi_pi, measureReal_def, measureReal_def,
    Measure.restrict_apply (orderedTupleRegion_measurable _ _)]
  congr 1
  apply measure_congr
  have hp : ∀ᵐ t : Fin n → ℝ ∂Measure.pi (fun _ : Fin n => μ), ∀ i, 0 ≤ t i :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (i := i)).eventually hμ)
  filter_upwards [hp] with t ht
  apply propext
  constructor
  · exact And.left
  · intro hr
    refine ⟨hr, ?_⟩
    intro i _
    exact (single_le_sum (fun j _ => ht j) (mem_univ i)).trans hr.2

 theorem orderedTupleRegion_div {u : ℝ} (hu : 0 < u) (n : ℕ) :
    (fun t : Fin n → ℝ => fun i => t i/u) ⁻¹' orderedTupleRegion n 1 =
      orderedTupleRegion n u := by
  ext t
  have hm : StrictMono (fun i => t i/u) ↔ StrictMono t := by
    constructor
    · intro h i j hij
      exact (div_lt_div_iff_of_pos_right hu).mp (h hij)
    · intro h i j hij
      exact (div_lt_div_iff_of_pos_right hu).mpr (h hij)
  simp only [orderedTupleRegion, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
    hm, ← sum_div, div_le_one hu]

 theorem logarithmicSimplexMass_scale {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hu1 : u ≤ 1) (n : ℕ) :
    orderedSimplexMass (logarithmicPrimeMeasure c) n u =
      orderedSimplexMass (logarithmicPrimeMeasure (c/u)) n 1 := by
  have hμ : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), 0 ≤ t := by
    have hs : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), t ∈ Set.Ioc c 1 := by
      rw [ae_iff]
      exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (logarithmicPrimeMeasure_support hc)
    exact hs.mono (fun t ht => (hc.trans ht.1).le)
  rw [← orderedSimplexMass_restrict_upper _ hμ n u]
  have hm : Measure.map (fun t : Fin n → ℝ => fun i => t i/u)
      (Measure.pi (fun _ : Fin n => (logarithmicPrimeMeasure c : Measure ℝ).restrict (Set.Iic u))) =
      Measure.pi (fun _ : Fin n => (logarithmicPrimeMeasure (c/u) : Measure ℝ)) := by
    rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable (fun t : ℝ => t/u)).aemeasurable)]
    congr 1
    funext i
    exact logarithmicPrimeMeasure_scale hc hu hu1
  unfold orderedSimplexMass
  rw [measureReal_def, measureReal_def, ← hm,
    Measure.map_apply (by fun_prop) (orderedTupleRegion_measurable _ _), orderedTupleRegion_div hu]

end JointDickman

end OAI
