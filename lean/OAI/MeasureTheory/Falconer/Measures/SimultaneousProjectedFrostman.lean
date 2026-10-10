import OAI.MeasureTheory.Falconer.Recursion.BoundedPotentialCompact
import OAI.MeasureTheory.Falconer.Recursion.PotentialBallBound

namespace OAI

/-! # Simultaneous Frostman bounds on one positive compact restriction -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem simultaneous_projected_frostman (μ : ProbabilityMeasure (Space d))
    (n : ι → ℕ) (P : ∀ i, Space d →L[ℝ] Space (n i))
    {u : ℝ} (hu : 0 < u)
    (henergy : ∀ i, PlanarFalconer.rieszEnergyOn ((μ : Measure (Space d)).map (P i)) u < ∞) :
    ∃ K : Set (Space d), IsCompact K ∧ 0 < (μ : Measure (Space d)) K ∧
      ∃ C : ℝ, 0 < C ∧ ∀ i,
        FrostmanBallBound (((μ : Measure (Space d)).restrict K).map (P i)) u C := by
  classical
  let f (i : ι) (x : Space d) :=
    euclideanRieszPotential ((μ : Measure (Space d)).map (P i)) u (P i x)
  let F (x : Space d) := ∑ i : ι, f i x
  have hf (i : ι) : Measurable (f i) :=
    (euclideanRieszPotential_measurable _ u).comp (P i).continuous.measurable
  have hF : Measurable F := Finset.measurable_sum _ (fun i _ => hf i)
  have hfinite : (∫⁻ x, F x ∂(μ : Measure (Space d))) < ∞ := by
    rw [show F = (fun x => ∑ i : ι, f i x) from rfl,
      lintegral_finsetSum _ (fun i _ => hf i)]
    apply ENNReal.sum_lt_top.mpr
    intro i _
    exact (integrated_pulled_potential (μ : Measure (Space d)) (P i) u).trans_lt (henergy i)
  obtain ⟨K,hK,hKm,B,hB,hbound⟩ := positive_compact_bounded_function μ F hF
    (ae_lt_top hF hfinite.ne)
  refine ⟨K,hK,hKm,2^u*B,mul_pos (by positivity) hB,?_⟩
  intro i
  apply frostman_of_ae_bounded_potential _ ((μ : Measure (Space d)).map (P i))
    (Measure.map_mono Measure.restrict_le_self (P i).continuous.measurable) hu
  apply (ae_map_iff (P i).continuous.measurable.aemeasurable
    (measurableSet_le (euclideanRieszPotential_measurable _ u) measurable_const)).mpr
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact (Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)).trans (hbound x hx)

end Falconer

end OAI
