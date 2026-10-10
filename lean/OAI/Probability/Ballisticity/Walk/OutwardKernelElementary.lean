import Mathlib
import OAI.Probability.Ballisticity.Entropy.BufferCostBounds

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outwardKernelMass_lower {d : ℕ} (e f : Direction d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) {κ : ℝ≥0}
    (hκ : ∀ y, κ ≤ (ω y).1 e) :
    (κ:ℝ)^(2*H) ≤ outwardKernelMass e f H x ω := by
  let S := {y : Lattice d × Lattice d | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)}
  have hlow : ((κ:ℝ≥0∞)^2)^H ≤ rawPairEndpointLaw (realPosition (step e)) H ω x S := by
    induction H with
    | zero => simp [rawPairEndpointLaw_zero,S]
    | succ H ih =>
      have hh := rawPairEndpointLaw_upward e H ω x hκ S
      rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet] at hh
      have hpre : pairUp e ⁻¹' S=S := by
        ext y
        simp only [S,Set.mem_preimage,Set.mem_ofPred,pairUp_preserves_gap]
      rw [hpre] at hh
      apply le_trans _ hh
      rw [pow_succ']
      exact mul_le_mul_right ih _
  have hfinite : rawPairEndpointLaw (realPosition (step e)) H ω x S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((measure_mono (Set.subset_univ _)).trans (rawPairEndpointLaw_total_le_one _ _ _ _))
  have hh := ENNReal.toReal_mono hfinite hlow
  simpa only [ENNReal.toReal_pow,ENNReal.coe_toReal,←pow_mul,outwardKernelMass,S] using hh

lemma rawPairEndpointLaw_upper_congr {d : ℕ} (e : Direction d) (H : ℕ)
    (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a)
    (ω η : Environment d) (he : Set.EqOn ω η {y | a ≤ dot (realPosition y) (realPosition (step e))}) :
    rawPairEndpointLaw (realPosition (step e)) H ω x = rawPairEndpointLaw (realPosition (step e)) H η x := by
  have h₁ : Set.EqOn ω η (Strip (realPosition (step e)) x.1 H) := by
    intro y hy
    apply he
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx.1] using hy.1
  have h₂ : Set.EqOn ω η (Strip (realPosition (step e)) x.2 H) := by
    intro y hy
    apply he
    change a ≤ dot (realPosition y) (realPosition (step e))
    simpa only [hx.2] using hy.1
  unfold rawPairEndpointLaw
  rw [hitKernel_congr _ _ ω η h₁,hitKernel_congr _ _ ω η h₂]
end DirectionalTransience

end

end

end OAI
