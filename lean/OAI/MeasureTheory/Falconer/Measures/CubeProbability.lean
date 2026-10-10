import OAI.MeasureTheory.Falconer.Measures.CubeMass

namespace OAI

/-! # Probability approximants with uniform dyadic Frostman bounds -/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem exists_containing_cube {d : ℕ} (E : Set (Space d)) (hE : IsCompact E) :
    ∃ Q : DyadicCube d, 0 < Q.side ∧ E ⊆ Q.carrier := by
  obtain ⟨R,hR,hbound⟩ := hE.isBounded.exists_pos_norm_lt
  let Q : DyadicCube d := ⟨WithLp.toLp 2 (fun _ => -R),2*R⟩
  refine ⟨Q,by dsimp [Q]; positivity,?_⟩
  intro x hx i
  have hi : |x i| < R := (PiLp.norm_apply_le x i).trans_lt (hbound x hx)
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hi
  change -R ≤ x i ∧ x i < -R+2*R
  exact ⟨hlo.le,by linarith⟩

theorem cube_probability_sequence {d : ℕ} (hd : 1 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E) {s : ℝ≥0} (hs : 0 < s)
    (hDim : (s : ℝ≥0∞) < dimH E) (Q : DyadicCube d)
    (hQ : 0 < Q.side) (hEQ : E ⊆ Q.carrier) :
    ∃ c : ℝ, 0 < c ∧ ∃ μ : ℕ → ProbabilityMeasure (Space d),
      ∀ K, (μ K : Measure (Space d)) Eᶜ = 0 ∧
        ∀ p : List (Fin d → Bool), p.length ≤ K →
          (μ K : Measure (Space d)) (Q.descendant p).carrier ≤
            ENNReal.ofReal (c⁻¹*(Q.descendant p).side^(s:ℝ)) := by
  classical
  obtain ⟨c,hc,hcaps⟩ := exists_uniform_cube_capacity hd E hE hs hDim Q hQ hEQ
  choose ν hmass hcarry hbound using fun K =>
    finite_cube_measure E (s:ℝ) Q hQ K c hc.le (hcaps K)
  have hprob (K : ℕ) : IsProbabilityMeasure (ENNReal.ofReal c⁻¹ • ν K) := by
    constructor
    rw [Measure.smul_apply,smul_eq_mul,hmass K,← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hc.ne',ENNReal.ofReal_one]
  let μ : ℕ → ProbabilityMeasure (Space d) := fun K => ⟨ENNReal.ofReal c⁻¹ • ν K,hprob K⟩
  refine ⟨c,hc,μ,fun K => ⟨?_,?_⟩⟩
  · have hz : ν K Eᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr inter_subset_left) (hcarry K)
    simp [μ,Measure.smul_apply,hz]
  · intro p hp
    change (ENNReal.ofReal c⁻¹ • ν K) _ ≤ _
    rw [Measure.smul_apply,smul_eq_mul,ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_right (hbound K p hp) _

end Falconer

end OAI
