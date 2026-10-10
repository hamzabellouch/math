import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedProbeGenerator
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialRate

namespace OAI

/-! # The original neighboring step in the inward-pivot coordinates

This identifies the actual inside-letter flow used by the polar partition.
Its exponential rate is proportional to the enlargement parameter; the
original subexponential radius is absorbed in one vanishing rate.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Filter
open scoped Manifold Topology

theorem normalized_neighbor_amplitude_le {t R q B c δ r : ℝ}
    (ht : |t| ≤ R * Real.exp ((q + δ * B) * r)) :
    |Real.exp (-((1 - c * δ) * q * r)) * t| ≤
      R * Real.exp ((δ * (B + c * q)) * r) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-((1 - c * δ) * q * r)) *
        (R * Real.exp ((q + δ * B) * r)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = R * Real.exp (-((1 - c * δ) * q * r) + (q + δ * B) * r) := by
      rw [Real.exp_add]
      ring
    _ = _ := by congr 2; ring

namespace CartanWordModel

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

/-- Pulling the given group step back by the actual dilation gives precisely
the exponential of the rescaled original letter. -/
theorem normalized_neighbor_step
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (h : H) (i : Fin M.letterCount) (time : ℝ) (step : F.N.carrier)
    (hstep : F.inclusionN step = Exp (time •
      (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) :
    (S h).symm step = F.ExpN (F.N.equiv
      ((Real.exp (-M.weight i h) * time) • M.letter i)) := by
  have hs : step = F.ExpN (F.N.equiv (time • M.letter i)) :=
    F.closedN.injective (hstep.trans (F.compatibleN (time • M.letter i)).symm)
  apply (S h).injective
  rw [MulEquiv.apply_symm_apply, hS, hs]
  have hn := normalized_probe_generator T M h i time
  rw [← hn]
  have hid : cartanIdealWeightDilation T H h
      (cartanIdealWeightDilation T H (-h) (time • M.letter i)) = time • M.letter i :=
    (cartanIdealWeightDilation T H h).right_inv _
  rw [hid]

/-- The actual normalized neighbor step satisfies the small-rate bound
required by the inside-letter tiling, with no extra amplitude hypothesis. -/
theorem exists_normalized_neighbor_rate
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (i : Fin M.letterCount) (pivot : H) (c B δ : ℝ)
    (scale R time : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (step : ℕ → F.N.carrier)
    (hstep : ∀ n, F.inclusionN (step n) = Exp (time n •
      (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (htime : ∀ n, |time n| ≤ R n * Real.exp
      ((M.weight i pivot + δ * B) * scale n)) :
    ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ n, let h := (scale n * (1 - c * δ)) • pivot
        let t := Real.exp (-M.weight i h) * time n
        (S h).symm (step n) = F.ExpN (F.N.equiv (t • M.letter i)) ∧
          |t| ≤ Real.exp (((B + c * M.weight i pivot) * δ + η n) * scale n) := by
  obtain ⟨η, hη0, hη, hrad⟩ := exists_sequence_subexponential_rate scale R hscale hR
  refine ⟨η, hη0, hη, ?_⟩
  intro n
  dsimp only
  refine ⟨M.normalized_neighbor_step T F S hS _ i _ _ (hstep n), ?_⟩
  have he : M.weight i ((scale n * (1 - c * δ)) • pivot) =
      (1 - c * δ) * M.weight i pivot * scale n := by
    rw [map_smul, smul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ R n * Real.exp ((δ * (B + c * M.weight i pivot)) * scale n) :=
      normalized_neighbor_amplitude_le (htime n)
    _ ≤ Real.exp (scale n * η n) *
        Real.exp ((δ * (B + c * M.weight i pivot)) * scale n) :=
      mul_le_mul_of_nonneg_right (hrad n) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end CartanWordModel
end PolycyclicRecognition

end

end OAI
