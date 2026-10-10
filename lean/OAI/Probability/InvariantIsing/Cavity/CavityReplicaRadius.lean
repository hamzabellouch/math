import OAI.Probability.InvariantIsing.Cavity.CavityCappedSpinTest
import OAI.Probability.InvariantIsing.Cavity.CavityMarkedTopology
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffRadii

namespace OAI

/-! The maximum selected-coordinate norm gives exactly the simultaneous
spatial restriction of every replica. A common divergent sequence of
radii avoids the boundaries of all the limiting replica laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityReplicaRadius {m r q d : ℕ} {L : Type*}
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (p : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) : ℝ := ‖J p.2‖

lemma continuous_cavityReplicaRadius {m r q d : ℕ} {L : Type*} [TopologicalSpace L]
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    Continuous (cavityReplicaRadius (L := L) J) :=
  (J.continuous.comp continuous_snd).norm

lemma cavityReplicaRadius_le_iff {m r q d : ℕ} {L : Type*}
    (J : EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d)))
    (p : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))
    {B : ℝ} (hB : 0 ≤ B) :
    cavityReplicaRadius J p ≤ B ↔ ∀ i, 1 + ‖J p.2 i‖^2 ≤ 1+B^2 := by
  rw [cavityReplicaRadius, pi_norm_le_iff_of_nonneg hB]
  apply forall_congr'
  intro i
  constructor
  · intro h
    have hn := sq_le_sq₀ (norm_nonneg (J p.2 i)) hB |>.mpr h
    linarith
  · intro h
    exact (sq_le_sq₀ (norm_nonneg (J p.2 i)) hB).mp (by linarith)

theorem cavity_replica_common_null_radii {m q d : ℕ}
    (L : ℕ → Type*) [∀ r, TopologicalSpace (L r)]
    [∀ r, MeasurableSpace (L r)] [∀ r, BorelSpace (L r)]
    (Q : (r : ℕ) → ProbabilityMeasure
      (L r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
    (J : (r : ℕ) → EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →L[ℝ]
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    ∃ B : ℕ → ℝ, Tendsto B atTop atTop ∧
      ∀ j : ℕ, 0 < B j ∧ ∀ r,
        (Q r : Measure (L r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))
          {p | cavityReplicaRadius (J r) p = B j} = 0 := by
  obtain ⟨B,hlim,hB⟩ := cavity_common_null_cutoff_radii
    (fun r => (Q r : Measure (L r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))))
    (fun r => cavityReplicaRadius (J r))
    (fun r => (continuous_cavityReplicaRadius (J r)).measurable)
  refine ⟨B,hlim,fun j => ⟨?_,(hB j).2.2⟩⟩
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith [(hB j).1]

end InvariantIsing

end

end OAI
