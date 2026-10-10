import OAI.Probability.InvariantIsing.Cavity.CavityReplicaComparison
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffZero

namespace OAI

/-! A bounded change of energy on the retained set controls its
normalized two-replica cutoff law, independently of its mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_bounded_cutoff_energy_comparison {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H J : X → ℝ)
    {M₀ M₁ V E M s : ℝ} (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (A : X → ℕ →₀ ℝ) (hA : ∀ x, (A x).sum (fun _ z => z^2) ≤ V)
    (S : Set X) (hE : 0 ≤ E) (hchange : ∀ x ∈ S, |H x-J x| ≤ E)
    (F : (Fin 2 → X) → ℝ) (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) (hs : 0 < s) :
    |(∫ z, cavityCutoffReplicaMean ν (fun x => H x+cylinderField (A x) z) S F
        ∂gaussianCoordinates) -
      ∫ z, cavityCutoffReplicaMean ν (fun x => J x+cylinderField (A x) z) S F
        ∂gaussianCoordinates| ≤ 4*E/s+M^2*s/2 := by
  have hmS : MeasurableSet S := (Set.to_countable S).measurableSet
  have hiH := cylinder_partition_exp_integrable_ae ν H (cavity_bounded_base_exp_integrable ν H hH) A hA
  have hiJ := cylinder_partition_exp_integrable_ae ν J (cavity_bounded_base_exp_integrable ν J hJ) A hA
  by_cases hz : ν S = 0
  · have heH : (∫ z, cavityCutoffReplicaMean ν (fun x => H x+cylinderField (A x) z) S F
        ∂gaussianCoordinates) = 0 := by
      rw [← integral_zero (ℕ → ℝ) ℝ (μ := gaussianCoordinates)]
      apply integral_congr_ae
      filter_upwards [hiH] with z hzH
      exact cavity_cutoff_replica_zero ν _ hzH S hmS hz F
    have heJ : (∫ z, cavityCutoffReplicaMean ν (fun x => J x+cylinderField (A x) z) S F
        ∂gaussianCoordinates) = 0 := by
      rw [← integral_zero (ℕ → ℝ) ℝ (μ := gaussianCoordinates)]
      apply integral_congr_ae
      filter_upwards [hiJ] with z hzJ
      exact cavity_cutoff_replica_zero ν _ hzJ S hmS hz F
    rw [heH, heJ, sub_self, abs_zero]
    positivity
  · let := subtypeReference_probability ν hmS hz
    have heH : (∫ z, cavityCutoffReplicaMean ν (fun x => H x+cylinderField (A x) z) S F
        ∂gaussianCoordinates) = cavityCylinderReplicaMean (subtypeReference ν S)
          (fun x => H x) (fun x => A x) (fun σ => F (fun i => (σ i).val)) := by
      apply integral_congr_ae
      filter_upwards [hiH] with z hzH
      exact cavity_cutoff_replica_subtype_all ν _ hzH S hmS F
    have heJ : (∫ z, cavityCutoffReplicaMean ν (fun x => J x+cylinderField (A x) z) S F
        ∂gaussianCoordinates) = cavityCylinderReplicaMean (subtypeReference ν S)
          (fun x => J x) (fun x => A x) (fun σ => F (fun i => (σ i).val)) := by
      apply integral_congr_ae
      filter_upwards [hiJ] with z hzJ
      exact cavity_cutoff_replica_subtype_all ν _ hzJ S hmS F
    rw [heH, heJ]
    have hb := cavity_bounded_replica_comparison (subtypeReference ν S)
      (fun x => H x) (fun x => J x) (fun x => hH x) (fun x => hJ x)
      (fun x => A x) (fun x => A x) (fun x => hA x) (fun x => hA x)
      (show (0 : ℝ) ≤ 0 from le_rfl) (fun x y => by simp)
      (fun x => hchange x x.property) (fun σ => F (fun i => (σ i).val))
      hM (fun σ => hF _) hs
    norm_num only [Nat.cast_ofNat, mul_zero, add_zero, zero_add] at hb
    exact hb

end InvariantIsing

end

end OAI
