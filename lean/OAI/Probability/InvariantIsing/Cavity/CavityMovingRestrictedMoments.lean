import OAI.Probability.InvariantIsing.Cavity.CavityMovingReweighting
import OAI.Probability.InvariantIsing.Cavity.CavityExtraReplicaPrefix

namespace OAI

/-! Bounded nonnegative restricted weights can be normalized after the
extra-replica limit with a fixed positive denominator regularizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_moving_regularized_test_fin
    {Ω X Ξ Y : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Ξ n)] [∀ n, MeasurableSpace (Y n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : (n : ℕ) → Ξ n → Measure (Y n)) (hρ : ∀ n, Measurable (ρ n))
    [∀ n ω, IsProbabilityMeasure (ρ n ω)]
    (w : (n : ℕ) → Ω n × X n → ℝ) (hw : ∀ n, Measurable (w n))
    (v : (n : ℕ) → Ξ n × Y n → ℝ) (hv : ∀ n, Measurable (v n)) {r : ℕ}
    (F : (n : ℕ) → Ω n × (Fin r → X n) → ℝ) (hF : ∀ n, Measurable (F n))
    (G : (n : ℕ) → Ξ n × (Fin r → Y n) → ℝ) (hG : ∀ n, Measurable (G n))
    {δ M B : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hwb : ∀ n ω x, w n (ω,x) ∈ Icc 0 M) (hvb : ∀ n ω x, v n (ω,x) ∈ Icc 0 M)
    (hFb : ∀ n ω σ, |F n (ω,σ)| ≤ B) (hGb : ∀ n ω σ, |G n (ω,σ)| ≤ B)
    (hmom : ∀ j : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : Fin (r+j) → X n,
        (∏ i, w n (ω,ξ i)) * F n (ω,fun i => ξ (Fin.castAdd j i))
          ∂Measure.pi (fun _ => ν n ω) ∂P n) -
      ∫ ω, ∫ ξ : Fin (r+j) → Y n,
        (∏ i, v n (ω,ξ i)) * G n (ω,fun i => ξ (Fin.castAdd j i))
          ∂Measure.pi (fun _ => ρ n ω) ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, cavityRegularizedReplicaMean (ν n ω) (fun x => w n (ω,x))
        (fun σ => F n (ω,σ)) δ ∂P n) -
      ∫ ω, cavityRegularizedReplicaMean (ρ n ω) (fun x => v n (ω,x))
        (fun σ => G n (ω,σ)) δ ∂Q n) atTop (𝓝 0) := by
  apply cavity_moving_regularized_reweighted_test P Q ν hν ρ hρ w hw v hv F hF G hG
    hδ hM hB hwb hvb hFb hGb
  intro j
  have hp n ω := (cavity_extra_replica_identity (ν n ω) (fun x => w n (ω,x))
    (fun σ => F n (ω,σ)) ((hw n).comp measurable_prodMk_left)
    ((hF n).comp measurable_prodMk_left) j).symm.trans
    (cavity_extra_replica_identity_fin (ν n ω) (fun x => w n (ω,x))
      (fun σ => F n (ω,σ)) ((hw n).comp measurable_prodMk_left)
      ((hF n).comp measurable_prodMk_left) j)
  have hq n ω := (cavity_extra_replica_identity (ρ n ω) (fun x => v n (ω,x))
    (fun σ => G n (ω,σ)) ((hv n).comp measurable_prodMk_left)
    ((hG n).comp measurable_prodMk_left) j).symm.trans
    (cavity_extra_replica_identity_fin (ρ n ω) (fun x => v n (ω,x))
      (fun σ => G n (ω,σ)) ((hv n).comp measurable_prodMk_left)
      ((hG n).comp measurable_prodMk_left) j)
  simpa only [hp,hq] using hmom j

end InvariantIsing

end

end OAI
