import OAI.Probability.InvariantIsing.Cavity.CavityExtraReplicaPrefix
import OAI.Probability.InvariantIsing.Cavity.CavityMovingReplicaTest
import OAI.Probability.InvariantIsing.Cavity.CavityCappedLogLimit

namespace OAI

/-! Capped spin-replica normalization from ordinary fourth moments and
finite-prefix numerator limits, as supplied by the physical Haar comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_capped_negative_log_mean_bound_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H)
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => R (ω, x)^4) (ν ω))
    (hmi : Integrable (fun ω => ∫ x, R (ω, x)^4 ∂ν ω) P)
    {D M T : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hg : ∀ ω x, |H (ω, x)| ≤ D * (1 + R (ω, x)^2))
    (hM : (∫ ω, ∫ x, R (ω, x)^4 ∂ν ω ∂P) ≤ M) :
    Integrable (fun ω => (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2) P ∧
    (∫ ω, (max (-Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2 ∂P) ≤
      2 * D^2 * (1 + M) := by
  have hb : ∀ᵐ ω ∂P, (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2 ≤
      2 * D^2 * (1 + ∫ x, R (ω, x)^4 ∂ν ω) := by
    filter_upwards [hi] with ω hω
    exact cavity_capped_log_negative_sq_of_growth (ν ω) (fun x => H (ω, x))
      (fun x => R (ω, x)) (hH.comp measurable_prodMk_left) hω hD hT (hg ω)
  have hZ : Measurable (fun ω => ∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω) :=
    measurable_cavityWeightNormalizer ν hν _ ((hH.min measurable_const).exp)
  have he := ((integrable_const 1).add hmi).const_mul (2 * D^2)
  have hN : Integrable (fun ω => (max (-Real.log
      (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2) P := by
    apply he.mono' ((hZ.log.neg.max measurable_const).pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    change |(max (-Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω)) 0)^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hω
  refine ⟨hN, ?_⟩
  have hh := integral_mono_ae hN he hb
  simp only [Pi.add_apply, integral_const_mul, integral_add (integrable_const 1) hmi,
    integral_const, probReal_univ, one_smul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hM) (by positivity))

theorem cavity_moving_capped_replica
    {Ω X Ξ Y : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Ξ n)] [∀ n, MeasurableSpace (Y n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : (n : ℕ) → Measure (Ξ n)) [∀ n, IsProbabilityMeasure (Q n)]
    (ν : (n : ℕ) → Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (ρ : (n : ℕ) → Ξ n → Measure (Y n)) (hρ : ∀ n, Measurable (ρ n))
    [∀ n ω, IsProbabilityMeasure (ρ n ω)]
    (H R : (n : ℕ) → Ω n × X n → ℝ) (G S : (n : ℕ) → Ξ n × Y n → ℝ)
    (hH : ∀ n, Measurable (H n)) (hG : ∀ n, Measurable (G n)) {r : ℕ}
    (F : (n : ℕ) → Ω n × (Fin r → X n) → ℝ) (hF : ∀ n, Measurable (F n))
    (J : (n : ℕ) → Ξ n × (Fin r → Y n) → ℝ) (hJ : ∀ n, Measurable (J n))
    (hiR : ∀ n, ∀ᵐ ω ∂P n, Integrable (fun x => R n (ω, x)^4) (ν n ω))
    (hiS : ∀ n, ∀ᵐ ω ∂Q n, Integrable (fun x => S n (ω, x)^4) (ρ n ω))
    (hmiR : ∀ n, Integrable (fun ω => ∫ x, R n (ω, x)^4 ∂ν n ω) (P n))
    (hmiS : ∀ n, Integrable (fun ω => ∫ x, S n (ω, x)^4 ∂ρ n ω) (Q n))
    {D M B T : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hgH : ∀ n ω x, |H n (ω, x)| ≤ D * (1 + R n (ω, x)^2))
    (hgG : ∀ n ω x, |G n (ω, x)| ≤ D * (1 + S n (ω, x)^2))
    (hMR : ∀ n, (∫ ω, ∫ x, R n (ω, x)^4 ∂ν n ω ∂P n) ≤ M)
    (hMS : ∀ n, (∫ ω, ∫ x, S n (ω, x)^4 ∂ρ n ω ∂Q n) ≤ M)
    (hFb : ∀ n ω σ, |F n (ω, σ)| ≤ B) (hJb : ∀ n ω σ, |J n (ω, σ)| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto (fun n =>
      (∫ ω, ∫ ξ : Fin (r + k) → X n,
        (∏ i, Real.exp (min (H n (ω, ξ i)) T)) *
          F n (ω, fun i => ξ (Fin.castAdd k i))
          ∂Measure.pi (fun _ => ν n ω) ∂P n) -
      ∫ ω, ∫ ξ : Fin (r + k) → Y n,
        (∏ i, Real.exp (min (G n (ω, ξ i)) T)) *
          J n (ω, fun i => ξ (Fin.castAdd k i))
          ∂Measure.pi (fun _ => ρ n ω) ∂Q n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (∫ ω, cavityWeightedReplicaMean (ν n ω)
        (fun x => Real.exp (min (H n (ω, x)) T)) (fun σ => F n (ω, σ)) ∂P n) -
      ∫ ω, cavityWeightedReplicaMean (ρ n ω)
        (fun x => Real.exp (min (G n (ω, x)) T)) (fun σ => J n (ω, σ)) ∂Q n)
      atTop (𝓝 0) := by
  let w n p := Real.exp (min (H n p) T)
  let v n p := Real.exp (min (G n p) T)
  have hw n : Measurable (w n) := ((hH n).min measurable_const).exp
  have hv n : Measurable (v n) := ((hG n).min measurable_const).exp
  have hwb n ω x : w n (ω, x) ∈ Icc 0 (Real.exp T) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
  have hvb n ω x : v n (ω, x) ∈ Icc 0 (Real.exp T) :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
  have hZn n := cavity_capped_negative_log_mean_bound_ae (P n) (ν n) (hν n) (H n) (R n)
    (hH n) (hiR n) (hmiR n) hD hT (hgH n) (hMR n)
  have hWn n := cavity_capped_negative_log_mean_bound_ae (Q n) (ρ n) (hρ n) (G n) (S n)
    (hG n) (hiS n) (hmiS n) hD hT (hgG n) (hMS n)
  apply cavity_moving_reweighted_test P Q ν hν ρ hρ w hw v hv F hF J hJ
    (K := 2 * D^2 * (1 + M)) (Real.one_le_exp hT) hB (by positivity)
    hwb hvb hFb hJb
  · intro n ω
    apply MeasureTheory.integral_exp_pos
    exact integrable_of_measurable_abs_le ((hw n).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hwb n ω x).2)
  · intro n ω
    apply MeasureTheory.integral_exp_pos
    exact integrable_of_measurable_abs_le ((hv n).comp measurable_prodMk_left)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hvb n ω x).2)
  · exact fun n => (hZn n).1
  · exact fun n => (hWn n).1
  · exact fun n => (hZn n).2
  · exact fun n => (hWn n).2
  · intro k
    have hp n ω := (cavity_extra_replica_identity (ν n ω) (fun x => w n (ω, x))
      (fun σ => F n (ω, σ)) ((hw n).comp measurable_prodMk_left)
      ((hF n).comp measurable_prodMk_left) k).symm.trans
      (cavity_extra_replica_identity_fin (ν n ω) (fun x => w n (ω, x))
        (fun σ => F n (ω, σ)) ((hw n).comp measurable_prodMk_left)
        ((hF n).comp measurable_prodMk_left) k)
    have hq n ω := (cavity_extra_replica_identity (ρ n ω) (fun x => v n (ω, x))
      (fun σ => J n (ω, σ)) ((hv n).comp measurable_prodMk_left)
      ((hJ n).comp measurable_prodMk_left) k).symm.trans
      (cavity_extra_replica_identity_fin (ρ n ω) (fun x => v n (ω, x))
        (fun σ => J n (ω, σ)) ((hv n).comp measurable_prodMk_left)
        ((hJ n).comp measurable_prodMk_left) k)
    simpa only [hp, hq] using hmom k

end InvariantIsing

end

end OAI
