import OAI.Probability.FreeIsing.Ising.CanonicalArtanhIdentification

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation PosteriorCompensatorStopping ArtanhMartingaleFormula

lemma denseRange_positive_rat_toNNReal :
    DenseRange (fun q : {q : ℚ // 0 < q} => (q.1 : ℝ).toNNReal) := by
  apply dense_of_exists_between
  intro a b hab
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn (show (a : ℝ) < (b : ℝ) from hab)
  have hqR : (0 : ℝ) < q := lt_of_le_of_lt a.coe_nonneg haq
  have hq : (0 : ℚ) < q := by exact_mod_cast hqR
  refine ⟨(q : ℝ).toNNReal, ⟨⟨q, hq⟩, rfl⟩, ?_, ?_⟩
  · exact_mod_cast (show (a : ℝ) < ((q : ℝ).toNNReal : ℝ) by
      simpa only [Real.coe_toNNReal _ hqR.le] using haq)
  · exact_mod_cast (show ((q : ℝ).toNNReal : ℝ) < (b : ℝ) by
      simpa only [Real.coe_toNNReal _ hqR.le] using hqb)

theorem canonical_artanh_eq_all_of_meanSquare_limits_dense
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d)
    (n : ℕ) {ι : Type*} [Countable ι] (e : ι → ℝ≥0) (he : DenseRange e)
    {J : ℝ≥0 → Paths d → ℝ}
    (hJ : ∀ i, MemLp (J (e i)) 2 (observationLaw μ))
    (hcJ : ∀ᵐ x ∂observationLaw μ, Continuous (fun T => J T x))
    (hlim : ∀ i, let N := stoppedProcess (continuousPosterior beta v) (canonicalPosteriorExit beta v n)
      Tendsto (fun k => ∫ x,
        (BrownianGrid.uniformSum N (fun t x => firstWeight (N t x)) (e i) k x - J (e i) x) ^ 2
          ∂observationLaw μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂observationLaw μ, ∀ T,
      stoppedProcess (continuousField beta v) (canonicalPosteriorExit beta v n) T x =
        J T x + stoppedProcess (nnrealTimePrimitive (canonicalResponseDrift beta v))
          (canonicalPosteriorExit beta v n) T x := by
  have hcA := canonicalResponseDrift_primitive_continuous hμ hb v
  have hleft := (continuousField_modification hd hμ hb hcrit v).1.mono
    (fun x hx => StoppedTimePrimitive.continuous_stoppedProcess hx (canonicalPosteriorExit beta v n))
  have hright := (hcJ.and hcA).mono (fun x hx => hx.1.add
    (StoppedTimePrimitive.continuous_stoppedProcess hx.2 (canonicalPosteriorExit beta v n)))
  have h := ae_eq_of_dense_evaluations e he hleft hright
    (fun i => canonical_artanh_eq_of_meanSquare_limit hd hμ hb hcrit v n (e i) (hJ i) (hlim i))
  exact h.mono (fun x hx T => congrFun hx T)

end Problem367.IsingObservationFactor

end

end OAI
