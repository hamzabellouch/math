import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainProducts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput

namespace OAI

/-! # Polynomial volume upper bounds for nilpotent metric balls

Linear bounded-step chains, the finite Dynkin formula and exponential Haar
coordinates give the only volume estimate used by boundary averaging.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule MeasureTheory MeasureTheory.Measure Metric
open scoped Manifold ENNReal

/-- A finite sequence with controlled vertices and steps gives the inductive
chain used by the coordinate estimates. -/
theorem boundedHeightChain_of_sequence
    {X W : Type*} [MetricSpace X] [NormedAddCommGroup W]
    (π : X → W) (p : ℕ → X) {L M : ℝ} (n : ℕ)
    (hheight : ∀ i ≤ n, ‖π (p i)‖ ≤ M)
    (hstep : ∀ i < n, dist (p i) (p (i + 1)) ≤ L) :
    BoundedHeightChain π L M n (p 0) (p n) := by
  induction n with
  | zero => exact .nil _ (hheight 0 le_rfl)
  | succ n ih =>
    exact (ih (fun i hi => hheight i (hi.trans (Nat.le_succ n)))
      (fun i hi => hstep i (hi.trans (Nat.lt_succ_self n)))).snoc
      (hheight _ le_rfl) (hstep n (Nat.lt_succ_self n))

variable {G E : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Every large metric ball is contained in one polynomially growing
exponential coordinate cube. -/
theorem exists_polynomial_ball_coordinate_bound
    (chains : LinearMetricChains G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hzero : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    {J : Type*} [Fintype J] (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 1 ≤ R →
      ball (1 : G) R ⊆ exponentialCoordinateBox Exp b (D * R ^ c) := by
  obtain ⟨A, hA, hcoord⟩ := exists_polynomial_chain_coordinate_bound (W := ℝ)
    dynkin Exp hExp chart hchart hzero b chains.step
  have hs := chains.slope_nonneg
  have he := chains.error_nonneg
  let D := A * (1 + chains.slope + chains.error) ^ c
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro R hR g hg
  obtain ⟨n, p, hp0, hpn, hn, hp⟩ := chains.chain 1 g
  have hchain := boundedHeightChain_of_sequence (fun _ : G => (0 : ℝ)) p (M := 0) n
    (by intro i hi; simp) hp
  rw [hp0, hpn] at hchain
  obtain ⟨v, hv, hbound⟩ := hcoord (fun _ : G => (0 : ℝ)) 0 n 1 g hchain
  refine ⟨v, by simpa only [inv_one, one_mul] using hv, hbound.trans ?_⟩
  have hdist : dist (1 : G) g ≤ R := by simpa only [mem_ball, dist_comm] using hg.le
  have hn' : (n : ℝ) ≤ chains.slope * R + chains.error :=
    hn.trans (add_le_add (mul_le_mul_of_nonneg_left hdist chains.slope_nonneg) le_rfl)
  have hlen : 1 + (n : ℝ) ≤ (1 + chains.slope + chains.error) * R := by
    nlinarith [chains.error_nonneg, mul_nonneg chains.error_nonneg (sub_nonneg.mpr hR)]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + n) hlen c
  have hh := mul_le_mul_of_nonneg_left hpow hA
  simpa only [mul_pow, D, mul_assoc] using hh

variable [SimplyConnectedSpace G]

/-- The concrete exponential Haar measure has polynomial ball-volume upper
growth. The exponent need not be the sharp homogeneous dimension. -/
theorem exists_haar_polynomial_ball_volume
    (chains : LinearMetricChains G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ∃ (μ : Measure G) (C : ℝ) (d : ℕ), μ.IsHaarMeasure ∧ 0 ≤ C ∧
      ∀ R : ℝ, 1 ≤ R → (μ (ball 1 R)).toReal ≤ C * R ^ d := by
  let b := Module.finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  obtain ⟨chart, μ, hchart, hμ, hvol⟩ := exists_haar_exponential_cube_volume haar Exp hExp hnil b
  let := hμ
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ
    (GroupLieAlgebra (𝓘(ℝ, E)) G) (GroupLieAlgebra (𝓘(ℝ, E)) G)).mp hnil
  obtain ⟨D, hD, hball⟩ := exists_polynomial_ball_coordinate_bound chains dynkin Exp hExp
    chart hchart hc b
  let n := finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  refine ⟨μ, (2 * D) ^ n, c * n, hμ, by positivity, ?_⟩
  intro R hR
  have hDR : 0 ≤ D * R ^ c := mul_nonneg hD (pow_nonneg (by linarith) _)
  have hmass := measure_mono (μ := μ) (hball R hR)
  rw [hvol _ hDR] at hmass
  have hfinite : ENNReal.ofReal (2 * (D * R ^ c)) ^ n ≠ ∞ := by finiteness
  have hh := ENNReal.toReal_mono hfinite hmass
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hDR)] at hh
  convert hh using 1
  simp only [mul_pow, pow_mul]
  ring

/-- Haar normalization only changes the polynomial coefficient. -/
theorem haar_polynomial_ball_volume
    [SecondCountableTopology G]
    (chains : LinearMetricChains G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
      ∀ R : ℝ, 1 ≤ R → (μ (ball 1 R)).toReal ≤ C * R ^ d := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨ν, C, d, hν, hC, hvol⟩ := exists_haar_polynomial_ball_volume chains dynkin haar Exp hExp hnil
  let := hν
  have heq := isMulLeftInvariant_eq_smul μ ν
  refine ⟨(haarScalarFactor μ ν : ℝ) * C, mul_nonneg (NNReal.coe_nonneg _) hC, d, ?_⟩
  intro R hR
  have hm := congrArg (fun τ : Measure G => τ (ball 1 R)) heq
  change μ (ball 1 R) = (haarScalarFactor μ ν) • ν (ball 1 R) at hm
  rw [hm]
  change ((haarScalarFactor μ ν : ℝ≥0∞) * ν (ball 1 R)).toReal ≤ _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  exact (mul_le_mul_of_nonneg_left (hvol R hR) (NNReal.coe_nonneg _)).trans_eq (by ring)

end PolycyclicRecognition

end

end OAI
