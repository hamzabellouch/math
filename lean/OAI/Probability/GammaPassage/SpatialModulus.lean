import OAI.Probability.GammaPassage.CoordinateTails
import OAI.Probability.GammaPassage.EnvironmentScaling
import OAI.Probability.FirstPassage.SpatialModulus

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory PlanarFPP Finset Filter Set
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Failure of the Gamma allowance for some actual coordinate path in the box. -/
def gammaBadConnections (shape rate : ℝ) (τ : Edge → Ω → ℝ)
    (ε : ℝ) (n : ℕ) : Set Ω :=
  ⋃ pq ∈ (latticeBox n) ×ˢ (latticeBox n),
    {ω | coordinateAllowance shape rate * (latticeDistance pq.1 pq.2 : ℝ) + ε * n ≤
      pathCost (fun e => τ e ω) pq.1 (coordinatePath pq.1 pq.2)}

/-- Finite union bound over all ordered pairs, without independence of path events. -/
theorem GammaEnvironment.gammaBadConnections_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (ε : ℝ) (n : ℕ) :
    P.real (gammaBadConnections shape rate τ ε n) ≤
      (2 * (n : ℝ) + 1) ^ 4 * (2 * Real.exp (-(rate / 4) * (ε * n))) := by
  let := h.probability
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _pq ∈ (latticeBox n) ×ˢ (latticeBox n),
        2 * Real.exp (-(rate / 4) * (ε * n)) :=
      sum_le_sum (fun pq _ => h.costly_coordinatePath_probability_real hs hr pq.1 pq.2 (ε * n))
    _ = _ := by simp [latticeBox_card]; ring

/-- The only summability requirement is positive rate times positive epsilon. -/
theorem summable_gamma_box_connection_bound {rate ε : ℝ}
    (hr : 0 < rate) (hε : 0 < ε) :
    Summable (fun n : ℕ =>
      (2 * (n : ℝ) + 1) ^ 4 * (2 * Real.exp (-(rate / 4) * (ε * n)))) := by
  apply (PlanarFPP.summable_box_connection_bound (mul_pos hr hε)).congr
  intro n
  have he : -(rate * ε) * (n : ℝ) / 4 = -(rate / 4) * (ε * n) := by ring
  rw [he]

/-- For each fixed positive epsilon, almost surely all sufficiently large boxes
have the connection estimate for every pair, even pairs selected from the environment. -/
theorem GammaEnvironment.ae_eventually_coordinate_connections
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      pathCost (fun e => τ e ω) p (coordinatePath p q) <
        coordinateAllowance shape rate * (latticeDistance p q : ℝ) + ε * n := by
  let := h.probability
  have hsumm : Summable (fun n => P.real (gammaBadConnections shape rate τ ε n)) :=
    (summable_gamma_box_connection_bound hr hε).of_nonneg_of_le
      (fun _ => measureReal_nonneg) (h.gammaBadConnections_probability hs hr ε)
  have hfinite : (∑' n, P (gammaBadConnections shape rate τ ε n)) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hsumm.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with n hn
  intro p hp q hq
  by_contra hc
  apply hn
  exact mem_iUnion₂.mpr ⟨(p, q), mem_product.mpr ⟨hp, hq⟩, le_of_not_gt hc⟩

/-- The same modulus for the actual infimum passage time. Fixed epsilon precedes
AE; simultaneous control concerns finite-box pairs, not an uncountable family of epsilons. -/
theorem GammaEnvironment.ae_eventually_passageTime_connections
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q <
        coordinateAllowance shape rate * (latticeDistance p q : ℝ) + ε * n := by
  filter_upwards [h.ae_positive_edges, h.ae_eventually_coordinate_connections hs hr hε]
    with ω hp hc
  filter_upwards [hc] with n hn
  intro p hp' q hq'
  exact (passageTime_le_cost _ (fun e => (hp e).le) p q
    (coordinatePath p q) (coordinatePath_endpoint p q)).trans_lt (hn p hp' q hq')

end GammaFPP

end OAI
