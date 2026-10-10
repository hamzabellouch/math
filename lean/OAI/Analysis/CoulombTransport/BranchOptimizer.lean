import OAI.Analysis.CoulombTransport.RealCounterexampleAssembly

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

private lemma branchOptimizer_cost_cycle (x y z : E3) :
    coulombCost (y, (z, x)) = coulombCost (x, (y, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance]
  rw [norm_sub_rev y x, norm_sub_rev z x]
  ac_rfl

private lemma branchOptimizer_potential_cycle (p : E3 → ℝ≥0∞) (x y z : E3) :
    triplePotential p (y, (z, x)) = triplePotential p (x, (y, z)) := by
  simp only [triplePotential, tripleFst, tripleSnd, tripleThd]
  ac_rfl

/-- The explicit six-graph branch coupling is itself a finite optimizer.
This preserves the identity of the optimizer, unlike an existential attainment
statement, so its geometric separation can be used in Monge approximation. -/
theorem branchCoupling_optimality_of_shifted_certificate
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    {U : Set E3} (hU : MeasurableSet U)
    (hmuU : ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) =
        kantorovichValue (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ∧
      (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by
  apply certificate_optimality
    (isThreeCoupling_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)) hp hpfinite hC
  · intro pi hpi
    exact hpi.ae_of_support_certificate hU hmuU hbound
  · apply ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
      (measurableSet_eq_fun (measurable_triplePotential hp)
        (measurable_coulombCost.add measurable_const))
    · intro x y z hxyz
      change triplePotential p (y, (z, x)) = coulombCost (y, (z, x)) + C
      rw [branchOptimizer_potential_cycle, branchOptimizer_cost_cycle]
      exact hxyz
    · exact hcontact01
    · exact hcontact23

/-- Signed-potential version of explicit branch optimizer certification.
The assumptions are a subset of the real counterexample assembly assumptions;
no density, injectivity, or nonattainment hypothesis is required. -/
theorem branchCoupling_optimality_of_real_certificate
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    {B U : Set E3} (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 0 x) + u (H 1 x)) = coulombCost (x, (H 0 x, H 1 x)))
    (hcontact23 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 2 x) + u (H 3 x)) = coulombCost (x, (H 2 x, H 3 x))) :
    (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) =
        kantorovichValue (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ∧
      (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) < ⊤ := by
  have : IsProbabilityMeasure (branchMarginal nu (H 0) (H 1) (H 2) (H 3)) :=
    isProbabilityMeasure_branchMarginal nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hmuU := ae_branchMarginal_mem nu hH hU hfull hBU hHU
  have hfinite : (∫⁻ x, shiftedPotential u M x
      ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤ :=
    (lintegral_shiftedPotential_lt_top_of_ae_le
      (M := M) (hmuU.mono fun x hx => (hubound x hx).2)).ne
  apply branchCoupling_optimality_of_shifted_certificate nu H hH hU hmuU
    (measurable_shiftedPotential hu M) hfinite ENNReal.ofReal_ne_top
  · intro t h1 h2 h3
    exact shiftedPotential_certificate (hubound _ h1).1 (hubound _ h2).1
      (hubound _ h3).1 (hbound t h1 h2 h3)
  · filter_upwards [hfull, hcontact01] with x hx heq
    apply (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1
      (hubound (H 0 x) (hHU 0 ⟨x, hx, rfl⟩)).1
      (hubound (H 1 x) (hHU 1 ⟨x, hx, rfl⟩)).1).mpr
    exact heq
  · filter_upwards [hfull, hcontact23] with x hx heq
    apply (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1
      (hubound (H 2 x) (hHU 2 ⟨x, hx, rfl⟩)).1
      (hubound (H 3 x) (hHU 3 ⟨x, hx, rfl⟩)).1).mpr
    exact heq

end Problem356

end

end OAI
