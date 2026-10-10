import OAI.Analysis.CoulombTransport.CounterexampleAssembly
import OAI.Analysis.CoulombTransport.Calibration

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

private lemma coulombCost_pos_realAssembly (t : Triple) : 0 < coulombCost t := by
  have hpos : 0 < invDistance (tripleFst t) (tripleSnd t) :=
    ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
  unfold coulombCost
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hpos zero_le) zero_le

/-- For the strictly positive Coulomb cost, the shifted and signed contact
conditions are equivalent; no nonnegativity assumption on the signed sum is
needed. -/
lemma triplePotential_shifted_contact_iff {u : E3 → ℝ} {M : ℝ} {t : Triple}
    (hM : 0 ≤ M)
    (h1 : -M ≤ u (tripleFst t)) (h2 : -M ≤ u (tripleSnd t))
    (h3 : -M ≤ u (tripleThd t)) :
    (triplePotential (shiftedPotential u M) t =
      coulombCost t + ENNReal.ofReal (3 * M)) ↔
    ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) =
      coulombCost t :=
  shifted_three_eq_iff_of_pos h1 h2 h3 hM (coulombCost_pos_realAssembly t)

theorem hasCoulombCounterexample_of_real_branches
    (rho : E3 → ℝ) (hrho : IsSmoothCompactProbabilityDensity rho)
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    (hdensity : densityMeasure rho = branchMarginal nu (H 0) (H 1) (H 2) (H 3))
    {B U : Set E3} (hB : MeasurableSet B) (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B → MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 0 x) + u (H 1 x)) = coulombCost (x, (H 0 x, H 1 x)))
    (hcontact23 : ∀ᵐ x ∂nu,
      ENNReal.ofReal (u x + u (H 2 x) + u (H 3 x)) = coulombCost (x, (H 2 x, H 3 x)))
    (hselect : ∀ x y z : E3, x ∈ B → y ∈ U → z ∈ U →
      ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
      ∃ i, y = H i x) :
    HasCoulombCounterexample rho := by
  let mu := branchMarginal nu (H 0) (H 1) (H 2) (H 3)
  have : IsProbabilityMeasure mu :=
    isProbabilityMeasure_branchMarginal nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hmuU : ∀ᵐ x ∂mu, x ∈ U := ae_branchMarginal_mem nu hH hU hfull hBU hHU
  have hfinite : (∫⁻ x, shiftedPotential u M x ∂mu) ≠ ⊤ :=
    (lintegral_shiftedPotential_lt_top_of_ae_le
      (M := M) (hmuU.mono fun x hx => (hubound x hx).2)).ne
  apply hasCoulombCounterexample_of_branches rho hrho nu H hH hdensity
    hB hU hfull hBU hHU hInj himage hCentral hPair
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
  · intro x y z hx hy hz heq
    apply hselect x y z hx hy hz
    exact (triplePotential_shifted_contact_iff hM
      (hubound x (hBU hx)).1 (hubound y hy).1 (hubound z hz).1).mp heq

end Problem356

end

end OAI
