import OAI.Analysis.CoulombTransport.BranchCoupling
import OAI.Analysis.CoulombTransport.CouplingSupport
import OAI.Analysis.CoulombTransport.ContactObstruction
import OAI.Analysis.CoulombTransport.CertificateAttainment
import OAI.Analysis.CoulombTransport.SplittingConstruction

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- The four-map marginal is the generic finite split measure, with central
weight `1/3` and four equal outer weights `1/6`. -/
lemma branchMarginal_eq_splitMeasure (nu : Measure E3) (H : Fin 4 → E3 → E3) :
    branchMarginal nu (H 0) (H 1) (H 2) (H 3) =
      Splitting.splitMeasure nu (1 / 3) (fun _ : Fin 4 => 1 / 6) H := by
  simp [branchMarginal, Splitting.splitMeasure, Fin.sum_univ_succ, smul_add, add_assoc]

/-- Support of the central measure and its four images gives support of the
five-component marginal. -/
lemma ae_branchMarginal_mem (nu : Measure E3) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) {B U : Set E3}
    (hU : MeasurableSet U) (hfull : ∀ᵐ x ∂nu, x ∈ B)
    (hBU : B ⊆ U) (hHU : ∀ i, H i '' B ⊆ U) :
    ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U := by
  have hcentral : ∀ᵐ x ∂nu, x ∈ U := hfull.mono fun _ hx => hBU hx
  have houter : ∀ i, ∀ᵐ x ∂Measure.map (H i) nu, x ∈ U := by
    intro i
    apply (ae_map_iff (hH i).aemeasurable hU).mpr
    exact hfull.mono fun x hx => hHU i ⟨x, hx, rfl⟩
  unfold branchMarginal
  apply ae_add_measure_iff.mpr
  refine ⟨Measure.ae_smul_measure hcentral _, Measure.ae_smul_measure ?_ _⟩
  exact ae_add_measure_iff.mpr
    ⟨ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨houter 0, houter 1⟩, houter 2⟩,
      houter 3⟩

private lemma coulombCost_cycle_assembly (x y z : E3) :
    coulombCost (y, (z, x)) = coulombCost (x, (y, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance]
  rw [norm_sub_rev y x, norm_sub_rev z x]
  ac_rfl

private lemma triplePotential_cycle_assembly (p : E3 → ℝ≥0∞) (x y z : E3) :
    triplePotential p (y, (z, x)) = triplePotential p (x, (y, z)) := by
  simp only [triplePotential, tripleFst, tripleSnd, tripleThd]
  ac_rfl

theorem hasCoulombCounterexample_of_branches
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
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C)
    (hselect : ∀ x y z : E3, x ∈ B → y ∈ U → z ∈ U →
      triplePotential p (x, (y, z)) = coulombCost (x, (y, z)) + C →
      ∃ i, y = H i x) :
    HasCoulombCounterexample rho := by
  let mu := branchMarginal nu (H 0) (H 1) (H 2) (H 3)
  let pi0 := branchCoupling nu (H 0) (H 1) (H 2) (H 3)
  have : IsProbabilityMeasure mu :=
    isProbabilityMeasure_branchMarginal nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hpi0 : IsThreeCoupling mu pi0 :=
    isThreeCoupling_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hmuU : ∀ᵐ x ∂mu, x ∈ U := ae_branchMarginal_mem nu hH hU hfull hBU hHU
  have hboundall : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, triplePotential p t ≤ coulombCost t + C := by
    intro pi hpi
    exact hpi.ae_of_support_certificate hU hmuU hbound
  have hcontact0 : ∀ᵐ t ∂pi0, triplePotential p t = coulombCost t + C := by
    apply ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
      (measurableSet_eq_fun (measurable_triplePotential hp)
        (measurable_coulombCost.add measurable_const))
    · intro x y z hxyz
      change triplePotential p (y, (z, x)) = coulombCost (y, (z, x)) + C
      rw [triplePotential_cycle_assembly, coulombCost_cycle_assembly]
      exact hxyz
    · exact hcontact01
    · exact hcontact23
  obtain ⟨hattained, hfinite⟩ :=
    kantorovichAttained_of_certificate hpi0 hp hpfinite hC hboundall hcontact0
  have hnu : nu ≪ mu := by
    change nu ≪ branchMarginal nu (H 0) (H 1) (H 2) (H 3)
    rw [branchMarginal_eq_splitMeasure]
    exact Splitting.absolutelyContinuous_splitMeasure nu (1 / 3) (fun _ : Fin 4 => 1 / 6) H
      (by norm_num)
  have hno : NoMongeOptimizer mu := by
    apply noMongeOptimizer_of_selection_obstruction mu nu hnu hfull
      (Contact := fun t => tripleSnd t ∈ U ∧ tripleThd t ∈ U ∧
        triplePotential p t = coulombCost t + C)
      (Select := fun x y => ∃ i, y = H i x)
    · intro pi hpi hopt
      have heq := certificate_contact_of_optimal hpi0 hpi hp hpfinite hC
        measurable_coulombCost hboundall hcontact0 hopt
      filter_upwards [hpi.ae_coordinates hmuU, heq] with t ht heq
      exact ⟨ht.2.1, ht.2.2, heq⟩
    · intro x y z hx ht
      exact hselect x y z hx ht.1 ht.2.1 ht.2.2
    · intro T hT hselection
      have hbad := Splitting.no_preserving_splitMeasure_selection
        (H := H) (c := (1 / 3 : ℝ≥0∞)) (d := (1 / 6 : ℝ≥0∞))
        (by simp : nu Set.univ ≠ 0) hB hfull hH hInj himage hCentral hPair
        (by norm_num)
      apply hbad
      refine ⟨T, hT.1, ?_, hselection⟩
      simpa only [← branchMarginal_eq_splitMeasure] using hT.2
  change IsSmoothCompactProbabilityDensity rho ∧
    IsProbabilityMeasure (densityMeasure rho) ∧ kantorovichValue (densityMeasure rho) < ⊤ ∧
    KantorovichAttained (densityMeasure rho) ∧ NoMongeOptimizer (densityMeasure rho)
  rw [hdensity]
  exact ⟨hrho, inferInstanceAs (IsProbabilityMeasure mu), hfinite, hattained, hno⟩

/-- The concrete six-graph coupling is itself the finite optimizer. This
exposes the witness used by the counterexample assembly to the separated
support approximation argument. -/
theorem branchCoupling_optimal_of_certificate
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
  have hpi0 := isThreeCoupling_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
  apply certificate_optimality hpi0 hp hpfinite hC
  · intro pi hpi
    exact hpi.ae_of_support_certificate hU hmuU hbound
  · apply ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
      (measurableSet_eq_fun (measurable_triplePotential hp)
        (measurable_coulombCost.add measurable_const))
    · intro x y z hxyz
      change triplePotential p (y, (z, x)) = coulombCost (y, (z, x)) + C
      rw [triplePotential_cycle_assembly, coulombCost_cycle_assembly]
      exact hxyz
    · exact hcontact01
    · exact hcontact23

end Problem356

end

end OAI
