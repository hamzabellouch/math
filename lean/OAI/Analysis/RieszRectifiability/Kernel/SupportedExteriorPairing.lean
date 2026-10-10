import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.HeightPairingRegions

namespace OAI

/-!
# Supported exterior pairings

Support in a measurable subset allows the left factor of a product measure to be
restricted without changing integrability or the integral. These identities bound
the absolute renormalized pairing over a complement by its exterior integral when
the original set contains a ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem prod_restrict_left_subset {d : ℕ} (μ η : Measure (Ambient d))
    [SFinite μ] [SFinite η]
    (A s : Set (Ambient d)) (hA : MeasurableSet A) (hAs : A ⊆ s) :
    ((μ.restrict s).prod η).restrict (A ×ˢ univ) = (μ.restrict A).prod η := by
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_restrict hA, inter_eq_left.mpr hAs]

theorem integrable_prod_iff_of_left_support {d : ℕ} (μ η : Measure (Ambient d))
    [SFinite μ] [SFinite η]
    (A s : Set (Ambient d)) (hA : MeasurableSet A) (hAs : A ⊆ s)
    (F : Ambient d × Ambient d → ℝ) (hzero : ∀ q, q.1 ∉ A → F q = 0) :
    Integrable F ((μ.restrict s).prod η) ↔ Integrable F ((μ.restrict A).prod η) := by
  have hsupp : support F ⊆ A ×ˢ univ := by
    intro q hq
    refine ⟨?_, mem_univ _⟩
    by_contra h
    exact hq (hzero q h)
  have h := integrableOn_iff_integrable_of_support_subset
    (μ := (μ.restrict s).prod η) hsupp
  rw [IntegrableOn, prod_restrict_left_subset μ η A s hA hAs] at h
  exact h.symm

theorem integral_prod_eq_of_left_support {d : ℕ} (μ η : Measure (Ambient d))
    [SFinite μ] [SFinite η]
    (A s : Set (Ambient d)) (hA : MeasurableSet A) (hAs : A ⊆ s)
    (F : Ambient d × Ambient d → ℝ) (hzero : ∀ q, q.1 ∉ A → F q = 0) :
    (∫ q, F q ∂(μ.restrict s).prod η) = ∫ q, F q ∂(μ.restrict A).prod η := by
  have h : (∫ q in A ×ˢ univ, F q ∂(μ.restrict s).prod η) =
      ∫ q, F q ∂(μ.restrict s).prod η := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    apply hzero q
    intro h
    exact hq ⟨h, mem_univ _⟩
  rw [prod_restrict_left_subset μ η A s hA hAs] at h
  exact h.symm

theorem renormalized_pairing_complement_bound {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d) (R : ℝ)
    (A s : Set (Ambient d)) (hA : MeasurableSet A) (hAs : A ⊆ s)
    (hcontain : ball a R ⊆ s) (w φ : Ambient d → ℝ)
    (hφzero : ∀ x ∉ A, φ x = 0)
    (houter : Integrable (renormalizedNormalIntegrand m w φ a)
      ((μ.restrict A).prod (μ.restrict (closedExterior a R)))) :
    Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict s).prod (μ.restrict sᶜ)) ∧
      (∫ q, |renormalizedNormalIntegrand m w φ a q| ∂(μ.restrict s).prod (μ.restrict sᶜ)) ≤
        ∫ q, |renormalizedNormalIntegrand m w φ a q|
          ∂(μ.restrict A).prod (μ.restrict (closedExterior a R)) := by
  have hzero : ∀ q : Ambient d × Ambient d, q.1 ∉ A →
      renormalizedNormalIntegrand m w φ a q = 0 := by
    intro q hq
    simp only [renormalizedNormalIntegrand, hφzero q.1 hq, zero_mul]
  have hsub : sᶜ ⊆ closedExterior a R := by
    rw [closedExterior_eq_compl_ball]
    exact compl_subset_compl.mpr hcontain
  have hmeas : (μ.restrict A).prod (μ.restrict sᶜ) ≤
      (μ.restrict A).prod (μ.restrict (closedExterior a R)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact Measure.restrict_mono (Set.prod_mono subset_rfl hsub) le_rfl
  refine ⟨(integrable_prod_iff_of_left_support μ (μ.restrict sᶜ) A s hA hAs
    _ hzero).mpr (houter.mono_measure hmeas), ?_⟩
  rw [integral_prod_eq_of_left_support μ (μ.restrict sᶜ) A s hA hAs
    (fun q => |renormalizedNormalIntegrand m w φ a q|) (by
      intro q hq
      rw [hzero q hq, abs_zero])]
  exact integral_mono_measure hmeas (Eventually.of_forall fun _ => abs_nonneg _) houter.abs

end

end RieszRectifiability

end OAI
