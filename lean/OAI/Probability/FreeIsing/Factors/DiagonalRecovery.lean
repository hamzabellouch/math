import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Problem367

theorem exists_eq_dirac_of_selfProd_ae_eq
    {X : Type*} [MeasurableSpace X] (nu : Measure X)
    [IsProbabilityMeasure nu]
    (h : ∀ᵐ p ∂nu.prod nu, p.1 = p.2) :
    ∃ x : X, nu = Measure.dirac x := by
  obtain ⟨x, hx⟩ := (Measure.ae_ae_of_ae_prod h).exists
  refine ⟨x, ?_⟩
  have hconst : (fun y : X => y) =ᵐ[nu] (fun _ => x) := by
    filter_upwards [hx] with y hy using hy.symm
  simpa using Measure.map_congr hconst

theorem exists_measurable_dirac_of_forall
    {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    (kappa : Kernel W X)
    (h : ∀ w, ∃ x : X, kappa w = Measure.dirac x) :
    ∃ F : W → X, Measurable F ∧ ∀ w, kappa w = Measure.dirac (F w) := by
  choose F hF using h
  refine ⟨F, ?_, hF⟩
  intro s hs
  have heq : F ⁻¹' s = (fun w => kappa w s) ⁻¹' {1} := by
    ext w
    simp only [mem_preimage, mem_singleton_iff, hF w, Measure.dirac_apply' _ hs]
    exact (indicator_eq_one_iff_mem ENNReal).symm
  rw [heq]
  exact kappa.measurable_coe hs (measurableSet_singleton 1)

theorem exists_measurable_dirac_of_selfProd_ae_eq
    {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableEq X] [Nonempty X]
    (mu : Measure W) (kappa : Kernel W X) [IsMarkovKernel kappa]
    (h : ∀ᵐ w ∂mu, ∀ᵐ p ∂(kappa w).prod (kappa w), p.1 = p.2) :
    ∃ F : W → X, Measurable F ∧ ∀ᵐ w ∂mu, kappa w = Measure.dirac (F w) := by
  classical
  let good : Set W := {w | (kappa ×ₖ kappa) w (diagonal X)ᶜ = 0}
  have hgood : MeasurableSet good :=
    ((kappa ×ₖ kappa).measurable_coe measurableSet_diagonal.compl)
      (measurableSet_singleton 0)
  have hgood_ae : ∀ᵐ w ∂mu, w ∈ good := by
    filter_upwards [h] with w hw
    change (kappa ×ₖ kappa) w (diagonal X)ᶜ = 0
    rw [Kernel.prod_apply]
    exact hw
  let base : X := Classical.choice inferInstance
  let modified := Kernel.piecewise hgood kappa
    (Kernel.deterministic (fun _ : W => base) measurable_const)
  have hmodified : ∀ w, ∃ x : X, modified w = Measure.dirac x := by
    intro w
    by_cases hw : w ∈ good
    · have hdiag : ∀ᵐ p ∂(kappa w).prod (kappa w), p.1 = p.2 := by
        change (kappa w).prod (kappa w) {p | ¬p.1 = p.2} = 0
        simpa only [good, mem_ofPred_eq, Kernel.prod_apply, diagonal, compl_ofPred] using hw
      obtain ⟨x, hx⟩ := exists_eq_dirac_of_selfProd_ae_eq (kappa w) hdiag
      exact ⟨x, by simpa [modified, Kernel.piecewise_apply, Kernel.deterministic_apply, hw] using hx⟩
    · exact ⟨base, by simp [modified, Kernel.piecewise_apply, Kernel.deterministic_apply, hw]⟩
  obtain ⟨F, hF, hdirac⟩ := exists_measurable_dirac_of_forall modified hmodified
  refine ⟨F, hF, ?_⟩
  filter_upwards [hgood_ae] with w hw
  simpa [modified, Kernel.piecewise_apply, Kernel.deterministic_apply, hw] using hdirac w

theorem ae_eq_recovery_of_ae_dirac
    {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableEq X] (mu : Measure W) (kappa : Kernel W X)
    {F : W → X} (hF : Measurable F)
    (h : ∀ᵐ w ∂mu, kappa w = Measure.dirac (F w)) :
    ∀ᵐ p ∂mu ⊗ₘ kappa, p.2 = F p.1 := by
  apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun measurable_snd (hF.comp measurable_fst))
  filter_upwards [h] with w hw
  rw [hw]
  simp

theorem exists_measurable_recovery_of_conditionalCopies
    {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    [MeasurableEq X] [Nonempty X]
    (mu : Measure W) [SFinite mu] (kappa : Kernel W X) [IsMarkovKernel kappa]
    (h : ∀ᵐ p ∂mu ⊗ₘ (kappa ×ₖ kappa), p.2.1 = p.2.2) :
    ∃ F : W → X, Measurable F ∧
      (∀ᵐ w ∂mu, kappa w = Measure.dirac (F w)) ∧
      ∀ᵐ p ∂mu ⊗ₘ kappa, p.2 = F p.1 := by
  have hcopies : ∀ᵐ w ∂mu, ∀ᵐ p ∂(kappa w).prod (kappa w), p.1 = p.2 := by
    simpa only [Kernel.prod_apply] using Measure.ae_ae_of_ae_compProd h
  obtain ⟨F, hF, hdirac⟩ := exists_measurable_dirac_of_selfProd_ae_eq mu kappa hcopies
  exact ⟨F, hF, hdirac, ae_eq_recovery_of_ae_dirac mu kappa hF hdirac⟩

end Problem367

end

end OAI
