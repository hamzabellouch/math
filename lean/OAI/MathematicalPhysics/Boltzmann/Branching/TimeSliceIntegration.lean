import OAI.MathematicalPhysics.Boltzmann.Branching.HalfGaussianMoment

namespace OAI

/-! # From almost-everywhere positive-time slices to spacetime bounds -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Compactness

theorem ae_interval_of_slices {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {T : ℝ} {P : ℝ × X → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ t ∈ Ioc (0:ℝ) T, ∀ᵐ x ∂ν, P (t,x)) :
    ∀ᵐ z ∂(volume.restrict (Icc (0:ℝ) T)).prod ν, P z := by
  apply (Measure.ae_prod_iff_ae_ae hP).mpr
  have hn : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hn] with t ht htn
  exact h t ⟨lt_of_le_of_ne ht.1 (Ne.symm htn),ht.2⟩


theorem measurableSet_ae_fiber {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] {P : X × Y → Prop} (hP : MeasurableSet {z | P z}) :
    MeasurableSet {x | ∀ᵐ y ∂ν, P (x,y)} := by
  have hm : Measurable (fun x => ν (Prod.mk x ⁻¹' {z | ¬P z})) :=
    measurable_measure_prodMk_left hP.compl
  have he : {x | ∀ᵐ y ∂ν, P (x,y)} = {x | ν (Prod.mk x ⁻¹' {z | ¬P z}) = 0} := by
    ext x
    change (∀ᵐ y ∂ν, P (x,y)) ↔ _
    rw [ae_iff]
    rfl
  rw [he]
  exact measurableSet_eq_fun hm measurable_const

theorem ae_interval_nested_of_slices {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure X} {ρ : Measure Y} [SFinite ν] [SFinite ρ]
    {T : ℝ} {P : (ℝ × X) × Y → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ t ∈ Ioc (0:ℝ) T, ∀ᵐ x ∂ν, ∀ᵐ y ∂ρ, P ((t,x),y)) :
    ∀ᵐ u ∂(volume.restrict (Icc (0:ℝ) T)).prod ν, ∀ᵐ y ∂ρ, P (u,y) :=
  ae_interval_of_slices (measurableSet_ae_fiber hP) h

end BoltzmannNonuniqueness.Compactness

namespace BoltzmannNonuniqueness.VelocityMoment

theorem measurable_moment {X : Type*} [MeasurableSpace X] {f : X × Velocity → ℝ}
    (hf : Measurable f) : Measurable (fun x => moment (fun v => f (x,v))) := by
  have hm : Measurable (fun z : X × Velocity => ENNReal.ofReal (weight z.2*f z)) := by
    unfold weight
    fun_prop
  exact hm.lintegral_prod_right'

end BoltzmannNonuniqueness.VelocityMoment

end

end OAI
