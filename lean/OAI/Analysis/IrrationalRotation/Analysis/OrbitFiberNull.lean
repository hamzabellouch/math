import OAI.Analysis.IrrationalRotation.Analysis.OrbitMeasurable
import OAI.Analysis.IrrationalRotation.Spectral.PolarStructure

namespace OAI

open Set Filter Function MeasureTheory

namespace Invariant233

variable {X Y : Type*} [m : MeasurableSpace X] [MeasurableSpace Y]
  [Nonempty Y] [MeasurableSpace.CountablySeparated Y] [MeasurableSingletonClass Y]
  {μ : Measure X} [IsFiniteMeasure μ]

theorem orbit_joint_fiber_measure_zero
    (σ : Equiv.Perm X) (hσ : Measurable σ) (hinv : Measurable σ.symm)
    (htotal : ∀ n : ℕ, 0 < n → Ergodic (σ : X → X)^[n] μ)
    {f : X → Y} (hf : Measurable f)
    (hnonconstant : ¬ ∃ c : Y, f =ᵐ[μ] Function.const X c)
    (z : ℤ → Y) :
    μ {x | ∀ n : ℤ, f ((σ ^ n) x) = z n} = 0 := by
  let F : X → (ℤ → Y) := fun x n => f ((σ ^ n) x)
  have hspace : MeasurableSpace.comap F inferInstance = orbitMeasurableSpace σ f := by
    exact MeasurableSpace.comap_process_pi (fun n x => f ((σ ^ n) x))
  have hs : @MeasurableSet X (orbitMeasurableSpace σ f) (F ⁻¹' {z}) := by
    rw [← hspace]
    exact ⟨{z}, measurableSet_singleton z, rfl⟩
  have hnull : μ (F ⁻¹' {z}) = 0 := by
    by_contra hpos
    obtain ⟨t, ht, hsub, htpos, hdiff⟩ :=
      orbitMeasurableSpace_atomless σ hσ hinv htotal hf hnonconstant hs hpos
    have ht' : MeasurableSet[MeasurableSpace.comap F inferInstance] t := by
      rwa [hspace]
    rcases InvariantProjection.PolarStructure.fiber_is_atom_in_comap F z ht' hsub with
      hzero | hfull
    · exact htpos (by simp [hzero])
    · exact hdiff (by simp [hfull])
  have heq : {x | ∀ n : ℤ, f ((σ ^ n) x) = z n} = F ⁻¹' {z} := by
    ext x
    exact (funext_iff : F x = z ↔ ∀ n, F x n = z n).symm
  rwa [heq]

theorem orbit_joint_fiber_measure_zero_of_negInfiniteLogIntegral
    (σ : Equiv.Perm X) (hσ : Measurable σ) (hinv : Measurable σ.symm)
    (htotal : ∀ n : ℕ, 0 < n → Ergodic (σ : X → X)^[n] μ)
    {f : X → ℝ} (hf : Measurable f)
    (hnonzero : ∀ᵐ x ∂μ, f x ≠ 0) (hlog : HasNegInfiniteLogIntegral μ f)
    (z : ℤ → ℝ) :
    μ {x | ∀ n : ℤ, f ((σ ^ n) x) = z n} = 0 :=
  orbit_joint_fiber_measure_zero σ hσ hinv htotal hf
    (not_ae_constant_of_negInfiniteLogIntegral hnonzero hlog) z

omit [IsFiniteMeasure μ] in

theorem ae_zero_of_null_joint_fibers
    {I E : Type*} [Countable I] [AddCommGroup E] [Module ℂ E]
    {g : I → X → ℂ}
    (hnull : ∀ z : I → ℂ, μ {x | ∀ i, g i x = z i} = 0)
    {v : X → E} (z : I → ℂ)
    (hv : ∀ i, ∀ᵐ x ∂μ, g i x • v x = z i • v x) :
    v =ᵐ[μ] 0 := by
  have havoid := measure_eq_zero_iff_ae_notMem.mp (hnull z)
  filter_upwards [ae_all_iff.mpr hv, havoid] with x hx hnot
  by_contra hne
  apply hnot
  intro i
  exact smul_left_injective ℂ hne (hx i)

theorem ae_zero_of_orbit_joint_eigenrelation
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (σ : Equiv.Perm X) (hσ : Measurable σ) (hinv : Measurable σ.symm)
    (htotal : ∀ n : ℕ, 0 < n → Ergodic (σ : X → X)^[n] μ)
    {f : X → ℂ} (hf : Measurable f)
    (hnonconstant : ¬ ∃ c : ℂ, f =ᵐ[μ] Function.const X c)
    {v : X → E} (z : ℤ → ℂ)
    (hv : ∀ n, ∀ᵐ x ∂μ, f ((σ ^ n) x) • v x = z n • v x) :
    v =ᵐ[μ] 0 :=
  ae_zero_of_null_joint_fibers
    (orbit_joint_fiber_measure_zero σ hσ hinv htotal hf hnonconstant) z hv

end Invariant233

end OAI
