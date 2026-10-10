import OAI.Analysis.IrrationalRotation.Analysis.OrbitMeasurable

namespace OAI

open Set Filter Function MeasureTheory

namespace Invariant233

variable {X Y : Type*} [m : MeasurableSpace X] [mY : MeasurableSpace Y]

omit m in

theorem orbitMeasurableSpace_eq_comap_tuple (σ : Equiv.Perm X) (f : X → Y) :
    orbitMeasurableSpace σ f =
      MeasurableSpace.comap (fun x => fun n : ℤ => f ((σ ^ n) x)) inferInstance := by
  exact (MeasurableSpace.comap_process_pi (fun n x => f ((σ ^ n) x))).symm

theorem measure_orbit_fiber_eq_zero
    [Nonempty Y] [MeasurableSpace.CountablySeparated Y] [MeasurableSingletonClass Y]
    {μ : Measure X} [IsFiniteMeasure μ]
    (σ : Equiv.Perm X) (hσ : Measurable σ) (hinv : Measurable σ.symm)
    (htotal : ∀ n : ℕ, 0 < n → Ergodic (σ : X → X)^[n] μ)
    {f : X → Y} (hf : Measurable f)
    (hnonconstant : ¬ ∃ c : Y, f =ᵐ[μ] Function.const X c)
    (v : ℤ → Y) :
    μ {x | ∀ n : ℤ, f ((σ ^ n) x) = v n} = 0 := by
  let F : X → ℤ → Y := fun x n => f ((σ ^ n) x)
  let s : Set X := F ⁻¹' {v}
  have hs : @MeasurableSet X (orbitMeasurableSpace σ f) s := by
    rw [orbitMeasurableSpace_eq_comap_tuple]
    exact ⟨{v}, measurableSet_singleton v, rfl⟩
  have hzero : μ s = 0 := by
    by_contra hpos
    obtain ⟨t, ht, hts, htpos, hdiff⟩ :=
      orbitMeasurableSpace_atomless σ hσ hinv htotal hf hnonconstant hs hpos
    rw [orbitMeasurableSpace_eq_comap_tuple] at ht
    obtain ⟨B, _hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht
    by_cases hv : v ∈ B
    · have hst : s ⊆ F ⁻¹' B := by
        intro x hx
        change F x = v at hx
        change F x ∈ B
        rwa [hx]
      exact hdiff (by rw [Set.sdiff_eq_empty.mpr hst, measure_empty])
    · have hempty : F ⁻¹' B = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxv : F x = v := hts hx
        exact hv (hxv ▸ hx)
      exact htpos (by rw [hempty, measure_empty])
  have heq : {x | ∀ n : ℤ, f ((σ ^ n) x) = v n} = s := by
    ext x
    simp only [s, F, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
      funext_iff]
  rwa [heq]

theorem measure_orbit_fiber_eq_zero_of_negInfiniteLogIntegral
    {μ : Measure X} [IsFiniteMeasure μ]
    (σ : Equiv.Perm X) (hσ : Measurable σ) (hinv : Measurable σ.symm)
    (htotal : ∀ n : ℕ, 0 < n → Ergodic (σ : X → X)^[n] μ)
    {f : X → ℝ} (hf : Measurable f)
    (hnonzero : ∀ᵐ x ∂μ, f x ≠ 0) (hlog : HasNegInfiniteLogIntegral μ f)
    (v : ℤ → ℝ) :
    μ {x | ∀ n : ℤ, f ((σ ^ n) x) = v n} = 0 :=
  measure_orbit_fiber_eq_zero σ hσ hinv htotal hf
    (not_ae_constant_of_negInfiniteLogIntegral hnonzero hlog) v

end Invariant233

end OAI
