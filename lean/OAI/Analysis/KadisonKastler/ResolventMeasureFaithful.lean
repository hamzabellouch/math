import OAI.Analysis.KadisonKastler.ResolventCyclicMultipliers
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

/-! # Faithfulness removes scalar spectral mass at a kernel

An indicator of a zero set would give a kernel vector in the cyclic
spectral model. Injectivity of the represented operator excludes it.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventVectorMeasure_zero_set (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (g : C(spectrum ℝ R, ℂ))
    (hinj : Function.Injective (resolventContinuousCalculus R hR g)) :
    resolventVectorMeasure R hR x {s | g s = 0} = 0 := by
  let μ := resolventVectorMeasure R hR x
  let S : Set (spectrum ℝ R) := {s | g s = 0}
  have hS : MeasurableSet S := (isClosed_eq g.continuous continuous_const).measurableSet
  let v : ResolventCyclicL2 R hR x := indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℂ)
  have hz : resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm v = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [resolventScalarMultiplier_apply_ae R hR x g g.continuous.measurable ‖g‖
      g.norm_coe_le_norm v, indicatorConstLp_coeFn (p := 2) (hs := hS)
        (hμs := measure_ne_top μ S) (c := (1 : ℂ))]
      with s ha hv
    rw [ha, hv]
    by_cases hs : s ∈ S
    · rw [Set.indicator_of_mem hs]
      change g s = 0 at hs
      simp only [hs, zero_mul, Pi.zero_apply]
    · rw [Set.indicator_of_notMem hs, mul_zero]
      rfl
  have hu : resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x v) = 0 := by
    rw [← resolventCyclicIsometry_multiplier, hz, map_zero]
  have hv0 : v = 0 := (resolventCyclicIsometry R hR x).injective
    ((hinj (hu.trans (map_zero _).symm)).trans (map_zero _).symm)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [Lp.eq_zero_iff_ae_eq_zero.mp hv0,
    indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := measure_ne_top μ S)
      (c := (1 : ℂ))] with s hv hs
  intro hmem
  have he : (1 : ℂ) = 0 := by
    have he := hs.symm.trans hv
    rw [Set.indicator_of_mem (show s ∈ S from hmem)] at he
    exact he
  exact one_ne_zero he

theorem resolventVectorMeasure_zero_endpoint (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) (x : H) :
    resolventVectorMeasure R hR x {s | s.val = 0} = 0 := by
  let g : C(spectrum ℝ R, ℂ) :=
    ⟨fun s => (s.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩
  have he : resolventContinuousCalculus R hR g = R := by
    exact (resolventContinuousCalculus_ofReal R hR
      ((ContinuousMap.id ℝ).restrict (spectrum ℝ R))).trans (cfcHom_id hR)
  have h := resolventVectorMeasure_zero_set R hR x g (by rwa [he])
  simpa only [g, ContinuousMap.coe_mk, Complex.ofReal_eq_zero] using h

theorem resolventVectorMeasure_one_endpoint (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective ((1 : H →L[ℂ] H) - R)) (x : H) :
    resolventVectorMeasure R hR x {s | s.val = 1} = 0 := by
  let g : C(spectrum ℝ R, ℂ) :=
    ⟨fun s => (s.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩
  have he : resolventContinuousCalculus R hR g = R := by
    exact (resolventContinuousCalculus_ofReal R hR
      ((ContinuousMap.id ℝ).restrict (spectrum ℝ R))).trans (cfcHom_id hR)
  have h := resolventVectorMeasure_zero_set R hR x (1 - g) (by
    simpa only [map_sub, map_one, he] using hinj)
  have hs : {s : spectrum ℝ R | (1 - g) s = 0} = {s | s.val = 1} := by
    ext s
    change (1 : ℂ) - (s.val : ℂ) = 0 ↔ s.val = 1
    rw [sub_eq_zero, eq_comm, Complex.ofReal_eq_one]
  rwa [hs] at h

end

end KadisonKastler

end OAI
