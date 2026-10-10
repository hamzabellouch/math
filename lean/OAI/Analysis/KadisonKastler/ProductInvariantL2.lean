import OAI.Analysis.KadisonKastler.ProductInvariantIntegrals
import OAI.Analysis.KadisonKastler.ShiftInvariantFunctions
import OAI.Analysis.KadisonKastler.ScalarWeakLimit
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

namespace OAI

/-! # The product range of a one-coordinate invariant projection

An L2 function fixed by the shift in its first coordinate is measurable,
modulo null sets, for the product of the invariant and second sigma algebras.
The proof tests its orthogonal-projection remainder against rectangles.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {S : X → X}

def firstCoordinateShift (S : X → X) (z : X × Y) : X × Y := (S z.1, z.2)

@[instance_reducible]
def firstInvariantSigma (μ : Measure X) (S : X → X) : MeasurableSpace (X × Y) :=
  (shiftInvariantSigma μ S).prod ‹MeasurableSpace Y›

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem firstInvariantSigma_le : firstInvariantSigma (Y := Y) μ S ≤
    (inferInstance : MeasurableSpace (X × Y)) := by
  apply sup_le_sup
  · exact MeasurableSpace.comap_mono (shiftInvariantSigma_le μ S)
  · exact le_rfl

theorem firstCoordinateShift_quasi (hS : Measure.QuasiMeasurePreserving S μ μ) :
    Measure.QuasiMeasurePreserving (firstCoordinateShift (Y := Y) S) (μ.prod ν) (μ.prod ν) :=
  MeasureTheory.QuasiMeasurePreserving.prodMap hS (Measure.QuasiMeasurePreserving.id ν)

omit [IsFiniteMeasure μ] in
theorem firstInvariantSigma_le_shiftInvariantSigma :
    firstInvariantSigma (Y := Y) μ S ≤
      shiftInvariantSigma (μ.prod ν) (firstCoordinateShift S) := by
  have hfst : @Measurable (X × Y) X
      (shiftInvariantSigma (μ.prod ν) (firstCoordinateShift S)) (shiftInvariantSigma μ S)
      Prod.fst := by
    intro A hA
    refine ⟨hA.1.preimage measurable_fst, ?_⟩
    exact (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hA.2
  have hsnd : @Measurable (X × Y) Y
      (shiftInvariantSigma (μ.prod ν) (firstCoordinateShift S)) ‹MeasurableSpace Y›
      Prod.snd := by
    intro B hB
    exact ⟨hB.preimage measurable_snd, Filter.Eventually.of_forall (fun _ => Iff.rfl)⟩
  exact hfst.prodMk hsnd

theorem firstInvariantSigma_fixed (hS : Measure.QuasiMeasurePreserving S μ μ)
    {f : X × Y → ℂ} (hf : AEStronglyMeasurable[firstInvariantSigma μ S] f (μ.prod ν)) :
    ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z := by
  have hm := hf.mono (firstInvariantSigma_le_shiftInvariantSigma (ν := ν))
  have hi := complex_fixed_of_measurable_shiftInvariantSigma hm.stronglyMeasurable_mk.measurable
  filter_upwards [hm.ae_eq_mk, (firstCoordinateShift_quasi (ν := ν) hS).ae hm.ae_eq_mk, hi]
    with z hz hs hi
  exact hs.trans (hi.trans hz.symm)

theorem L2_mem_firstInvariantSigma_of_fixed
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : Lp ℂ 2 (μ.prod ν))
    (hf : ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z) :
    f ∈ lpMeas ℂ ℂ (firstInvariantSigma μ S) 2 (μ.prod ν) := by
  have hm : firstInvariantSigma (Y := Y) μ S ≤ mX.prod mY := firstInvariantSigma_le
  let : Fact (firstInvariantSigma (Y := Y) μ S ≤ mX.prod mY) := ⟨hm⟩
  let K := lpMeas ℂ ℂ (firstInvariantSigma μ S) 2 (μ.prod ν)
  let p := K.starProjection f
  let h := f - p
  have hp : p ∈ K := K.starProjection_apply_mem f
  have hpf := firstInvariantSigma_fixed hS
    (mem_lpMeas_iff_aestronglyMeasurable.mp hp)
  have hfix : ∀ᵐ z ∂μ.prod ν, h (S z.1, z.2) = h z := by
    filter_upwards [hf, hpf, Lp.coeFn_sub f p,
      (firstCoordinateShift_quasi (ν := ν) hS).ae (Lp.coeFn_sub f p)] with z hf hp hz hs
    change h (firstCoordinateShift S z) = h z
    change h (firstCoordinateShift S z) = _ at hs
    rw [hs, hz]
    exact congrArg₂ (· - ·) hf hp
  have hz : h = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    apply invariant_integrable_zero_of_rectangle_tests (Lp.stronglyMeasurable h)
      ((Lp.memLp h).integrable (by norm_num)) hfix
    intro A B hA hB
    have hAB : MeasurableSet[firstInvariantSigma μ S] (A ×ˢ B) := hA.prod hB
    have hAB' : MeasurableSet (A ×ˢ B) := hm _ hAB
    have hfin : (μ.prod ν) (A ×ˢ B) ≠ ⊤ := measure_ne_top _ _
    have hi : indicatorConstLp 2 hAB' hfin (1 : ℂ) ∈ K :=
      mem_lpMeas_indicatorConstLp hm hAB hfin
    have ho := (K.sub_starProjection_mem_orthogonal f) _ hi
    exact (L2.inner_indicatorConstLp_one hAB' hfin h).symm.trans ho
  have he : f = p := sub_eq_zero.mp hz
  rw [he]
  exact hp

section Bounded

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem scalarInfinity_mem_firstInvariantSigma_of_fixed
    (hS : Measure.QuasiMeasurePreserving S μ μ) (f : ScalarLInfinity (μ.prod ν))
    (hf : scalarInfinityPullback (firstCoordinateShift S)
      (firstCoordinateShift_quasi hS) f = f) :
    f ∈ lpMeas ℂ ℂ (firstInvariantSigma μ S) ⊤ (μ.prod ν) := by
  have hfix : ∀ᵐ z ∂μ.prod ν,
      scalarInfinityToL2 f (S z.1, z.2) = scalarInfinityToL2 f z := by
    have ha := scalarInfinityPullback_ae (firstCoordinateShift S)
      (firstCoordinateShift_quasi hS) f
    rw [hf] at ha
    filter_upwards [ha, scalarInfinityToL2_ae f,
      (firstCoordinateShift_quasi (ν := ν) hS).ae (scalarInfinityToL2_ae f)]
      with z ha hz hs
    exact hs.trans (ha.symm.trans hz.symm)
  have hm := L2_mem_firstInvariantSigma_of_fixed hS (scalarInfinityToL2 f) hfix
  exact mem_lpMeas_iff_aestronglyMeasurable.mpr
    ((mem_lpMeas_iff_aestronglyMeasurable.mp hm).congr (scalarInfinityToL2_ae f))

end Bounded

end

end KadisonKastler

end OAI
