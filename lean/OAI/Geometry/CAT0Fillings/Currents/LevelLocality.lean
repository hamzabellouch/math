import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Extensions
import OAI.Geometry.CAT0Fillings.Charts.CurrentAxioms

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma LipschitzWith.ae_fderiv_zero_on_level {F : E → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (c : ℝ) :
    ∀ᵐ x ∂μ, F x = c → fderiv ℝ F x = 0 := by
  have hset : MeasurableSet {x | F x = c} := isClosed_eq hF.continuous continuous_const |>.measurableSet
  apply (ae_restrict_iff' hset).mp
  have heq : EqOn F (fun _ => c) {x | F x = c} := fun _ hx => hx
  filter_upwards [ae_uniqueDiffWithinAt μ {x | F x = c},ae_restrict_mem hset,
    (hF.ae_differentiableAt (μ := μ)).filter_mono (ae_mono Measure.restrict_le_self)]
    with x hx hxc hd
  rw [← fderivWithin_eq_fderiv hx hd, fderivWithin_congr' heq hxc]
  simpa only [Function.const_def,Pi.zero_apply] using
    congrFun (fderivWithin_const (𝕜 := ℝ) (E := E) (s := {x | F x = c}) c) x

lemma ae_fderivWithin_zero_on_level {s : Set E} (hs : MeasurableSet s)
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (c : ℝ) :
    ∀ᵐ x ∂μ.restrict s, f x = c → fderivWithin ℝ f s x = 0 := by
  obtain ⟨F,hF,heq⟩ := hf.extend_real
  filter_upwards [ae_fderivWithin_eq_fderiv_extension μ hs hF heq,
    (LipschitzWith.ae_fderiv_zero_on_level μ hF c).filter_mono
      (ae_mono Measure.restrict_le_self),ae_restrict_mem hs] with x hx hz hxs
  intro hfc
  rw [hx]
  exact hz ((heq hxs).symm.trans hfc)

end CAT0Fillings

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ}
  (C : IntegerChart X (k+1))

lemma boundary_action_locality (b : X → ℝ) (π : Fin k → X → ℝ) (h : Admissible b π)
    (hloc : ∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧ Function.support b ⊆ U ∧
      ∀ x ∈ U, π i x = c) : C.action (fun _ => 1) (Matrix.vecCons b π) = 0 := by
  obtain ⟨i,U,c,hU,hb,hπ⟩ := hloc
  obtain ⟨L,J,hφ,_⟩ := C.bilipschitz
  obtain ⟨K,hK⟩ := h.1.1
  have hadm : Admissible (fun _ : X => (1:ℝ)) (Matrix.vecCons b π) :=
    ⟨BoundedLip.const 1,fun j => Fin.cases h.1.1 (fun l => h.2 l) j⟩
  rw [action,ite_eq_left hadm]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem C.borel,
    ae_fderivWithin_zero_on_level volume C.borel (C.scalar_lipschitzOn hφ hK) 0]
    with z hz hzero
  have hdet : C.jacobian (Matrix.vecCons b π) z = 0 := by
    by_cases hbz : C.scalar b z = 0
    · apply Matrix.det_eq_zero_of_row_eq_zero 0
      intro j
      change fderivWithin ℝ (C.scalar b) C.domain z (EuclideanSpace.single j 1) = 0
      rw [hzero hbz]; rfl
    · have hext : C.paramExtended z = C.param ⟨z,hz⟩ := by simp [paramExtended,hz]
      have hzU : C.paramExtended z ∈ U := by
        rw [hext]
        apply hb
        simpa [Function.mem_support,C.scalar_eq hz] using hbz
      have hh := (C.continuousOn_paramExtended z hz).preimage_mem_nhdsWithin (hU.mem_nhds hzU)
      have heq : C.scalar (π i) =ᶠ[𝓝[C.domain] z] fun _ => c := by
        filter_upwards [hh,eventually_mem_nhdsWithin] with y hy hys
        rw [C.scalar_eq hys]
        have hye : C.paramExtended y = C.param ⟨y,hys⟩ := by simp [paramExtended,hys]
        exact hπ _ (hye ▸ hy)
      have heqz : C.scalar (π i) z = c := by
        rw [C.scalar_eq hz]
        exact hπ _ (hext ▸ hzU)
      have hd0 : fderivWithin ℝ (C.scalar (π i)) C.domain z = 0 :=
        (heq.fderivWithin_eq (𝕜 := ℝ) heqz).trans (by
          simpa only [Function.const_def,Pi.zero_apply] using
            congrFun (fderivWithin_const (𝕜 := ℝ) (E := Euc (k+1)) (s := C.domain) c) z)
      apply Matrix.det_eq_zero_of_row_eq_zero i.succ
      intro j
      change fderivWithin ℝ (C.scalar (π i)) C.domain z (EuclideanSpace.single j 1) = 0
      rw [hd0]; rfl
  rw [hdet,mul_zero]; rfl

end CAT0Fillings.IntegerChart

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}

omit [BorelSpace X] in
lemma IntegerRectifiable.boundary_locality {T : Functional X (k+1)}
    (hT : IntegerRectifiable T) (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π)
    (hloc : ∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧ Function.support b ⊆ U ∧
      ∀ x ∈ U, π i x = c) : boundarySucc T b π = 0 := by
  classical
  rw [boundarySucc,ite_eq_left hab]
  obtain ⟨C,hd,hC,hs,heq⟩ := hT
  rw [heq]
  suffices hall : ∀ i, (C i).action (fun _ => 1) (Matrix.vecCons b π) = 0 by
    simp only [hall,tsum_zero]
  intro i
  rcases isEmpty_or_nonempty X with hX | hX
  · have hb0 : (fun _ : X => (1:ℝ)) = fun _ => 0 := funext (fun x => isEmptyElim x)
    rw [hb0]
    simpa using (hC i).linearFirst (fun _ => 0) (fun _ => 0) (Matrix.vecCons b π) 0 0
      (BoundedLip.const 0) (BoundedLip.const 0) (fun j => Fin.cases hab.1.1 (fun l => hab.2 l) j)
  · exact (C i).boundary_action_locality b π hab hloc

end CAT0Fillings

end

end OAI
