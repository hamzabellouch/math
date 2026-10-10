import OAI.InformationTheory.Entanglement.FactorizedLawGap
import OAI.InformationTheory.Entanglement.DefaultNull

namespace OAI

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder MeasureTheory Kronecker
namespace SecretKey
open ChannelCompletion
variable {T : Type*} [MeasurableSpace T] {n m : Type} [Fintype n] [Fintype m]
 [DecidableEq n] [DecidableEq m]
namespace PositiveMatrixMeasure

def restrict (W : PositiveMatrixMeasure T n) (A : Set T) : PositiveMatrixMeasure T n where
  entry i j := (W.entry i j).restrict A
  positive s hs := by
    by_cases hA : MeasurableSet A
    · simpa only [VectorMeasure.restrict_apply _ hA hs] using W.positive (s∩A) (hs.inter hA)
    · simp only [VectorMeasure.restrict_not_measurable _ hA]
      exact Matrix.PosSemidef.zero
omit [DecidableEq n] in
lemma restrict_value (W : PositiveMatrixMeasure T n) {A s : Set T}
    (hA : MeasurableSet A) (hs : MeasurableSet s) : (W.restrict A).value s=W.value (s∩A) := by
  ext i j
  exact VectorMeasure.restrict_apply _ hA hs

def scale (W : PositiveMatrixMeasure T n) (c : ℝ) (hc : 0≤c) : PositiveMatrixMeasure T n where
  entry i j := (c : ℂ) • W.entry i j
  positive s hs := by
    change ((c : ℂ) • W.value s).PosSemidef
    exact (W.positive s hs).smul (by exact_mod_cast hc)
omit [DecidableEq n] in
lemma scale_value (W : PositiveMatrixMeasure T n) (c : ℝ) (hc : 0≤c) (s : Set T) :
    (W.scale c hc).value s=(c : ℂ) • W.value s := rfl
end PositiveMatrixMeasure

def publicMass (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n) (A : Set T) : ℝ :=
  ∑ i, ∑ j, (Matrix.trace ((W i j).value A)).re
def conditionedBlocks (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n) (A : Set T)
    (hr : 0<publicMass W A) : Fin 2 → Fin 2 → PositiveMatrixMeasure T n :=
  fun i j => ((W i j).restrict A).scale (publicMass W A)⁻¹ (inv_nonneg.mpr hr.le)
omit [DecidableEq n] in
lemma conditionedBlocks_normalized (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    {A : Set T} (hA : MeasurableSet A) (hr : 0<publicMass W A) :
    (∑ i, ∑ j, (Matrix.trace ((conditionedBlocks W A hr i j).value Set.univ)).re)=1 := by
  simp only [conditionedBlocks,PositiveMatrixMeasure.scale_value,
    PositiveMatrixMeasure.restrict_value _ hA MeasurableSet.univ,Set.univ_inter,
    Matrix.trace_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,← Finset.mul_sum]
  exact inv_mul_cancel₀ hr.ne'

theorem conditioned_factorized_gap (R : Mat (n×m)) (hR : Represented R)
    (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T (n×m))
    (σ : PositiveMatrixMeasure T (n×m)) (μ : Measure T) [IsFiniteMeasure μ]
    (X : Fin 2 → T → Mat n) (Y : Fin 2 → T → Mat m)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ j, Measurable (Y j))
    (hXp : ∀ i t, (X i t).PosSemidef) (hYp : ∀ j t, (Y j t).PosSemidef)
    (hDi : ∀ i j a b, Integrable (fun t => eveBlock R (X i t ⊗ₖ Y j t) a b) μ)
    (hDs : ∀ i j s, MeasurableSet s → ∀ a b,
      (∫ t in s, eveBlock R (X i t ⊗ₖ Y j t) a b ∂μ)=(W i j).value s a b)
    (A : Set T) (hA : MeasurableSet A) (hr : 0<publicMass W A)
    (hσ1 : (Matrix.trace (σ.value Set.univ)).re=1) :
    1/5≤cqBitDistance (conditionedBlocks W A hr) σ := by
  let c := (publicMass W A)⁻¹
  have hc : 0≤c := inv_nonneg.mpr hr.le
  let X' := fun i t => (c : ℂ) • X i t
  have he (i j t) : eveBlock R (X' i t ⊗ₖ Y j t)=(c : ℂ) • eveBlock R (X i t ⊗ₖ Y j t) := by
    change eveBlock R (((c : ℂ) • X i t) ⊗ₖ Y j t) = _
    rw [Matrix.smul_kronecker,eveBlock_smul]
  apply factorized_law_gap R hR (conditionedBlocks W A hr) σ (μ.restrict A) X' Y
    (fun i => (measurable_const (a := (c : ℂ))).smul (hXm i)) hYm
    (fun i t => (hXp i t).smul (by exact_mod_cast hc)) hYp
  · intro i j a b
    simp only [he,Matrix.smul_apply,smul_eq_mul]
    exact ((hDi i j a b).integrableOn).const_mul _
  · intro i j s hs a b
    simp only [he,Matrix.smul_apply,smul_eq_mul,integral_const_mul]
    rw [Measure.restrict_restrict hs,hDs i j (s∩A) (hs.inter hA)]
    simp only [conditionedBlocks,PositiveMatrixMeasure.scale_value,
      PositiveMatrixMeasure.restrict_value _ hA hs,Matrix.smul_apply,smul_eq_mul,c]
  · exact conditionedBlocks_normalized W hA hr
  · exact hσ1

end SecretKey

end

end OAI
