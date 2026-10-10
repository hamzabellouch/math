import Mathlib
import OAI.Probability.SKBarriers.Interpolation.SKHamiltonianDerivative
import OAI.Probability.SKBarriers.Gaussian.GaussianStepAlgebra

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Terminal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineLogPartition_sites (N : ℕ) (L : Fin N → E →L[ℝ] ℝ) :
    affineLogPartition (fun _ : Config N => 0) (fun s => ∑ i, spin (s i) • L i) =
      fun z => ∑ i, affineLogPartition (fun _ : Bool => 0) (fun b => spin b • L i) z := by
  funext z
  simp only [affineLogPartition,zero_add,sum_apply,
    smul_apply,smul_eq_mul,Real.exp_sum]
  rw [← Fintype.prod_sum (fun i b => Real.exp (spin b * L i z)),Real.log_prod]
  intro i _
  exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'

theorem affineLogPartition_bool (L : E →L[ℝ] ℝ) (z : E) :
    affineLogPartition (fun _ : Bool => 0) (fun b => spin b • L) z =
      Real.log (2*Real.cosh (L z)) := by
  simp only [affineLogPartition,zero_add,smul_apply,smul_eq_mul,
    Fintype.sum_bool,spin,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,Real.cosh_eq]
  congr 1
  ring
end Terminal

def siteField {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    ParameterSpace (blockDimension D N k) →L[ℝ] ℝ :=
  ∑ b, v b • coordinateProjection (blockDimension D N k) (fieldIndex D N k b i)

def siteLogPartition {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    ParameterSpace (blockDimension D N k) → ℝ :=
  affineLogPartition (fun _ : Bool => 0) (fun b => spin b • siteField (D := D) v i)

theorem blockExponent_zero_disorder {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (v : Fin (k+1) → ℝ) (s : Config N) :
    blockExponent I (fun _ => 0) v s = ∑ i, spin (s i) • siteField (D := D) v i := by
  ext z
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,zero_add,siteField,
    sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem blockLogPartition_zero_disorder {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (v : Fin (k+1) → ℝ) :
    affineLogPartition (fun _ => 0) (blockExponent I (fun _ => 0) v) =
      fun z => ∑ i, siteLogPartition (D := D) v i z := by
  convert affineLogPartition_sites N (siteField (D := D) v) using 1
  · congr 1
    funext s
    exact blockExponent_zero_disorder I v s
  · rfl

def fieldOwner {D N k : ℕ} (i₀ : Fin N) : Fin (blockDimension D N k) → Fin N :=
  Fin.addCases (fun _ => i₀) (fun t => (finProdFinEquiv.symm t).2)

@[simp] theorem fieldOwner_field {D N k : ℕ} (i₀ : Fin N) (b : Fin (k+1)) (i : Fin N) :
    fieldOwner i₀ (fieldIndex D N k b i) = i := by
  rw [fieldIndex_eq_natAdd]
  unfold fieldOwner
  rw [Fin.addCases_right]
  rw [Equiv.symm_apply_apply]

theorem siteLogPartition_invariant {D N k : ℕ} (v : Fin (k+1) → ℝ) (i₀ i : Fin N)
    (t : Fin (blockDimension D N k)) (h : i ≠ fieldOwner i₀ t) :
    TranslationInvariant (siteLogPartition (D := D) v i) (coordinateAxis (blockDimension D N k) t) := by
  apply affineLogPartition_translation
  intro b
  simp only [smul_apply,siteField,sum_apply,
    smul_eq_mul,coordinateProjection_coordinateAxis]
  have he (j : Fin (k+1)) : fieldIndex D N k j i ≠ t := by
    intro ht
    apply h
    rw [← ht,fieldOwner_field]
  simp only [he,ite_false,mul_zero,Finset.sum_const_zero]

theorem skBlockRoot_zero_disorder_tensorizes {N k : ℕ} (hN : 0 < N) (v : Fin (k+1) → ℝ) :
    skBlockRoot N k 0 v =
      ∑ i, hierarchyPressure (blockDimension (Fintype.card (Edge N)) N k)
        (blockMass (Fintype.card (Edge N)) N k)
        (siteLogPartition (D := Fintype.card (Edge N)) v i) 0 := by
  simp only [skBlockRoot,zero_div,blockLogPartition_zero_disorder]
  exact congrFun (hierarchyPressure_sum_independent _ _ (fieldOwner ⟨0,hN⟩)
    (fun i => siteLogPartition (D := Fintype.card (Edge N)) v i)
    (fun i => affineLogPartition_boundedDerivs _ _)
    (fun t i h => siteLogPartition_invariant v ⟨0,hN⟩ i t h)) 0
end SK.Analytic

end
end

end

end OAI
