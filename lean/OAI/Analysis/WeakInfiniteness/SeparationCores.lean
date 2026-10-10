import Mathlib
import OAI.Analysis.WeakInfiniteness.ColumnNormalization
import OAI.Analysis.WeakInfiniteness.NonunitalSpectralTools2

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma columnCoreFunction_zero {τ : ℝ} (hτ : 0 ≤ τ) : columnCoreFunction τ 0=0 := by
  simp only [columnCoreFunction,Real.sqrt_zero,zero_sub]
  exact max_eq_right (neg_nonpos.mpr hτ)

lemma nonunital_column_left_normalization (D : A) {τ : ℝ} (hτ : 0 < τ) :
    let F : Unitization ℂ A := cfc (columnMetricFunction τ) ((D : Unitization ℂ A)*star (D : Unitization ℂ A))
    let h : A := cfcₙ (columnCoreFunction τ) (star D*D)
    ∃ p : A,F*(D : Unitization ℂ A)=(p : Unitization ℂ A) ∧
      ‖F‖ ≤ τ⁻¹ ∧ ‖p‖ ≤ 1 ∧ 0 ≤ h ∧ star p*p*h=h := by
  dsimp only
  let F : Unitization ℂ A := cfc (columnMetricFunction τ) ((D : Unitization ℂ A)*star (D : Unitization ℂ A))
  let p : A := (F*(D : Unitization ℂ A)).snd
  let h : A := cfcₙ (columnCoreFunction τ) (star D*D)
  have hp : (p : Unitization ℂ A)=F*(D : Unitization ℂ A) := by
    apply unitization_inr_snd_of_fst_eq_zero
    simp only [Unitization.fst_mul,Unitization.fst_inr,mul_zero]
  have hh : (h : Unitization ℂ A)=cfc (columnCoreFunction τ) (star (D : Unitization ℂ A)*(D : Unitization ℂ A)) := by
    dsimp only [h]
    rw [Unitization.real_cfcₙ_eq_cfc_inr _ _ (columnCoreFunction_zero hτ.le),Unitization.inr_mul,Unitization.inr_star]
  obtain ⟨hF,hpn,hhn,hph⟩ := column_left_normalization (D : Unitization ℂ A) hτ
  refine ⟨p,hp.symm,hF,?_,?_,?_⟩
  · rw [← Unitization.norm_inr (𝕜 := ℂ) p,hp]
    exact hpn
  · exact cfcₙ_nonneg (fun s _ => le_max_right _ _)
  · apply Unitization.inr_injective (R := ℂ)
    rw [Unitization.inr_mul,Unitization.inr_mul,Unitization.inr_star,hp,hh]
    exact hph

end

end

end WeakPureInfiniteness
end

end OAI
