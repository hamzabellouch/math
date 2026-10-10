import Mathlib
import OAI.Analysis.WeakInfiniteness.NonunitalSpectralTools
import OAI.Analysis.WeakInfiniteness.SeparationCoreSelection
import OAI.Analysis.WeakInfiniteness.SeparationNormCoverage

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

universe u

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma separation_transferred_coverage
    (a x₀ x₁ C N : A) (K F Y : Unitization ℂ A) {r l τ c : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hτ : τ=r*Real.sqrt l/8) (hc : c ≤ 4)
    (haeq : (a : Unitization ℂ A)=(x₀ : Unitization ℂ A)+((C : Unitization ℂ A)*(N : Unitization ℂ A))*K)
    (hx₁ : (x₁ : Unitization ℂ A)=(((Real.sqrt l)⁻¹ : ℝ) : ℂ) • Y)
    (hK : ‖K‖ ≤ (Real.sqrt l)⁻¹) (hF : ‖F‖ ≤ τ⁻¹)
    (hdet : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      τ ≤ ‖π (cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N)))‖ →
      c ≤ ‖(Unitization.starLift π) (F*Y)‖) :
    ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),r ≤ ‖π a‖ →
      r*c/8 ≤ max ‖π x₀‖ ‖π x₁‖ := by
  intro H π hπ
  let φ := Unitization.starLift π
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hD : ‖π (C*N)‖=‖φ (C : Unitization ℂ A)*φ (N : Unitization ℂ A)‖ := by
    rw [← map_mul,← Unitization.inr_mul,starLift_inr_apply_general]
  have hFπ : ‖φ F‖ ≤ τ⁻¹ := (NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom _).trans hF
  have hKπ : ‖φ K‖ ≤ (Real.sqrt l)⁻¹ := (NonUnitalStarAlgHom.norm_apply_le φ.toNonUnitalStarAlgHom _).trans hK
  have hxπ : φ (x₁ : Unitization ℂ A)=(((Real.sqrt l)⁻¹ : ℝ) : ℂ) • φ Y := by rw [hx₁,map_smul]
  have haπ : φ (a : Unitization ℂ A)=φ (x₀ : Unitization ℂ A)+
      (φ (C : Unitization ℂ A)*φ (N : Unitization ℂ A))*φ K := by
    rw [haeq,map_add,map_mul,map_mul]
  have ht := separation_column_coverage (φ (a : Unitization ℂ A)) (φ (x₀ : Unitization ℂ A))
    (φ (C : Unitization ℂ A)) (φ (N : Unitization ℂ A)) (φ K) (φ F) (φ Y)
    hr hl hτ hc (by simpa only [φ,starLift_inr_apply_general] using hπ) haπ hKπ hFπ
    (fun hd => by
      rw [← map_mul]
      apply hdet H π
      rw [map_column_core_norm π (C*N) (by positivity),hD]
      exact hd)
  rw [← hxπ] at ht
  simpa only [φ,starLift_inr_apply_general] using ht

end

end

end WeakPureInfiniteness
end

end OAI
