import Mathlib
import OAI.Analysis.WeakInfiniteness.FinalAssembly
import OAI.Analysis.WeakInfiniteness.SeparationCoreSelection
import OAI.Analysis.WeakInfiniteness.SeparationCoverage

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

universe u v

section

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_separationN (π : A →⋆ₙₐ[ℂ] B) (X : A) {l : ℝ} (hl : 0 < l) :
    π (cfcₙ (separationN l) (star X*X))=cfc (separationN l) (star (π X)*π X) := by
  rw [π.map_cfcₙ (separationN l) (star X*X) (continuous_separationN l).continuousOn
    (separationN_zero hl) (by fun_prop) (IsSelfAdjoint.star_mul_self X) ((IsSelfAdjoint.star_mul_self X).map π),
    map_mul,map_star,cfcₙ_eq_cfc (continuous_separationN l).continuousOn (separationN_zero hl)]

omit [PartialOrder A] [StarOrderedRing A] in
lemma nonunital_separationGN (X : A) {l : ℝ} (hl : 0 < l) :
    cfcₙ (separationG l) (star X*X)*cfcₙ (separationN l) (star X*X)=
      cfcₙ (separationN l) (star X*X) := by
  rw [← cfcₙ_mul _ _ _ (continuous_separationG l).continuousOn (separationG_zero hl)
    (continuous_separationN l).continuousOn (separationN_zero hl)]
  exact cfcₙ_congr (fun s _ => separationGN hl s)

omit [PartialOrder A] [StarOrderedRing A] in
lemma nonunital_norm_separationN (X : A) (l : ℝ) :
    ‖cfcₙ (separationN l) (star X*X)‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro s _
  change ‖spectralRamp (4*l) (Real.sqrt s)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (spectralRamp_nonneg _ _)]
  exact spectralRamp_le_one _ _

lemma separation_core_comparisons
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    (X C k : A) (hk : 0 ≤ k) {l τ : ℝ} (hl : 0 < l) (hτ : 0 < τ)
    (hkdet : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),4*l ≤ ‖π X‖ → π k ≠ 0) :
    let g := cfcₙ (separationG l) (star X*X)
    let N := cfcₙ (separationN l) (star X*X)
    let h := cfcₙ (columnCoreFunction τ) (star (C*g)*(C*g))
    let d := cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N))
    ElementCuntzSubequiv d h ∧ ElementCuntzSubequiv d k := by
  dsimp only
  let g := cfcₙ (separationG l) (star X*X)
  let N := cfcₙ (separationN l) (star X*X)
  let h := cfcₙ (columnCoreFunction τ) (star (C*g)*(C*g))
  let d := cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N))
  have hh : 0 ≤ h := cfcₙ_nonneg (fun s _ => le_max_right _ _)
  have hd : 0 ≤ d := cfcₙ_nonneg (fun s _ => le_max_right _ _)
  have hnlt (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπd : π d ≠ 0) :
      2*τ < ‖π (C*N)‖ := by
    have hn := norm_pos_iff.mpr hπd
    rw [show d=cfcₙ (columnCoreFunction (2*τ)) (star (C*N)*(C*N)) from rfl,
      map_column_core_norm π (C*N) (by positivity)] at hn
    exact sub_pos.mp ((lt_max_iff.mp hn).resolve_right (lt_irrefl 0))
  constructor
  · apply elementCuntz_of_primitive_support hpi hd hh
    intro H π _ hπd
    have hlt := hnlt H π hπd
    have hn : ‖π (C*N)‖ ≤ ‖π (C*g)‖ := by
      have he : C*N=(C*g)*N := by rw [mul_assoc,nonunital_separationGN X hl]
      rw [he,map_mul]
      have hN : ‖π N‖ ≤ 1 := (NonUnitalStarAlgHom.norm_apply_le π _).trans (nonunital_norm_separationN X l)
      exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (π (C*g))])
    apply norm_pos_iff.mp
    rw [show h=cfcₙ (columnCoreFunction τ) (star (C*g)*(C*g)) from rfl,
      map_column_core_norm π (C*g) hτ.le]
    exact lt_of_lt_of_le (by linarith : 0 < ‖π (C*g)‖-τ) (le_max_left _ _)
  · apply elementCuntz_of_primitive_support hpi hd hk
    intro H π _ hπd
    apply hkdet H π
    by_contra hn
    have hN : π N=0 := by
      rw [show N=cfcₙ (separationN l) (star X*X) from rfl,map_separationN π X hl]
      exact separationN_eq_zero_of_norm_le _ hl (le_of_lt (lt_of_not_ge hn))
    have hnlt' := hnlt H π hπd
    rw [map_mul,hN,mul_zero,norm_zero] at hnlt'
    linarith

end

end

end WeakPureInfiniteness
end

end OAI
