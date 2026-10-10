import Mathlib
import OAI.Analysis.WeakInfiniteness.ColumnCoreNorm
import OAI.Analysis.WeakInfiniteness.OrthogonalCores
import OAI.Analysis.WeakInfiniteness.Plateau
import OAI.Analysis.WeakInfiniteness.SeparationCores
import OAI.Analysis.WeakInfiniteness.SeparationScalar

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

omit [PartialOrder A] [StarOrderedRing A] in
lemma map_column_core_norm (π : A →⋆ₙₐ[ℂ] B) (D : A) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖π (cfcₙ (columnCoreFunction τ) (star D*D))‖=max (‖π D‖-τ) 0 := by
  rw [π.map_cfcₙ (columnCoreFunction τ) (star D*D)
    (continuous_columnCoreFunction τ).continuousOn (columnCoreFunction_zero hτ)
    (by fun_prop) (IsSelfAdjoint.star_mul_self D)
    ((IsSelfAdjoint.star_mul_self D).map π)]
  rw [map_mul,map_star,cfcₙ_eq_cfc (continuous_columnCoreFunction τ).continuousOn (columnCoreFunction_zero hτ)]
  exact norm_column_core _ hτ

omit [PartialOrder A] [StarOrderedRing A] in
lemma separationG_core (X : A) {l : ℝ} (hl : 0 < l) :
    cfcₙ (separationG l) (star X*X)*cfcₙ (columnCoreFunction (2*l)) (star X*X)=
      cfcₙ (columnCoreFunction (2*l)) (star X*X) := by
  rw [← cfcₙ_mul (separationG l) (columnCoreFunction (2*l)) _
    (continuous_separationG l).continuousOn (separationG_zero hl)
    (continuous_columnCoreFunction (2*l)).continuousOn (columnCoreFunction_zero (by positivity))]
  apply cfcₙ_congr
  intro s _
  change separationG l s*max (Real.sqrt s-2*l) 0=max (Real.sqrt s-2*l) 0
  by_cases h : Real.sqrt s ≤ 2*l
  · rw [max_eq_right (sub_nonpos.mpr h),mul_zero]
  · rw [show separationG l s=1 from spectralRamp_eq_one hl (le_of_not_ge h),one_mul]

lemma exists_separation_cores
    (hpi : ∀ a : A,0 ≤ a → ProperlyInfinite (diagonalCopies 1 a))
    (X : A) {l : ℝ} (hl : 0 < l) :
    let g := cfcₙ (separationG l) (star X*X)
    ∃ e f k₁ k₂ : A,0 ≤ e ∧ 0 ≤ f ∧ 0 ≤ k₁ ∧ 0 ≤ k₂ ∧
      ‖e‖ ≤ 1 ∧ ‖f‖ ≤ 1 ∧ e*f=0 ∧ e*star e*k₁=k₁ ∧ f*star f*k₂=k₂ ∧
      g*e=e ∧ g*f=f ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        4*l ≤ ‖π X‖ → π k₁ ≠ 0 ∧ π k₂ ≠ 0 := by
  dsimp only
  let h₀ : A := cfcₙ (columnCoreFunction (2*l)) (star X*X)
  let g : A := cfcₙ (separationG l) (star X*X)
  have hh₀ : 0 ≤ h₀ := cfcₙ_nonneg (fun s _ => le_max_right _ _)
  obtain ⟨e₀,f₀,he₀,hf₀,_,_,hef₀,heh,hfh,hrep⟩ :=
    exists_two_orthogonal_cores hh₀ (hpi h₀ hh₀) hl
  let e : A := cfcₙ (spectralRamp (1/4)) e₀
  let f : A := cfcₙ (spectralRamp (1/4)) f₀
  let k₁ : A := positiveCut (1/2) e₀
  let k₂ : A := positiveCut (1/2) f₀
  have he : 0 ≤ e := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg _ s)
  have hf : 0 ≤ f := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg _ s)
  have heE : e ∈ hereditarySubalgebra e₀ he₀.isSelfAdjoint := cfcₙ_mem _ (self_mem_hereditary e₀ he₀)
  have hfF : f ∈ hereditarySubalgebra f₀ hf₀.isSelfAdjoint := cfcₙ_mem _ (self_mem_hereditary f₀ hf₀)
  have heH : e ∈ hereditarySubalgebra h₀ hh₀.isSelfAdjoint := cfcₙ_mem _ heh
  have hfH : f ∈ hereditarySubalgebra h₀ hh₀.isSelfAdjoint := cfcₙ_mem _ hfh
  have hgH : g*h₀=h₀ := separationG_core X hl
  have hek : e*k₁=k₁ := spectralRamp_mul_positiveCut e₀ (by norm_num) (by norm_num)
  have hfk : f*k₂=k₂ := spectralRamp_mul_positiveCut f₀ (by norm_num) (by norm_num)
  refine ⟨e,f,k₁,k₂,he,hf,positiveCut_nonneg _ _,positiveCut_nonneg _ _,
    norm_spectralRamp_le_one _ _,norm_spectralRamp_le_one _ _,
    mul_zero_of_hereditary he₀.isSelfAdjoint hf₀.isSelfAdjoint hef₀ heE hfF,?_,?_,
    left_identity_on_hereditary g h₀ hh₀.isSelfAdjoint hgH heH,
    left_identity_on_hereditary g h₀ hh₀.isSelfAdjoint hgH hfH,?_⟩
  · rw [he.star_eq,mul_assoc,hek,hek]
  · rw [hf.star_eq,mul_assoc,hfk,hfk]
  · intro H π hn
    have hhn : 2*l ≤ ‖π h₀‖ := by
      rw [show h₀=cfcₙ (columnCoreFunction (2*l)) (star X*X) from rfl,
        map_column_core_norm π X (by positivity)]
      exact le_trans (by linarith) (le_max_left _ _)
    obtain ⟨heN,hfN⟩ := hrep H π hhn
    constructor
    · have hm : π k₁=positiveCut (1/2) (π e₀) :=
        π.map_cfcₙ (fun s : ℝ => max (s-1/2) 0) e₀ (by fun_prop) (by norm_num)
          (by fun_prop) he₀.isSelfAdjoint (map_nonneg π he₀).isSelfAdjoint
      rw [hm]
      exact positiveCut_ne_zero_of_lt_norm (map_nonneg π he₀) (by norm_num) (by rw [heN]; norm_num)
    · have hm : π k₂=positiveCut (1/2) (π f₀) :=
        π.map_cfcₙ (fun s : ℝ => max (s-1/2) 0) f₀ (by fun_prop) (by norm_num)
          (by fun_prop) hf₀.isSelfAdjoint (map_nonneg π hf₀).isSelfAdjoint
      rw [hm]
      exact positiveCut_ne_zero_of_lt_norm (map_nonneg π hf₀) (by norm_num) (by rw [hfN]; norm_num)

end

end

end WeakPureInfiniteness
end

end OAI
