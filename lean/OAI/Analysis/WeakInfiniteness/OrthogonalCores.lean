import Mathlib
import OAI.Analysis.WeakInfiniteness.CuntzCopies
import OAI.Analysis.WeakInfiniteness.CutImplementation
import OAI.Analysis.WeakInfiniteness.NonunitalSpectralTools2
import OAI.Analysis.WeakInfiniteness.SupportedCorner
import OAI.Analysis.WeakInfiniteness.TensorFoundations

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

open scoped Topology CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance matrixRealModuleCores {m : Type*} [Fintype m] :
    Module ℝ (CStarMatrix m m A) := Module.complexToReal _

lemma exists_two_exact_core_columns {h : A} (hh : 0 ≤ h)
    (hpi : ProperlyInfinite (diagonalCopies 1 h)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r s : A,star r*r=cfcₙ (spectralRamp δ) h ∧
      star s*s=cfcₙ (spectralRamp δ) h ∧ star r*s=0 ∧
      r*star r+s*star s ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  have hc := hpi.diagonal_absorbs (by norm_num : 1 ≤ 1) 2
  obtain ⟨R,hR,hRher,_⟩ := hc.exact_spectralRamp (diagonalCopies_nonneg 2 hh)
    (diagonalCopies_nonneg 1 hh) δ hδ
  rw [← diagonalCopies_cfc 2 h hh.isSelfAdjoint (spectralRamp δ)
    (continuous_spectralRamp δ) (spectralRamp_eq_zero hδ hδ.le)] at hR
  refine ⟨R 0 0,R 0 1,?_,?_,?_,?_⟩
  · have he := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M 0 0) hR
    simpa only [CStarMatrix.mul_apply,CStarMatrix.conjTranspose_apply,Fin.sum_univ_one,
      diagonalCopies,CStarMatrix.ofMatrix_apply,Matrix.diagonal_apply_eq] using he
  · have he := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M 1 1) hR
    simpa only [CStarMatrix.mul_apply,CStarMatrix.conjTranspose_apply,Fin.sum_univ_one,
      diagonalCopies,CStarMatrix.ofMatrix_apply,Matrix.diagonal_apply_eq] using he
  · have he := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M 0 1) hR
    simpa only [CStarMatrix.mul_apply,CStarMatrix.conjTranspose_apply,Fin.sum_univ_one,
      diagonalCopies,CStarMatrix.ofMatrix_apply,Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1)] using he
  · have hm := map_mem_hereditary (matrixSingletonHom (A := A))
      (diagonalCopies_nonneg 1 hh).isSelfAdjoint hRher
    change (R*R.conjTranspose) 0 0 ∈ hereditarySubalgebra h hh.isSelfAdjoint at hm
    simpa only [CStarMatrix.mul_apply,CStarMatrix.conjTranspose_apply,Fin.sum_univ_two] using hm

lemma norm_spectralRamp_le_one {B : Type*} [NonUnitalCStarAlgebra B]
    (h : B) (δ : ℝ) : ‖cfcₙ (spectralRamp δ) h‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro t _
  rw [Real.norm_eq_abs,abs_of_nonneg (spectralRamp_nonneg δ t)]
  exact spectralRamp_le_one δ t

lemma norm_spectralRamp_eq_one {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {h : B} (hh : 0 ≤ h) {δ : ℝ} (hδ : 0 < δ) (hn : 2*δ ≤ ‖h‖) :
    ‖cfcₙ (spectralRamp δ) h‖=1 := by
  have hz : h ≠ 0 := by intro hz; rw [hz,norm_zero] at hn; linarith
  let : Nontrivial B := nontrivial_of_ne h 0 hz
  apply le_antisymm (norm_spectralRamp_le_one h δ)
  have he := norm_apply_le_norm_cfcₙ (spectralRamp δ) h
    (spectrum_subset_quasispectrum ℝ h (CStarAlgebra.norm_mem_spectrum_of_nonneg h hh))
    (continuous_spectralRamp δ).continuousOn (spectralRamp_eq_zero hδ hδ.le) hh.isSelfAdjoint
  simpa only [spectralRamp_eq_one hδ hn,norm_one] using he

lemma exists_two_orthogonal_cores {h : A} (hh : 0 ≤ h)
    (hpi : ProperlyInfinite (diagonalCopies 1 h)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e f : A,0 ≤ e ∧ 0 ≤ f ∧ ‖e‖ ≤ 1 ∧ ‖f‖ ≤ 1 ∧ e*f=0 ∧
      e ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧
      f ∈ hereditarySubalgebra h hh.isSelfAdjoint ∧
      ∀ (H : ComplexHilbert) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        2*δ ≤ ‖π h‖ → ‖π e‖=1 ∧ ‖π f‖=1 := by
  obtain ⟨r,s,hr,hs,hrs,hm⟩ := exists_two_exact_core_columns hh hpi hδ
  let e := r*star r
  let f := s*star s
  have he : 0 ≤ e := mul_star_self_nonneg r
  have hf : 0 ≤ f := mul_star_self_nonneg s
  have heN : ‖e‖ ≤ 1 := by
    rw [show e=r*star r from rfl,CStarRing.norm_self_mul_star,← CStarRing.norm_star_mul_self (x := r),hr]
    exact norm_spectralRamp_le_one h δ
  have hfN : ‖f‖ ≤ 1 := by
    rw [show f=s*star s from rfl,CStarRing.norm_self_mul_star,← CStarRing.norm_star_mul_self (x := s),hs]
    exact norm_spectralRamp_le_one h δ
  have hef : e*f=0 := by
    change (r*star r)*(s*star s)=0
    rw [mul_assoc,← mul_assoc (star r),hrs,zero_mul,mul_zero]
  have hem : e ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
    exact hereditarySubalgebra_le_of_mem (hereditarySubalgebra_inner h hh.isSelfAdjoint)
      (add_nonneg he hf).isSelfAdjoint hm (mem_hereditary_of_le (e+f) e (add_nonneg he hf) he (le_add_of_nonneg_right hf))
  have hfm : f ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
    exact hereditarySubalgebra_le_of_mem (hereditarySubalgebra_inner h hh.isSelfAdjoint)
      (add_nonneg he hf).isSelfAdjoint hm (mem_hereditary_of_le (e+f) f (add_nonneg he hf) hf (le_add_of_nonneg_left he))
  refine ⟨e,f,he,hf,heN,hfN,hef,hem,hfm,?_⟩
  intro H π hn
  have hp : 0 ≤ π h := map_nonneg π hh
  have hc : π (cfcₙ (spectralRamp δ) h)=cfcₙ (spectralRamp δ) (π h) :=
    π.map_cfcₙ _ _ (continuous_spectralRamp δ).continuousOn (spectralRamp_eq_zero hδ hδ.le)
      (by fun_prop) hh.isSelfAdjoint hp.isSelfAdjoint
  have hnr : ‖π e‖=‖π (cfcₙ (spectralRamp δ) h)‖ := by
    rw [← hr,map_mul,map_mul,map_star,CStarRing.norm_self_mul_star,CStarRing.norm_star_mul_self]
  have hns : ‖π f‖=‖π (cfcₙ (spectralRamp δ) h)‖ := by
    rw [← hs,map_mul,map_mul,map_star,CStarRing.norm_self_mul_star,CStarRing.norm_star_mul_self]
  rw [hc,norm_spectralRamp_eq_one hp hδ hn] at hnr hns
  exact ⟨hnr,hns⟩

end

end

end WeakPureInfiniteness
end

end OAI
