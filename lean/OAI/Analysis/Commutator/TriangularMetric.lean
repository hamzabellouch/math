import Mathlib
import OAI.Analysis.Commutator.RectangularColumn
import OAI.Analysis.Commutator.HilbertPair
import OAI.Analysis.Commutator.GramBounds
import OAI.Analysis.Commutator.FactorMetric

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.RectangularColumn

open HilbertPair CbFactor

variable {A K F E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance : NormedAddCommGroup (K →L[ℂ] F) := ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℂ (K →L[ℂ] F) := ContinuousLinearMap.toNormedSpace

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F))
  (D : A →L[ℂ] (K →L[ℂ] F))

lemma triangular_left (a : A) :
    (left F K).toContinuousLinearMap.adjoint.comp (triangularMap σ lam D a)=
      (lam a).comp (left F K).toContinuousLinearMap.adjoint+
        (D a).comp (right F K).toContinuousLinearMap.adjoint := by
  ext x
  simp [left_adjoint,right_adjoint]

lemma triangular_right (a : A) :
    (right F K).toContinuousLinearMap.adjoint.comp (triangularMap σ lam D a)=
      (σ a).comp (right F K).toContinuousLinearMap.adjoint := by
  ext x
  simp [right_adjoint]

lemma triangular_star_right (a : A) :
    (star (triangularMap σ lam D (star a))).comp (right F K).toContinuousLinearMap=
      (right F K).toContinuousLinearMap.comp (σ a) := by
  have h := congrArg ContinuousLinearMap.adjoint (triangular_right σ lam D (star a))
  simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    map_star,ContinuousLinearMap.star_eq_adjoint] using h

variable (L : E →L[ℂ] SumHilbert F K) (W : SumHilbert F K →L[ℂ] E)
  (hLW : L.comp W=1)
  (hcov : ∀ a : A,triangularMap σ lam D a*(L.comp L.adjoint)=
    (L.comp L.adjoint)*star (triangularMap σ lam D (star a)))

abbrev lowerFactor := (right F K).toContinuousLinearMap.adjoint.comp L

abbrev lowerRight := W.comp (right F K).toContinuousLinearMap

omit [CompleteSpace E] in
include hLW in
lemma lowerFactor_right : (lowerFactor L).comp (lowerRight W)=1 := by
  simp only [lowerFactor,lowerRight,ContinuousLinearMap.comp_assoc]
  rw [←ContinuousLinearMap.comp_assoc L,hLW]
  simp [ContinuousLinearMap.one_def]

abbrev metricLower := (lowerFactor L).comp (lowerFactor L).adjoint

abbrev metricUpperRight := (left F K).toContinuousLinearMap.adjoint.comp
    ((L.comp L.adjoint).comp (right F K).toContinuousLinearMap)

lemma metricLower_eq : metricLower L=(right F K).toContinuousLinearMap.adjoint.comp
    ((L.comp L.adjoint).comp (right F K).toContinuousLinearMap) := by
  simp only [metricLower,lowerFactor,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.comp_assoc]

include hcov in
lemma metricLower_commutes (a : A) : σ a*metricLower L=metricLower L*σ a := by
  have h := congrArg (fun T : SumHilbert F K →L[ℂ] SumHilbert F K =>
    (right F K).toContinuousLinearMap.adjoint.comp (T.comp (right F K).toContinuousLinearMap)) (hcov a)
  change _=_ at h
  simp only [ContinuousLinearMap.mul_def,←ContinuousLinearMap.comp_assoc,
    triangular_right] at h
  simpa only [ContinuousLinearMap.comp_assoc,triangular_star_right,metricLower,lowerFactor,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc] using h

include hcov in
lemma metricUpperRight_equation (a : A) :
    (lam a).comp (metricUpperRight L)+(D a).comp (metricLower L)=
      (metricUpperRight L).comp (σ a) := by
  have h := congrArg (fun T : SumHilbert F K →L[ℂ] SumHilbert F K =>
    (left F K).toContinuousLinearMap.adjoint.comp (T.comp (right F K).toContinuousLinearMap)) (hcov a)
  simp only [ContinuousLinearMap.mul_def,←ContinuousLinearMap.comp_assoc,
    triangular_left,ContinuousLinearMap.add_comp] at h
  simpa only [ContinuousLinearMap.comp_assoc,triangular_star_right,metricLower,lowerFactor,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    metricUpperRight,ContinuousLinearMap.comp_assoc] using h

omit [CompleteSpace K] [CompleteSpace F] [CompleteSpace E] in
lemma lowerRight_norm_le {c : ℝ} (hc : 0≤c) (hW : ‖W‖≤c) : ‖lowerRight W‖≤c := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact (mul_le_mul hW (right F K).norm_toContinuousLinearMap_le
    (ContinuousLinearMap.opNorm_nonneg _) hc).trans_eq (mul_one c)

lemma metricUpperRight_norm_le (hL : ‖L‖≤1) : ‖metricUpperRight L‖≤1 := by
  have hJ1 : ‖(left F K).toContinuousLinearMap.adjoint‖≤1 := by
    simpa using (left F K).norm_toContinuousLinearMap_le
  have hJ2 : ‖(right F K).toContinuousLinearMap‖≤1 := (right F K).norm_toContinuousLinearMap_le
  have hLa : ‖L.adjoint‖≤1 := by simpa using hL
  have hQ : ‖L.comp L.adjoint‖≤1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hL hLa (ContinuousLinearMap.opNorm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hQJ : ‖(L.comp L.adjoint).comp (right F K).toContinuousLinearMap‖≤1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hQ hJ2 (ContinuousLinearMap.opNorm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hJ1 hQJ (ContinuousLinearMap.opNorm_nonneg _) zero_le_one).trans_eq (one_mul 1))

include hLW hcov in
theorem implementer_of_factor_metric {c : ℝ} (hc : 0≤c) (hL : ‖L‖≤1) (hW : ‖W‖≤c) :
    ∃ V : K →L[ℂ] F,‖V‖≤c^2 ∧ ∀ a : A,D a=V.comp (σ a)-(lam a).comp V := by
  have hlow := lowerFactor_right L W hLW
  have hpos := gram_strictlyPositive (lowerFactor L) (lowerRight W) hlow
  let u : (K →L[ℂ] K)ˣ := hpos.isUnit.unit
  have hu : (u : K →L[ℂ] K)=metricLower L := hpos.isUnit.unit_spec
  have hi : ‖(↑(u⁻¹) : K →L[ℂ] K)‖≤c^2 :=
    gram_inverse_norm_le (lowerFactor L) (lowerRight W) hlow hc
      (lowerRight_norm_le W hc hW) u hu
  let V : K →L[ℂ] F := (metricUpperRight L).comp (↑(u⁻¹) : K →L[ℂ] K)
  refine ⟨V,?_,?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (metricUpperRight_norm_le L hL) hi
        (ContinuousLinearMap.opNorm_nonneg _) zero_le_one).trans_eq (one_mul _))
  · intro a
    have hcomm : Commute (σ a) (u : K →L[ℂ] K) := by
      rw [hu]
      exact metricLower_commutes σ lam D L hcov a
    have hinv : (σ a)*(↑(u⁻¹) : K →L[ℂ] K)=(↑(u⁻¹) : K →L[ℂ] K)*(σ a) :=
      hcomm.units_inv_right.eq
    have he := congrArg (fun T : K →L[ℂ] F => T.comp (↑(u⁻¹) : K →L[ℂ] K))
      (metricUpperRight_equation σ lam D L hcov a)
    have hcancel : (metricLower L).comp (↑(u⁻¹) : K →L[ℂ] K)=1 := by
      rw [←hu]
      exact u.mul_inv
    rw [ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_assoc (D a) (metricLower L),hcancel,
      ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id] at he
    have hh : (σ a).comp (↑(u⁻¹) : K →L[ℂ] K)=(↑(u⁻¹) : K →L[ℂ] K).comp (σ a) := hinv
    rw [ContinuousLinearMap.comp_assoc (lam a) (metricUpperRight L),
      ContinuousLinearMap.comp_assoc (metricUpperRight L) (σ a),hh,
      ←ContinuousLinearMap.comp_assoc (metricUpperRight L)] at he
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he)

end Kadison.RectangularColumn

end

end
end

end OAI
