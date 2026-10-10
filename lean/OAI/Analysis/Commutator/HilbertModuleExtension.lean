import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry15

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ENNReal

open ContinuousLinearMap

namespace Kadison.HilbertModuleExtension

variable {ι E F K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (V : ι → E →ₗᵢ[ℂ] K) (W : ι → F →ₗᵢ[ℂ] H)
  (hV : IsHilbertSum ℂ (fun _ : ι => E) V) (hW : IsHilbertSum ℂ (fun _ : ι => F) W)

def extend (T : E →L[ℂ] F) : K →L[ℂ] H :=
  hW.linearIsometryEquiv.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)).comp
      hV.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap)

omit [CompleteSpace E] [CompleteSpace F] in
lemma extend_norm_le (T : E →L[ℂ] F) : ‖extend V W hV hW T‖ ≤ ‖T‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖hW.linearIsometryEquiv.symm
    (lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)
      (hV.linearIsometryEquiv x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)).le_of_opNorm_le
    (lp.norm_mapCLM_le 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)) _).trans_eq
      (by rw [LinearIsometryEquiv.norm_map])

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma extend_insert (T : E →L[ℂ] F) (i : ι) (x : E) :
    extend V W hV hW T (V i x)=W i (T x) := by
  classical
  change hW.linearIsometryEquiv.symm
    (lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)
      (hV.linearIsometryEquiv (V i x))) = _
  rw [←hV.linearIsometryEquiv_symm_apply_single x,LinearIsometryEquiv.apply_symm_apply]
  have h : lp.mapCLM 2 (fun _ : ι => T) (norm_nonneg T) (fun _ => le_rfl)
      (lp.single 2 i x)=lp.single 2 i (T x) := by
    ext j
    by_cases hji : j=i
    · subst j; simp
    · simp [lp.single_apply,Pi.single_eq_of_ne hji]
  rw [h,hW.linearIsometryEquiv_symm_apply_single]

omit [CompleteSpace E] [CompleteSpace F] in
lemma extend_sub (T R : E →L[ℂ] F) :
    extend V W hV hW (T-R)=extend V W hV hW T-extend V W hV hW R := by
  apply ActualHilbertSum.map_ext (fun _ : ι => E) V hV
  intro i
  ext x
  simp only [comp_apply,ActualHilbertSum.insert,LinearIsometry.coe_toContinuousLinearMap,
    extend_insert,sub_apply,map_sub]

include hV hW in
omit [CompleteSpace E] [CompleteSpace F] in
lemma eq_extend (G : K →L[ℂ] H) (T : E →L[ℂ] F)
    (h : ∀ i x, G (V i x)=W i (T x)) : G=extend V W hV hW T := by
  apply ActualHilbertSum.map_ext (fun _ : ι => E) V hV
  intro i
  ext x
  exact (h i x).trans (extend_insert V W hV hW T i x).symm

include hV hW in
omit [CompleteSpace E] [CompleteSpace F] in
lemma norm_sub_extend_le (G : K →L[ℂ] H) (T R : E →L[ℂ] F)
    (h : ∀ i x, G (V i x)=W i (R x)) :
    ‖G-extend V W hV hW T‖ ≤ ‖R-T‖ := by
  rw [eq_extend V W hV hW G R h,←extend_sub]
  exact extend_norm_le V W hV hW (R-T)

lemma project_extend (T : E →L[ℂ] F) (i : ι) (x : K) :
    ActualHilbertSum.project (fun _ : ι => F) W i (extend V W hV hW T x) =
      T (ActualHilbertSum.project (fun _ : ι => E) V i x) := by
  rw [ActualHilbertSum.project_coordinates _ W hW,ActualHilbertSum.project_coordinates _ V hV]
  change (hW.linearIsometryEquiv (hW.linearIsometryEquiv.symm _)) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma extend_intertwines (T : E →L[ℂ] F) (a : K →L[ℂ] K) (b : H →L[ℂ] H)
    (h : ∀ i j x,
      T (ActualHilbertSum.project (fun _ : ι => E) V i (a (V j x))) =
      ActualHilbertSum.project (fun _ : ι => F) W i (b (W j (T x)))) :
    (extend V W hV hW T).comp a=b.comp (extend V W hV hW T) := by
  apply ActualHilbertSum.map_ext (fun _ : ι => E) V hV
  intro j
  ext x
  apply ActualHilbertSum.ext_vectors (fun _ : ι => F) W hW
  intro i
  change ActualHilbertSum.project _ W i (extend V W hV hW T (a (V j x))) =
    ActualHilbertSum.project _ W i (b (extend V W hV hW T (V j x)))
  rw [project_extend,extend_insert]
  exact h i j x

end Kadison.HilbertModuleExtension

end

end
end

end OAI
