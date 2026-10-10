import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.MatrixComparison
import OAI.Analysis.JiangSu.MatrixAlgebras.ProjectionDefectRankUpper
import OAI.Analysis.JiangSu.Traces.SmallTracePeakIsometry

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open Pureness TraceCone
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma scalar_comparison_inr (hcone : AllDenselyFiniteTracesBounded A) (hcmp : StrictComparison hcone)
    (a b : A) (ha : 0≤a) (hb : 0≤b) (hb0 : b≠0)
    (hgap : ∀ τ : NormalizedTrace A,normalizedRootRank τ.unitized (Unitization.inr a)<
      normalizedRootRank τ.unitized (Unitization.inr b)) :
    CuntzSubequiv (Unitization.inr a : Unitization ℂ A) (Unitization.inr b) := by
  let aM : Positive (FinMatrix A 1) := ⟨scalarCorner 1 (le_refl 1) a,map_nonneg _ ha⟩
  let bM : Positive (FinMatrix A 1) := ⟨scalarCorner 1 (le_refl 1) b,map_nonneg _ hb⟩
  have hbM : matrixLimitStage 1 bM.1≠0 := by
    intro h
    apply hb0
    apply scalarCorner_injective 1 (le_refl 1)
    apply (matrixLimitStage_isometry 1).injective
    simpa only [map_zero] using h
  have hc := comparison_of_normalized_rank_lt hcone hcmp
    (Positive.map (matrixLimitStage 1) aM) (Positive.map (matrixLimitStage 1) bM) hbM (fun τ => by
      rw [τ.stabilized_rank_stage,τ.stabilized_rank_stage]
      change (τ.weight.matrixTrace (Fin 1)).rank aM < (τ.weight.matrixTrace (Fin 1)).rank bM
      rw [τ.matrix_rank_inr 1 aM,τ.matrix_rank_inr 1 bM]
      change matrixRank τ.unitized (finiteMatrixMap _ 1 (scalarCorner 1 (le_refl 1) a))<
        matrixRank τ.unitized (finiteMatrixMap _ 1 (scalarCorner 1 (le_refl 1) b))
      rw [inr_scalarCorner,inr_scalarCorner,DirectComparison.matrixRank_scalarCorner τ.unitized _ _ (Unitization.inr_nonneg_iff.mpr ha),
        DirectComparison.matrixRank_scalarCorner τ.unitized _ _ (Unitization.inr_nonneg_iff.mpr hb)]
      exact hgap τ)
  have hm := (hc.map (stabilizationInr (A := A))).map sharedMatrixEquiv.toNonUnitalStarAlgHom
  have he (w : Positive (FinMatrix A 1)) :
      sharedMatrixEquiv (stabilizationInr (matrixLimitStage 1 w.1))=
        completedMatrixInclude (Unitization ℂ A) 1 (finiteMatrixMap (Unitization.inrNonUnitalStarAlgHom ℂ A) 1 w.1) := by
    rw [stabilizationInr,stabilizationMap_stage,sharedMatrixEquiv_stage]
  have hp := (cuntzSubequiv_iff_shared _ _).mpr hm
  change CuntzSubequiv (sharedMatrixEquiv (stabilizationInr (matrixLimitStage 1 aM.1)))
    (sharedMatrixEquiv (stabilizationInr (matrixLimitStage 1 bM.1))) at hp
  rw [he aM,he bM] at hp
  have hm' := (cuntzSubequiv_completedMatrixInclude_iff _ 1 _ _).mp hp
  change CuntzSubequiv (finiteMatrixMap _ 1 (scalarCorner 1 (le_refl 1) a))
    (finiteMatrixMap _ 1 (scalarCorner 1 (le_refl 1) b)) at hm'
  rw [inr_scalarCorner,inr_scalarCorner] at hm'
  let E := scalarFinOneEquiv (A := Unitization ℂ A)
  have hE (x : Unitization ℂ A) : DirectComparison.scalarCorner (le_refl 1) x=E x := by
    simp only [DirectComparison.scalarCorner_apply,corner_refl,E]
  rw [hE,hE] at hm'
  apply (cuntzSubequiv_iff_sequence _ _).mpr
  obtain ⟨v,hv⟩ := (cuntzSubequiv_iff_sequence _ _).mp hm'
  refine ⟨fun n => E.symm (v n),?_⟩
  have ht := ((StarAlgEquiv.isometry E.symm).continuous.tendsto (E (Unitization.inr a))).comp hv
  simpa only [Function.comp_def,map_mul,map_star,StarAlgEquiv.symm_apply_apply] using ht

end NonunitalGamma

end
end

section

noncomputable section
namespace NonunitalGamma
open Pureness DirectComparison
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveCut_inr (a : A) (t : ℝ) (ht : 0≤t) :
    (Unitization.inr (cfcₙ (fun s : ℝ => max (s-t) 0) a) : Unitization ℂ A)=
      directPositiveCut t (Unitization.inr a) := by
  exact Unitization.real_cfcₙ_eq_cfc_inr a _ (by simp [ht])

 theorem projection_gap_isometry_inr [Nonempty (NormalizedTrace A)]
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : StrictComparison hcone)
    (e f : A) (he : 0≤e) (hen : ‖e‖≤1) (hf : 0≤f) (hfn : ‖f‖≤1)
    (α δ c ε : ℝ) (hα : 0<α) (hδ : 0<δ) (hδ1 : δ≤1)
    (hc : 0<c) (hε : 0<ε) (hε1 : ε≤1)
    (hgap : ∀ τ : NormalizedTrace A,(τ.functional e).re+c≤(τ.functional f).re)
    (hede : ∀ τ : NormalizedTrace A,(τ.functional (e-e*e)).re<α*c/3)
    (hfde : ∀ τ : NormalizedTrace A,(τ.functional (f-f*f)).re<δ*c/3) :
    ∃ s : Unitization ℂ A,‖s‖≤2 ∧ ‖star s*s-Unitization.inr e‖<ε+α ∧
      ‖Unitization.inr f*s-s‖≤2*δ := by
  let E : Unitization ℂ A := Unitization.inr e
  let F : Unitization ℂ A := Unitization.inr f
  have hE : 0≤E := Unitization.inr_nonneg_iff.mpr he
  have hF : 0≤F := Unitization.inr_nonneg_iff.mpr hf
  have hEn : ‖E‖≤1 := by simpa only [E,Unitization.norm_inr] using hen
  have hFn : ‖F‖≤1 := by simpa only [F,Unitization.norm_inr] using hfn
  let a : A := cfcₙ (fun s : ℝ => max (s-α) 0) e
  let b : A := cfcₙ (fun s : ℝ => max (s-(1-δ)) 0) f
  have haeq : (Unitization.inr a : Unitization ℂ A)=directPositiveCut α E := positiveCut_inr e α hα.le
  have hbeq : (Unitization.inr b : Unitization ℂ A)=directPositiveCut (1-δ) F := positiveCut_inr f (1-δ) (sub_nonneg.mpr hδ1)
  have ha : 0≤a := Unitization.inr_nonneg_iff.mp (haeq ▸ directPositiveCut_nonneg α E)
  have hb : 0≤b := Unitization.inr_nonneg_iff.mp (hbeq ▸ directPositiveCut_nonneg (1-δ) F)
  have hcmpgap (τ : NormalizedTrace A) : normalizedRootRank τ.unitized (Unitization.inr a)<normalizedRootRank τ.unitized (Unitization.inr b) := by
    rw [haeq,hbeq]
    apply (ENNReal.toReal_lt_toReal (directRank_ne_top _ _ (directPositiveCut_nonneg _ _))
      (directRank_ne_top _ _ (directPositiveCut_nonneg _ _))).mp
    have h1 := directPositiveCut_rank_le_trace_add_defect_div τ.unitized E hE hEn α hα
    have h2 := peak_cut_rank_lower τ.unitized F hF hFn δ hδ
    have hede' : (τ.unitized.functional (E-E*E)).re<α*c/3 := by
      simpa only [E,←Unitization.inr_mul,←Unitization.inr_sub,NormalizedTrace.unitized_inr] using hede τ
    have hfde' : (τ.unitized.functional (F-F*F)).re<δ*c/3 := by
      simpa only [F,←Unitization.inr_mul,←Unitization.inr_sub,NormalizedTrace.unitized_inr] using hfde τ
    have hs : (τ.unitized.functional (E-E*E)).re/α<c/3 := by
      apply (div_lt_iff₀ hα).mpr; nlinarith
    have hd : (τ.unitized.functional (F-F*F)).re/δ<c/3 := by
      apply (div_lt_iff₀ hδ).mpr; nlinarith
    have hg : (τ.unitized.functional E).re+c≤(τ.unitized.functional F).re := by
      simpa only [E,F,NormalizedTrace.unitized_inr] using hgap τ
    linarith
  have hb0 : b≠0 := by
    intro hz
    let τ : NormalizedTrace A := Classical.choice inferInstance
    have h := hcmpgap τ
    rw [hz,Unitization.inr_zero,normalizedRootRank_zero] at h
    exact not_lt_of_ge zero_le h
  have hab := scalar_comparison_inr hcone hcmp a b ha hb hb0 hcmpgap
  rw [haeq,hbeq] at hab
  obtain ⟨s,hsn,hsa,hfs⟩ := approximate_peak_isometry (directPositiveCut α E) F
    (norm_directPositiveCut_le_one E hE hEn α hα.le) hF hFn δ hδ.le hab ε hε hε1
  refine ⟨s,hsn,?_,hfs⟩
  have hec := norm_sub_directPositiveCut_le E hE α hα.le
  have ht := norm_sub_le_norm_sub_add_norm_sub (star s*s) (directPositiveCut α E) E
  rw [norm_sub_rev E (directPositiveCut α E)] at hec
  linarith

end NonunitalGamma

end
end

end OAI
