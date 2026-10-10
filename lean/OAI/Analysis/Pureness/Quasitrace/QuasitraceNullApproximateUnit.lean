import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientNorm
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

def nullSequenceStarAlgebra : NonUnitalStarSubalgebra ℂ (T.cauchySequenceAlgebra hadd) where
  carrier := T.nullSequenceIdeal hadd
  zero_mem' := (T.nullSequenceIdeal hadd).zero_mem
  add_mem' := (T.nullSequenceIdeal hadd).add_mem
  mul_mem' {u v} _ hv := (T.nullSequenceIdeal hadd).mul_mem_left u v hv
  smul_mem' c u hu := by
    change c • u ∈ T.nullSequenceIdeal hadd
    rw [Algebra.smul_def]
    exact (T.nullSequenceIdeal hadd).mul_mem_left (algebraMap ℂ _ c) u hu
  star_mem' := T.nullSequenceIdeal_star hadd

instance nullSequenceStarAlgebraCompleteSpace : CompleteSpace (T.nullSequenceStarAlgebra hadd) :=
  (T.nullSequenceIdeal_isClosed hadd).completeSpace_coe
instance nullSequenceStarAlgebraCStar : NonUnitalCStarAlgebra (T.nullSequenceStarAlgebra hadd) where
  norm_mul_self_le u := CStarRing.norm_mul_self_le u.1

instance cauchySequencePartialOrder : PartialOrder (T.cauchySequenceAlgebra hadd) :=
  CStarAlgebra.spectralOrder _
instance cauchySequenceStarOrderedRing : StarOrderedRing (T.cauchySequenceAlgebra hadd) :=
  CStarAlgebra.spectralOrderedRing _
instance nullSequencePartialOrder : PartialOrder (T.nullSequenceStarAlgebra hadd) :=
  CStarAlgebra.spectralOrder _
instance nullSequenceStarOrderedRing : StarOrderedRing (T.nullSequenceStarAlgebra hadd) :=
  CStarAlgebra.spectralOrderedRing _

local instance nullSequenceSpectralLE : LE (T.nullSequenceStarAlgebra hadd) :=
  (T.nullSequencePartialOrder hadd).toLE
local instance nullSequenceSpectralPreorder : Preorder (T.nullSequenceStarAlgebra hadd) :=
  (T.nullSequencePartialOrder hadd).toPreorder

def nullSequenceInclusion : T.nullSequenceStarAlgebra hadd →⋆ₙₐ[ℂ] T.cauchySequenceAlgebra hadd where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma nullSequenceInclusion_nonneg {e : T.nullSequenceStarAlgebra hadd} (he : 0 ≤ e) :
    0 ≤ (e : T.cauchySequenceAlgebra hadd) :=
  by
    have hs : star (CFC.sqrt e)*CFC.sqrt e = e := by
      rw [(CFC.sqrt_nonneg e).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self e he]
    have hs' := congrArg Subtype.val hs
    rw [← hs']
    exact star_mul_self_nonneg _

lemma cauchySequence_norm_one_sub {e : T.cauchySequenceAlgebra hadd} (he : 0 ≤ e) (hn : ‖e‖ ≤ 1) :
    ‖1-e‖ ≤ 1 := by
  have he1 : e ≤ 1 := by
    simpa using (CStarAlgebra.norm_le_iff_le_algebraMap e (by norm_num : (0:ℝ) ≤ 1) he).mp hn
  rw [CStarAlgebra.norm_le_iff_le_algebraMap (1-e) (by norm_num : (0:ℝ) ≤ 1) (sub_nonneg.mpr he1)]
  simpa using sub_le_self (1 : T.cauchySequenceAlgebra hadd) he

lemma exists_null_contraction {w : T.cauchySequenceAlgebra hadd} (hw : w ∈ T.nullSequenceIdeal hadd)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : T.cauchySequenceAlgebra hadd, e ∈ T.nullSequenceIdeal hadd ∧ IsSelfAdjoint e ∧
      ‖1-e‖ ≤ 1 ∧ ‖w*(1-e)‖ < ε := by
  let W : T.nullSequenceStarAlgebra hadd := ⟨w,hw⟩
  have hl := CStarAlgebra.increasingApproximateUnit (T.nullSequenceStarAlgebra hadd)
  have ht := hl.tendsto_mul_left W
  have heps := (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨e,hp,hn,hm⟩ := (hl.eventually_nonneg.and (hl.eventually_norm.and heps)).exists
  refine ⟨e.1,e.2,?_,T.cauchySequence_norm_one_sub hadd (T.nullSequenceInclusion_nonneg hadd hp) hn,?_⟩
  · exact congrArg Subtype.val hp.isSelfAdjoint
  · change dist (W*e) W < ε at hm
    rw [dist_eq_norm] at hm
    change ‖w*e.1-w‖ < ε at hm
    simpa only [mul_sub,mul_one,← neg_sub (w*e.1) w,norm_neg] using hm
end CuntzPureness.PositiveQuasitrace

end

end OAI
