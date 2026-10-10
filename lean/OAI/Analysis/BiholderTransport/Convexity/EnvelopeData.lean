import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.NormalCoordinates3

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

abbrev EnvelopeData (E ι : Type*) := (E × (ι → E)) × ((ι → ℝ) × ℝ)

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {ι : Type*} [Fintype ι]

def scaledNormalEnvelope (a : M) (s : ℝ) (q : EnvelopeData (Model n) ι) (i : ι)
    (h : Model n) : ℝ :=
  (movingNormalCost a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) h -
    movingNormalCost a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) 0) -
  (q.2.2 / s) * (movingNormalCost a q.1.1 (s • q.1.2 i) h -
    movingNormalCost a q.1.1 (s • q.1.2 i) 0)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma scaledNormalEnvelope_zero (a : M) (s : ℝ) (q : EnvelopeData (Model n) ι) (i : ι) :
    scaledNormalEnvelope a s q i 0 = 0 := by simp [scaledNormalEnvelope]

lemma scaledNormalEnvelope_contDiffAt {a : M} {s : ℝ}
    {q : EnvelopeData (Model n) ι} (i : ι)
    (hb : q.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) ∈
          injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hi : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) (s • q.1.2 i) ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) :
    ContDiffAt ℝ ∞ (fun z : EnvelopeData (Model n) ι × Model n =>
      scaledNormalEnvelope a s z.1 i z.2) (q,0) := by
  have hmean : ContDiff ℝ ∞ (fun z : EnvelopeData (Model n) ι × Model n =>
      z.1.2.2 • ∑ j, z.1.2.1 j • z.1.1.2 j) := by fun_prop
  have hpi : ContDiff ℝ ∞ (fun z : EnvelopeData (Model n) ι × Model n =>
      s • z.1.1.2 i) := by fun_prop
  have hleft := movingNormalCost_contDiffAt hb hp
  have hright := movingNormalCost_contDiffAt hb hi
  exact ((hleft.comp (q,0) ((contDiffAt_fst.fst.fst.prodMk hmean.contDiffAt).prodMk contDiffAt_snd)).sub
    (hleft.comp (q,0) ((contDiffAt_fst.fst.fst.prodMk hmean.contDiffAt).prodMk contDiffAt_const))).sub
      ((contDiffAt_fst.snd.snd.div_const s).mul
        ((hright.comp (q,0) ((contDiffAt_fst.fst.fst.prodMk hpi.contDiffAt).prodMk contDiffAt_snd)).sub
          (hright.comp (q,0) ((contDiffAt_fst.fst.fst.prodMk hpi.contDiffAt).prodMk contDiffAt_const))))

lemma scaledNormalEnvelope_first {a : M} {s : ℝ} (hs : s ≠ 0)
    {q : EnvelopeData (Model n) ι} (i : ι)
    (hb : q.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) ∈
          injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hi : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) (s • q.1.2 i) ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) (v : Model n) :
    fderiv ℝ (scaledNormalEnvelope a s q i) 0 v =
      q.2.2 * inner ℝ
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
            (q.1.2 i - ∑ j, q.2.1 j • q.1.2 j))
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) v) := by
  have H := ((movingNormalCost_hasFDerivAt_zero hb hp).sub_const
      (movingNormalCost a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) 0)).sub
    (((movingNormalCost_hasFDerivAt_zero hb hi).sub_const
      (movingNormalCost a q.1.1 (s • q.1.2 i) 0)).const_smul (q.2.2 / s))
  simp only [Pi.sub_def,Pi.smul_def,smul_eq_mul] at H
  unfold scaledNormalEnvelope
  rw [H.fderiv]
  simp only [_root_.sub_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,map_smul,map_sub,inner_neg_left,real_inner_smul_left,inner_sub_left,smul_eq_mul]
  field_simp
  ring

lemma scaledNormalEnvelope_second {a : M} {s : ℝ}
    {q : EnvelopeData (Model n) ι} (i : ι)
    (hb : q.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) ∈
          injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hi : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) (s • q.1.2 i) ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) (v : Model n) :
    fderiv ℝ (fderiv ℝ (scaledNormalEnvelope a s q i)) 0 v v =
      hessianValue ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
            (q.2.2 • ∑ j, q.2.1 j • q.1.2 j))
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) v) -
      q.2.2 / s * hessianValue ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) (s • q.1.2 i))
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) v) := by
  have hl : ContDiffAt ℝ 2 (movingNormalCost a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j)) 0 :=
    ((movingNormalCost_contDiffAt hb hp).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hr : ContDiffAt ℝ 2 (movingNormalCost a q.1.1 (s • q.1.2 i)) 0 :=
    ((movingNormalCost_contDiffAt hb hi).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := second_fderiv_scaled_differences hl hr 1 (q.2.2 / s) v
  unfold scaledNormalEnvelope
  simpa only [one_mul,movingNormalCost_second hb hp,movingNormalCost_second hb hi] using H

end WeakMTWTransport

end

end OAI
