import OAI.Dynamics.StandardMap.TerminalShortfall

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical ENNReal
namespace StandardMapEntropy
lemma dyadicMid_zero_two : dyadicMid 0 (dyadicInt 2)=dyadicInt 1 := by
  apply Subtype.ext; norm_num
noncomputable def capG (α : ℝ) (d : DistanceArray) : ℝ :=
  entropyCap α (arrayShortfall 0 (dyadicInt 2) d)-
    (entropyCap α (arrayShortfall 0 (dyadicInt 1) d)+entropyCap α (arrayShortfall (dyadicInt 1) (dyadicInt 2) d))/2
noncomputable def coreTestIndex : ArrayTestIndex := ⟨(0,dyadicInt 2),by norm_num⟩
lemma continuous_capG (α : ℝ) : Continuous (capG α) := by
  unfold capG
  exact ((entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _)).sub
    ((((entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _)).add
      ((entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _))).div_const 2)
lemma shortfall_ambient_mem (d : DistanceArray) (s t : DyadicTime) (hst : 1≤(t:ℝ)-(s:ℝ)) :
    arrayShortfall s t d∈Icc (-2:ℝ) 1 := by
  have hlen : 0<(t:ℝ)-(s:ℝ) := by linarith
  have hh := d.property.2.2.2.2 s t
  rw [abs_of_pos hlen] at hh
  have hl : d.val s t/((t:ℝ)-(s:ℝ))≤3 := (div_le_iff₀ hlen).mpr (by linarith)
  have hu := div_nonneg (d.property.1 s t) hlen.le
  unfold arrayShortfall
  constructor <;> linarith
lemma capG_bound (α : ℝ) : ∃C≥0,∀d:DistanceArray,|capG α d|≤C*arrayTest coreTestIndex d := by
  obtain ⟨C,hC,h1,h2⟩ := c2_compact_bounds (entropyCap_contDiff α) (-2) 1
  refine ⟨C,hC,?_⟩
  intro d
  have hm := arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) d
  simp only [arrayJ,dyadicMid_zero_two] at hm
  have hh := c2_capped_difference (entropyCap_contDiff α) hC h1 h2
    (shortfall_ambient_mem d 0 (dyadicInt 1) (by norm_num))
    (shortfall_ambient_mem d (dyadicInt 1) (dyadicInt 2) (by norm_num))
    (shortfall_ambient_mem d 0 (dyadicInt 2) (by norm_num)) hm
  simpa only [capG,arrayTest,coreTestIndex,arrayJ,arrayV,dyadicMid_zero_two] using hh
lemma capG_affine (α : ℝ) (w : Icc (0:ℝ) 1) : capG α (affineArray w)=0 := by
  have hh (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) : arrayShortfall s t (affineArray w)=1-w.val := by
    change 1-w.val*|(t:ℝ)-(s:ℝ)|/((t:ℝ)-(s:ℝ))=1-w.val
    rw [abs_of_pos (sub_pos.mpr hst),mul_div_cancel_right₀ _ (sub_ne_zero.mpr hst.ne')]
  unfold capG
  rw [hh _ _ (by norm_num),hh _ _ (by norm_num),hh _ _ (by norm_num)]
  ring
lemma capG_slow {α : ℝ} {d : DistanceArray}
    (h : ∀s t:DyadicTime,d.val s t≤(999/1000)*|(t:ℝ)-(s:ℝ)|) : capG α d=0 := by
  have hh (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) : entropyCap α (arrayShortfall s t d)=1 := by
    apply entropyCap_one
    have hs := h s t
    rw [abs_of_pos (sub_pos.mpr hst)] at hs
    have he := (div_le_iff₀ (sub_pos.mpr hst)).mpr hs
    unfold arrayShortfall
    linarith
  unfold capG
  rw [hh _ _ (by norm_num),hh _ _ (by norm_num),hh _ _ (by norm_num)]
  norm_num
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma capG_integrable_multi (α : ℝ) : Integrable (fun d : NonAffineArray => capG α d.val) L.multi := by
  obtain ⟨C,hC,hb⟩ := capG_bound α
  exact ((S.test_integrable_multi L coreTestIndex).const_mul C).mono'
    ((continuous_capG α).comp continuous_subtype_val).aestronglyMeasurable
    (Eventually.of_forall (fun d => by simpa only [Real.norm_eq_abs] using hb d.val))
lemma capG_integrable_remainder (α : ℝ) : Integrable (fun d : NonAffineArray => capG α d.val) (S.remainderLaw L) :=
  (S.capG_integrable_multi L α).mono_measure (S.remainder_le L)
lemma capG_integrable_sum (α : ℝ) : Integrable (fun d : NonAffineArray => capG α d.val) (S.backwardSum L) :=
  (S.capG_integrable_multi L α).mono_measure (S.backwardSum_le L)
lemma capG_integral_decomposition (α : ℝ) :
    (∫d:NonAffineArray,capG α d.val ∂L.multi)=
    (∫d:NonAffineArray,capG α d.val ∂S.remainderLaw L)+
      ∑'j:ℕ,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1) := by
  conv_lhs => rw [←S.backward_decomposition L]
  rw [integral_add_measure (S.capG_integrable_remainder L α) (S.capG_integrable_sum L α)]
  congr 1
  exact integral_sum_measure (S.capG_integrable_sum L α)
lemma capG_backward_absolutely_summable (α : ℝ) :
    Summable (fun j:ℕ => ∫d:NonAffineArray,|capG α d.val| ∂S.backwardLaw L (j+1)) :=
  (hasSum_integral_measure (S.capG_integrable_sum L α).abs).summable
end CriticalScaleSequence
end StandardMapEntropy

end OAI
