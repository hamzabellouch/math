import OAI.Dynamics.StandardMap.ArrayLimitSupport

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology Classical
namespace StandardMapEntropy
noncomputable def arrayHalf (d : DistanceArray) (hu : UnitArray d) : DistanceArray :=
  ⟨fun s t => 2*d.val (dyadicHalf s) (dyadicHalf t),by
    obtain ⟨h0,hs,hsy,ht,hb⟩ := d.property
    refine ⟨fun s t => mul_nonneg (by norm_num) (h0 _ _),?_,?_,?_,?_⟩
    · intro s; simp only [hs,mul_zero]
    · intro s t; dsimp only; rw [hsy]
    · intro s t u; have := ht (dyadicHalf s) (dyadicHalf t) (dyadicHalf u); dsimp only; linarith
    · intro s t
      have hh := hu (dyadicHalf s) (dyadicHalf t)
      change d.val (dyadicHalf s) (dyadicHalf t)≤|(t:ℝ)/2-(s:ℝ)/2| at hh
      rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      dsimp only; linarith⟩
lemma arrayHalf_unit (d : DistanceArray) (hu : UnitArray d) : UnitArray (arrayHalf d hu) := by
  intro s t
  have hh := hu (dyadicHalf s) (dyadicHalf t)
  change d.val (dyadicHalf s) (dyadicHalf t)≤|(t:ℝ)/2-(s:ℝ)/2| at hh
  rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  change 2*d.val (dyadicHalf s) (dyadicHalf t)≤|(t:ℝ)-(s:ℝ)|
  linarith
lemma arrayDilate_unit (d : DistanceArray) (hu : UnitArray d) : UnitArray (arrayDilate d) := by
  intro s t
  have hh := hu (s+s) (t+t)
  change d.val (s+s) (t+t)≤|((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))| at hh
  rw [show ((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))=2*((t:ℝ)-(s:ℝ)) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  change d.val (s+s) (t+t)/2≤|(t:ℝ)-(s:ℝ)|
  linarith
lemma arrayDilate_half (d : DistanceArray) (hu : UnitArray d) : arrayDilate (arrayHalf d hu)=d := by
  apply Subtype.ext; funext s t
  change (2*d.val (dyadicHalf (s+s)) (dyadicHalf (t+t)))/2=d.val s t
  rw [dyadicHalf_double,dyadicHalf_double]; ring
lemma arrayHalf_dilate (d : DistanceArray) (hu : UnitArray d) : arrayHalf (arrayDilate d) (arrayDilate_unit d hu)=d := by
  apply Subtype.ext; funext s t
  change 2*(d.val (dyadicHalf s+dyadicHalf s) (dyadicHalf t+dyadicHalf t)/2)=d.val s t
  rw [dyadicHalf_add_self,dyadicHalf_add_self]; ring
noncomputable def nonaffineHalfOn (d : {d : NonAffineArray // UnitArray d.val}) : NonAffineArray :=
  ⟨arrayHalf d.val.val d.property,by
    intro ha
    have hh := (arrayDilate_mem_affine_iff _).mpr ha
    rw [arrayDilate_half] at hh
    exact d.val.property hh⟩
lemma continuous_nonaffineHalfOn : Continuous nonaffineHalfOn := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact continuous_const.mul ((continuous_arrayEval (dyadicHalf s) (dyadicHalf t)).comp (continuous_subtype_val.comp continuous_subtype_val))
noncomputable def nonaffineHalf (d : NonAffineArray) : NonAffineArray :=
  if h : UnitArray d.val then nonaffineHalfOn ⟨d,h⟩ else d
lemma measurable_nonaffineHalf : Measurable nonaffineHalf := by
  exact continuous_nonaffineHalfOn.measurable.dite measurable_subtype_coe
    (isClosed_unitArray.preimage continuous_subtype_val).measurableSet
lemma nonaffineHalf_unit (d : NonAffineArray) (hu : UnitArray d.val) : UnitArray (nonaffineHalf d).val := by
  rw [nonaffineHalf,dite_eq_left hu]
  exact arrayHalf_unit d.val hu
lemma nonaffineDilate_half (d : NonAffineArray) (hu : UnitArray d.val) : nonaffineDilate (nonaffineHalf d)=d := by
  apply Subtype.ext
  rw [nonaffineHalf,dite_eq_left hu]
  exact arrayDilate_half d.val hu
lemma nonaffineHalf_dilate (d : NonAffineArray) (hu : UnitArray d.val) : nonaffineHalf (nonaffineDilate d)=d := by
  have hh : UnitArray (nonaffineDilate d).val := arrayDilate_unit d.val hu
  rw [nonaffineHalf,dite_eq_left hh]
  apply Subtype.ext
  exact arrayHalf_dilate d.val hu
lemma map_half_dilate (μ : Measure NonAffineArray) (hu : ∀ᵐ d ∂μ,UnitArray d.val) :
    (μ.map nonaffineDilate).map nonaffineHalf=μ := by
  rw [Measure.map_map measurable_nonaffineHalf continuous_nonaffineDilate.measurable]
  calc
    μ.map (nonaffineHalf ∘ nonaffineDilate)=μ.map id := Measure.map_congr (hu.mono (fun d hd => nonaffineHalf_dilate d hd))
    _=μ := Measure.map_id
lemma map_dilate_half (μ : Measure NonAffineArray) (hu : ∀ᵐ d ∂μ,UnitArray d.val) :
    (μ.map nonaffineHalf).map nonaffineDilate=μ := by
  rw [Measure.map_map continuous_nonaffineDilate.measurable measurable_nonaffineHalf]
  calc
    μ.map (nonaffineDilate ∘ nonaffineHalf)=μ.map id := Measure.map_congr (hu.mono (fun d hd => nonaffineDilate_half d hd))
    _=μ := Measure.map_id
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma half_balance : L.multi=L.multi.map nonaffineHalf+L.terminal.map nonaffineHalf := by
  have hh := congrArg (fun μ : Measure NonAffineArray => μ.map nonaffineHalf) (S.dilation_balance L)
  rw [map_half_dilate L.multi (S.unit_aemulti L),Measure.map_add] at hh <;> try exact measurable_nonaffineHalf
  exact hh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
