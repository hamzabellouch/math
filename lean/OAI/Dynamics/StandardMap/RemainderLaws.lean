import OAI.Dynamics.StandardMap.ShapeLimit

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma arrayTranslate_unit (r : DyadicTime) (d : DistanceArray) (hu : UnitArray d) : UnitArray (arrayTranslate r d) := by
  intro s t
  change d.val (s+r) (t+r)≤|(t:ℝ)-(s:ℝ)|
  have hh := hu (s+r) (t+r)
  change d.val (s+r) (t+r)≤|((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ))| at hh
  simpa only [add_sub_add_right_eq_sub] using hh
lemma dyadicHalf_add (s t : DyadicTime) : dyadicHalf (s+t)=dyadicHalf s+dyadicHalf t := by
  apply Subtype.ext; change ((s:ℝ)+(t:ℝ))/2=(s:ℝ)/2+(t:ℝ)/2; ring
lemma half_translate (r : DyadicTime) (d : NonAffineArray) (hu : UnitArray d.val) :
    nonaffineTranslation r (nonaffineHalf d)=nonaffineHalf (nonaffineTranslation (dyadicHalf r) d) := by
  have hu' : UnitArray (nonaffineTranslation (dyadicHalf r) d).val := arrayTranslate_unit _ _ hu
  rw [nonaffineHalf,dite_eq_left hu,nonaffineHalf,dite_eq_left hu']
  apply Subtype.ext; apply Subtype.ext; funext s t
  change 2*d.val.val (dyadicHalf (s+r)) (dyadicHalf (t+r))=
    2*d.val.val (dyadicHalf s+dyadicHalf r) (dyadicHalf t+dyadicHalf r)
  rw [dyadicHalf_add,dyadicHalf_add]
lemma unit_half_map (μ : Measure NonAffineArray) (hu : ∀ᵐd ∂μ,UnitArray d.val) :
    ∀ᵐd ∂μ.map nonaffineHalf,UnitArray d.val := by
  apply (ae_map_iff measurable_nonaffineHalf.aemeasurable
    ((isClosed_unitArray.preimage continuous_subtype_val).measurableSet)).mpr
  exact hu.mono (fun d hd => nonaffineHalf_unit d hd)
lemma half_map_translation_invariant (μ : Measure NonAffineArray) (hu : ∀ᵐd ∂μ,UnitArray d.val)
    (ht : ∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r : DyadicTime) :
    (μ.map nonaffineHalf).map (nonaffineTranslation r)=μ.map nonaffineHalf := by
  rw [Measure.map_map (nonaffineTranslation r).continuous.measurable measurable_nonaffineHalf]
  calc
    μ.map (nonaffineTranslation r ∘ nonaffineHalf)=μ.map (nonaffineHalf ∘ nonaffineTranslation (dyadicHalf r)) :=
      Measure.map_congr (hu.mono (fun d hd => half_translate r d hd))
    _=(μ.map (nonaffineTranslation (dyadicHalf r))).map nonaffineHalf := by
      rw [Measure.map_map measurable_nonaffineHalf (nonaffineTranslation _).continuous.measurable]
    _=μ.map nonaffineHalf := by rw [ht]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
noncomputable def backwardLaw (n : ℕ) : Measure NonAffineArray := L.terminal.map (nonaffineHalf^[n])
noncomputable def backwardSum : Measure NonAffineArray := Measure.sum (fun n : ℕ => S.backwardLaw L (n+1))
noncomputable def remainderLaw : Measure NonAffineArray := L.multi-S.backwardSum L
lemma backwardLaw_zero : S.backwardLaw L 0=L.terminal := by simp [backwardLaw]
lemma backwardLaw_succ (n : ℕ) : S.backwardLaw L (n+1)=(S.backwardLaw L n).map nonaffineHalf :=
  (map_iterate_succ L.terminal nonaffineHalf measurable_nonaffineHalf n).symm
lemma backwardLaw_unit (n : ℕ) : ∀ᵐd ∂S.backwardLaw L n,UnitArray d.val := by
  induction n with
  | zero => rw [S.backwardLaw_zero L]; exact S.unit_aeterminal L
  | succ n ih => rw [S.backwardLaw_succ L]; exact unit_half_map _ ih
lemma backwardLaw_translate (n : ℕ) (r : DyadicTime) : (S.backwardLaw L n).map (nonaffineTranslation r)=S.backwardLaw L n := by
  induction n generalizing r with
  | zero => rw [S.backwardLaw_zero L]; exact S.terminal_translate L r
  | succ n ih => rw [S.backwardLaw_succ L]; exact half_map_translation_invariant _ (S.backwardLaw_unit L n) ih r
lemma backwardSum_le : S.backwardSum L≤L.multi := renewal_sum_le _ _ _ measurable_nonaffineHalf (S.half_balance L)
lemma remainder_le : S.remainderLaw L≤L.multi := Measure.sub_le
lemma backwardSum_translate (r : DyadicTime) : (S.backwardSum L).map (nonaffineTranslation r)=S.backwardSum L := by
  rw [backwardSum,Measure.map_sum (nonaffineTranslation r).continuous.measurable.aemeasurable]
  congr 1; funext n; exact S.backwardLaw_translate L (n+1) r
lemma backward_decomposition : S.remainderLaw L+S.backwardSum L=L.multi := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  have : SigmaFinite (S.backwardSum L) := Measure.sigmaFinite_of_le L.multi (S.backwardSum_le L)
  exact sub_add_cancel_sigma L.multi (S.backwardSum L) (S.backwardSum_le L)
lemma remainder_unit : ∀ᵐd ∂S.remainderLaw L,UnitArray d.val := ae_mono (S.remainder_le L) (S.unit_aemulti L)
lemma remainder_half : (S.remainderLaw L).map nonaffineHalf=S.remainderLaw L := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  exact renewal_remainder_invariant _ _ _ measurable_nonaffineHalf (S.half_balance L)
lemma remainder_dilate : (S.remainderLaw L).map nonaffineDilate=S.remainderLaw L := by
  have hh := congrArg (fun μ : Measure NonAffineArray => μ.map nonaffineDilate) (S.remainder_half L)
  rw [map_dilate_half _ (S.remainder_unit L)] at hh
  exact hh.symm
lemma remainder_translate (r : DyadicTime) : (S.remainderLaw L).map (nonaffineTranslation r)=S.remainderLaw L := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  have : SigmaFinite (S.backwardSum L) := Measure.sigmaFinite_of_le L.multi (S.backwardSum_le L)
  apply (Measure.add_left_inj (S.backwardSum L) _ _).mp
  calc
    (S.remainderLaw L).map (nonaffineTranslation r)+S.backwardSum L=
        (S.remainderLaw L+S.backwardSum L).map (nonaffineTranslation r) := by
      rw [Measure.map_add _ _ (nonaffineTranslation r).continuous.measurable,S.backwardSum_translate L r]
    _=L.multi := by rw [S.backward_decomposition L,S.multi_translate L r]
    _=S.remainderLaw L+S.backwardSum L := (S.backward_decomposition L).symm
lemma remainder_shape : ∀ᵐd ∂S.remainderLaw L,SlowShape (realArray d.val) (999/1000) :=
  ae_mono (S.remainder_le L) (S.shape_aemulti L)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
