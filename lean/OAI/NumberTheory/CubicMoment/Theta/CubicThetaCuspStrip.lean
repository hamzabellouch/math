import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspSeparation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTorusModes
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalQuotientMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! A half-open three-Eisenstein period cell gives a genuinely injective
high cusp strip in the arithmetic quotient. Boundary points retain their
unique representatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPeriodCoordinates (z : ℂ) : Fin 2 → ℝ :=
  eisensteinRealCoords.symm (z/3)

lemma cubicThetaPeriodCoordinates_continuous : Continuous cubicThetaPeriodCoordinates :=
  eisensteinRealCoords.symm.continuous.comp (continuous_id.div_const 3)

lemma cubicThetaPeriodCoordinates_translate (z : ℂ) (w : Eisenstein) :
    cubicThetaPeriodCoordinates (z+3*(w:ℂ))=
      cubicThetaPeriodCoordinates z+fun i => ((coordinatesEquiv.symm w) i:ℝ) := by
  have hw : (w:ℂ)=eisensteinRealCoords (fun i => ((coordinatesEquiv.symm w) i:ℝ)) := by
    rw [eisensteinRealCoords_integer]
    change (w:ℂ)=(coordinatesEquiv (coordinatesEquiv.symm w):ℂ)
    rw [LinearEquiv.apply_symm_apply]
  unfold cubicThetaPeriodCoordinates
  rw [show (z+3*(w:ℂ))/3=z/3+(w:ℂ) by ring,map_add,hw,
    ContinuousLinearEquiv.symm_apply_apply]

lemma cubicThetaPeriodCoordinates_injective : Function.Injective cubicThetaPeriodCoordinates := by
  intro z w h
  have h' := eisensteinRealCoords.symm.injective h
  exact (div_left_inj' (by norm_num : (3:ℂ)≠0)).mp h'

def cubicThetaCuspStrip (H : ℝ) : Set CubicThetaPoint :=
  {p | H<(cubicThetaPointCoordinates p).2 ∧
    ∀ i, cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1 i∈Ico (0:ℝ) 1}

lemma cubicThetaCuspStrip_measurable (H : ℝ) : MeasurableSet (cubicThetaCuspStrip H) := by
  have hc : Continuous cubicThetaPointCoordinates := continuous_subtype_val
  have hv : Measurable (fun p : CubicThetaPoint => (cubicThetaPointCoordinates p).2) :=
    (continuous_snd.comp hc).measurable
  have hx (i : Fin 2) : Measurable (fun p : CubicThetaPoint =>
      cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1 i) :=
    ((continuous_apply i).comp
      (cubicThetaPeriodCoordinates_continuous.comp (continuous_fst.comp hc))).measurable
  have hall : MeasurableSet {p : CubicThetaPoint | ∀ i,
      cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1 i∈Ico (0:ℝ) 1} := by
    convert MeasurableSet.iInter (fun i =>
      (measurableSet_Ico : MeasurableSet (Ico (0:ℝ) 1)).preimage (hx i)) using 1
    ext p
    simp only [mem_iInter,mem_preimage,mem_ofPred_eq]
  exact (measurableSet_Ioi.preimage hv).inter hall

private lemma halfOpen_integer_unique {x y : ℝ} {n : ℤ}
    (hx : x∈Ico (0:ℝ) 1) (hy : y∈Ico (0:ℝ) 1) (he : x=y+n) : x=y := by
  have hlow : (-1:ℝ)<(n:ℝ) := by linarith [hx.1,hy.2]
  have hhigh : (n:ℝ)<1 := by linarith [hx.2,hy.1]
  have hlow' : (-1:ℤ)<n := by exact_mod_cast hlow
  have hhigh' : n<1 := by exact_mod_cast hhigh
  have hn : n=0 := by omega
  simpa only [hn,Int.cast_zero,add_zero] using he

theorem cubicThetaCuspStrip_injective {H : ℝ} (hH : 1≤H) :
    InjOn cubicThetaQuotientMap (cubicThetaCuspStrip H) := by
  intro p hp q hq he
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  change g • q=p at hg
  have hp' : 1<p.val.2 := lt_of_le_of_lt hH hp.1
  have hq' : 1<q.val.2 := lt_of_le_of_lt hH hq.1
  have hgp : 1<(g • q).val.2 := by
    change 1<(cubicThetaPointCoordinates (g • q)).2
    rw [hg]
    exact hp'
  obtain ⟨w,hw⟩ := cubicThetaPrincipal_high_translation g hq' hgp
  change cubicThetaPointCoordinates (g • q)=(q.val.1+3*(w:ℂ),q.val.2) at hw
  rw [hg] at hw
  have hz : (cubicThetaPointCoordinates p).1=(cubicThetaPointCoordinates q).1+3*(w:ℂ) :=
    congrArg Prod.fst hw
  have hc : cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1=
      cubicThetaPeriodCoordinates (cubicThetaPointCoordinates q).1 := by
    funext i
    apply halfOpen_integer_unique (hp.2 i) (hq.2 i) (n:=(coordinatesEquiv.symm w) i)
    rw [hz,cubicThetaPeriodCoordinates_translate]
    rfl
  apply Subtype.ext
  apply Prod.ext
  · exact cubicThetaPeriodCoordinates_injective hc
  · have hv := congrArg (fun z : ℂ × ℝ => z.2) hw
    exact hv

instance cubicThetaPoint_polish : PolishSpace CubicThetaPoint :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ × ℝ | 0<p.2}).polishSpace

lemma cubicThetaQuotient_injective_image_measurable {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S) :
    MeasurableSet (cubicThetaQuotientMap '' S) :=
  hS.image_of_continuousOn_injOn cubicThetaQuotientMap_open.continuous.continuousOn hi

lemma cubicThetaCuspStrip_image_measurable {H : ℝ} (hH : 1≤H) :
    MeasurableSet (cubicThetaQuotientMap '' cubicThetaCuspStrip H) :=
  cubicThetaQuotient_injective_image_measurable (cubicThetaCuspStrip_measurable H)
    (cubicThetaCuspStrip_injective hH)

end CubicFirstMoment

end

end OAI
