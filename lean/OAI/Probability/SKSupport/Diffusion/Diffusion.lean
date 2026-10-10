import Mathlib
import OAI.Probability.SKSupport.Moments.StripSquareMoment

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

lemma independent_gaussian_sum_interval_pos (P : Measure Ω) [IsProbabilityMeasure P]
    {Y Z : Ω → ℝ} (hY : Measurable Y) (hZ : Measurable Z) {v : ℝ≥0} (hv : v ≠ 0)
    (hLaw : HasLaw Z (gaussianReal 0 v) P) (hi : IndepFun Y Z P)
    {a b : ℝ} (hab : a < b) : 0 < P {ξ | Y ξ+Z ξ ∈ Ioo a b} := by
  let S : Set (ℝ × ℝ) := {p | p.1+p.2 ∈ Ioo a b}
  have hS : MeasurableSet S := measurableSet_Ioo.preimage (measurable_fst.add measurable_snd)
  have he := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mp hi
  apply pos_iff_ne_zero.mpr
  intro hz
  have hp : ((P.map Y).prod (gaussianReal 0 v)) S=0 := by
    rw [← hLaw.map_eq,← he,Measure.map_apply (hY.prodMk hZ) hS]
    exact hz
  obtain ⟨y,hy⟩ := (Measure.measure_prod_null hS |>.mp hp).exists
  have hy0 := gaussianReal_absolutelyContinuous' 0 hv hy
  have hsec : Prod.mk y ⁻¹' S=Ioo (a-y) (b-y) := by
    ext z
    change (a < y+z ∧ y+z < b) ↔ (a-y < z ∧ z < b-y)
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [hsec,Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hy0
  linarith

lemma BoundedLipschitzDrift.solution_interval_pos (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)
    (t : ℝ≥0) (ht : 0 < (t:ℝ)) {a c : ℝ} (hac : a < c) :
    0 < W.law {ξ | b.solution W.driver t ξ ∈ Ioo a c} := by
  let := W.isProbability
  have hD : 0 < (b.bound:ℝ)+1 := by positivity
  have hw : 0 < (c-a)/(4*((b.bound:ℝ)+1)) := div_pos (sub_pos.mpr hac) (by positivity)
  obtain ⟨h,hh0,hh⟩ := exists_between (lt_min ht hw)
  have hht : h < (t:ℝ) := (lt_min_iff.mp hh).1
  have hhw : 4*((b.bound:ℝ)+1)*h < c-a := by
    have h1 := (lt_div_iff₀ (by positivity : (0:ℝ) < 4*((b.bound:ℝ)+1))).mp (lt_min_iff.mp hh).2
    nlinarith
  have hdh : 2*(b.bound:ℝ)*h < c-a := by nlinarith [b.bound.coe_nonneg]
  let H : ℝ≥0 := ⟨h,hh0.le⟩
  let S : ℝ≥0 := ⟨(t:ℝ)-h,sub_nonneg.mpr hht.le⟩
  have htime : S+H=t := by apply NNReal.coe_injective;change (t:ℝ)-h+h=t;ring
  have hi := adapted_indep_increment W.brownian.toIsPreBrownianReal W.measurable S H (b.solution_adapted W S)
  have hLaw := W.brownian.toIsPreBrownianReal.hasLaw_sub (S+H) S
  have hv : nndist ((S+H:ℝ≥0):ℝ) (S:ℝ)=H := by
    apply NNReal.coe_injective
    rw [coe_nndist,Real.dist_eq,NNReal.coe_add,add_sub_cancel_left,abs_of_nonneg H.coe_nonneg]
  have hLaw' : HasLaw (fun ξ => W.B (S+H) ξ-W.B S ξ) (gaussianReal 0 H) W.law := by
    convert hLaw using 1
    congr 1
    exact hv.symm
  have hp := independent_gaussian_sum_interval_pos W.law (b.solution_measurable W S)
    ((W.measurable (S+H)).sub (W.measurable S)) (show H ≠ 0 from ne_of_gt hh0) hLaw' hi
    (a := a+(b.bound:ℝ)*h) (b := c-(b.bound:ℝ)*h) (by linarith)
  apply hp.trans_le
  apply measure_mono_ae
  filter_upwards [b.solution_increment W S H] with ξ hξ hmem
  rw [htime,← NNReal.coe_add,htime] at hξ
  have hd := b.displacement_bound W S t ξ
  have he : |(t:ℝ)-(S:ℝ)|=h := by change |(t:ℝ)-((t:ℝ)-h)|=h; rw [sub_sub_cancel,abs_of_pos hh0]
  rw [he] at hd
  rcases abs_le.mp hd with ⟨hdl,hdu⟩
  change a+(b.bound:ℝ)*h < b.solution W.driver S ξ+(W.B (S+H) ξ-W.B S ξ) ∧
    b.solution W.driver S ξ+(W.B (S+H) ξ-W.B S ξ) < c-(b.bound:ℝ)*h at hmem
  rw [htime] at hmem
  change a < b.solution W.driver t ξ ∧ b.solution W.driver t ξ < c
  rw [hξ]
  constructor <;> linarith [hmem.1,hmem.2]

theorem diffusion_interval_pos (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : 0 < (t:ℝ)) {a b : ℝ} (hab : a < b) :
    0 < W.law {ξ | diffusion W γ (⟨t,t.property.1⟩:ℝ≥0) ξ ∈ Ioo a b} := by
  have he : diffusion W γ (⟨t,t.property.1⟩:ℝ≥0)=(stripDrift W γ t).solution W.driver (⟨t,t.property.1⟩:ℝ≥0) :=
    funext (diffusion_eq_strip W γ t _ le_rfl)
  rw [he]
  exact (stripDrift W γ t).solution_interval_pos W (⟨t,t.property.1⟩:ℝ≥0) ht hab

end ZeroTemperatureSK

end
end

end OAI
