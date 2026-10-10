import OAI.Analysis.Steinitz.SectionEnergy

namespace OAI

/-! Lifted fiber rearrangement and overlap estimates. -/

section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace VerticalRearrangement
section Lift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def shear (e : E) : E × ℝ ≃ₜ E × ℝ where
  toFun p := (p.1+p.2 • e,p.2)
  invFun p := (p.1-p.2 • e,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma shear_preserving (e : E) : MeasurePreserving (shear e)
    ((volume : Measure E).prod volume) (volume.prod volume) := by
  have hp : MeasurePreserving (fun p : ℝ × E => (p.1,p.2+p.1 • e))
      ((volume : Measure ℝ).prod (volume : Measure E)) (volume.prod volume) := by
    apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun s y => y+s • e) (by fun_prop)
    exact ae_of_all _ fun s => (measurePreserving_add_right volume (s • e)).map_eq
  exact (measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure E))).comp
    (hp.comp (measurePreserving_swap (μ := (volume : Measure E)) (ν := (volume : Measure ℝ))))

noncomputable def liftFunction (ell c : ℝ) (e : E) (f : E → ℝ) (p : E × ℝ) : ℝ :=
  (Ioo (-ell) ell).indicator (fun s => c*f (p.1+s • e)) p.2

lemma lift_measurable (ell c : ℝ) (e : E) {f : E → ℝ} (hf : Measurable f) :
    Measurable (liftFunction ell c e f) := by
  have he : liftFunction ell c e f =
      ((Prod.snd ⁻¹' Ioo (-ell) ell) : Set (E × ℝ)).indicator (fun p => c*f (p.1+p.2 • e)) := by
    funext p
    by_cases hp : p.2 ∈ Ioo (-ell) ell <;> simp [liftFunction,indicator,hp]
  rw [he]
  exact (measurable_const.mul (hf.comp (by fun_prop))).indicator (measurable_snd measurableSet_Ioo)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_strip (ell c : ℝ) (e : E) (f : E → ℝ) (p : E × ℝ)
    (hp : ell ≤ |p.2|) : liftFunction ell c e f p = 0 := by
  apply indicator_of_notMem
  intro hh
  exact not_lt_of_ge hp (abs_lt.mpr hh)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_nonneg (ell : ℝ) {c : ℝ} (hc : 0 ≤ c) (e : E) {f : E → ℝ}
    (hf : ∀ x,0 ≤ f x) (p : E × ℝ) : 0 ≤ liftFunction ell c e f p :=
  indicator_nonneg (fun _ _ => mul_nonneg hc (hf _)) _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_square_eq (ell c : ℝ) (e : E) (f : E → ℝ) :
    (fun p => liftFunction ell c e f p^2) =
      (fun p : E × ℝ => (f p.1)^2 * (Ioo (-ell) ell).indicator (fun _ => c^2) p.2) ∘ shear e := by
  funext p
  change liftFunction ell c e f p^2 =
    f (p.1+p.2 • e)^2 * (Ioo (-ell) ell).indicator (fun _ => c^2) p.2
  by_cases hp : p.2 ∈ Ioo (-ell) ell
  · simp only [liftFunction,indicator_of_mem hp,mul_pow]
    ring
  · simp only [liftFunction,indicator_of_notMem hp,zero_pow (by norm_num : 2 ≠ 0),mul_zero]

lemma lift_memLp (ell c : ℝ) (e : E) {f : E → ℝ} (hm : Measurable f)
    (hf : MemLp f 2 volume) : MemLp (liftFunction ell c e f) 2 (volume.prod volume) := by
  apply (memLp_two_iff_integrable_sq (lift_measurable ell c e hm).aestronglyMeasurable).mpr
  rw [lift_square_eq]
  apply (shear_preserving e).integrable_comp_of_integrable
  exact ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf).mul_prod
    ((integrableOn_const (s := Ioo (-ell) ell) (C := c^2) (hs := by simp)).integrable_indicator measurableSet_Ioo)

lemma lift_total_square {ell : ℝ} (hell : 0 ≤ ell) (c : ℝ) (e : E) (f : E → ℝ) :
    (∫ p, liftFunction ell c e f p^2 ∂(volume : Measure E).prod volume) =
      (2*ell)*c^2*(∫ x,f x^2) := by
  rw [lift_square_eq]
  change (∫ p, ((fun p : E × ℝ => (f p.1)^2 *
      (Ioo (-ell) ell).indicator (fun _ => c^2) p.2) ((shear e) p)) ∂volume.prod volume) = _
  rw [(shear_preserving e).integral_comp (shear e).measurableEmbedding
    (fun p : E × ℝ => f p.1^2 * (Ioo (-ell) ell).indicator (fun _ => c^2) p.2),
    integral_prod_mul (fun y : E => f y^2) ((Ioo (-ell) ell).indicator (fun _ => c^2)),
    integral_indicator measurableSet_Ioo,setIntegral_const,smul_eq_mul,
    Real.volume_real_Ioo_of_le (by linarith : -ell ≤ ell)]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_difference_eq (ell c : ℝ) (e a : E) (f : E → ℝ) (p : E × ℝ) :
    liftFunction ell c e f (p.1+a,p.2)-liftFunction ell c e f p =
      liftFunction ell c e (fun y => f (y+a)-f y) p := by
  by_cases hp : p.2 ∈ Ioo (-ell) ell
  · simp only [liftFunction,indicator_of_mem hp,show p.1+a+p.2 • e=p.1+p.2 • e+a by abel]
    ring
  · simp only [liftFunction,indicator_of_notMem hp,sub_self]

lemma lift_total_difference {ell : ℝ} (hell : 0 ≤ ell) (c : ℝ) (e a : E) (f : E → ℝ) :
    (∫ p, (liftFunction ell c e f (p.1+a,p.2)-liftFunction ell c e f p)^2
      ∂(volume : Measure E).prod volume) = (2*ell)*c^2*HeatL2.realDistance f a := by
  simp_rw [lift_difference_eq]
  exact lift_total_square hell c e _

end Lift
end VerticalRearrangement

end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace VerticalRearrangement
section Lifting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma fiberStar_horizontal_difference {ell c : ℝ} (hell : 0 ≤ ell) (hc : 0 ≤ c)
    (e a : E) {f : E → ℝ} (hm : Measurable f) (hf : MemLp f 2 volume)
    (hfn : ∀ x,0 ≤ f x) :
    (∫ p, ((fiberStar (liftFunction ell c e f) (p.1+a,p.2)).toReal-
      (fiberStar (liftFunction ell c e f) p).toReal)^2 ∂(volume : Measure E).prod volume) ≤
       (2*ell)*c^2*HeatL2.realDistance f a := by
  let F := liftFunction ell c e f
  let G := liftFunction ell c e (fun y => f (y+a))
  have hshift : ∀ p : E × ℝ,G p=F (p.1+a,p.2) := by
    intro p
    dsimp [G,F,liftFunction]
    congr 2
    funext s
    congr 2
    abel
  have hg : Measurable (fun y : E => f (y+a)) := hm.comp (by fun_prop)
  have hgLp : MemLp (fun y : E => f (y+a)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume a)
  have hh := fiberStar_total_difference (μ := (volume : Measure E))
    (lift_measurable ell c e hg) (lift_measurable ell c e hm)
    (lift_nonneg ell hc e (fun y => hfn (y+a))) (lift_nonneg ell hc e hfn)
    (superlevel_measure_ne_top_of_strip (lift_strip ell c e _))
    (superlevel_measure_ne_top_of_strip (lift_strip ell c e f))
    (lift_memLp ell c e hg hgLp) (lift_memLp ell c e hm hf)
  change (∫ p,((fiberStar G p).toReal-(fiberStar F p).toReal)^2 ∂volume.prod volume) ≤ (∫ p,(G p-F p)^2 ∂volume.prod volume) at hh
  have hstar : ∀ p : E × ℝ,fiberStar G p=fiberStar F (p.1+a,p.2) := by
    intro p
    unfold fiberStar
    congr 2
    funext s
    exact hshift (p.1,s)
  simp_rw [hstar,hshift] at hh
  exact hh.trans_eq (lift_total_difference hell c e a f)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lifted_star_supported {K : Set E} (hK : Convex ℝ K) {f : E → ℝ}
    (hf : ∀ y,y ∉ K → f y=0) (ell c : ℝ) (e : E)
    {p : E × ℝ} (hp : p.1 ∉ ShiftedSections.sectionDomain K e ell |p.2|) :
    fiberStar (liftFunction ell c e f) p=0 := by
  apply ShiftedSections.fiberStar_supported hK _ hp
  intro q hq
  rcases hq with hq | hq
  · by_cases hs : q.2 ∈ Ioo (-ell) ell
    · simp only [liftFunction,indicator_of_mem hs,hf _ hq,mul_zero]
    · exact indicator_of_notMem hs _
  · exact lift_strip ell c e f q hq

end Lifting
end VerticalRearrangement

end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace VerticalRearrangement
section Height
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

lemma fiberStar_total_height {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤) :
    (∫⁻ p,ENNReal.ofReal |p.2| *(fiberStar F p)^2 ∂μ.prod volume) =
      (∫⁻ r,∫⁻ t,∫⁻ x,(ENNReal.ofReal (min (F (x,r)) (F (x,t))))^2 ∂μ)/4 := by
  have hm : Measurable (fun p : X × ℝ => ENNReal.ofReal |p.2| * (fiberStar F p)^2) :=
    measurable_snd.abs.ennreal_ofReal.mul ((fiberStar_measurable hF).pow_const 2)
  rw [lintegral_prod _ hm.aemeasurable]
  have hp x := function_rearranged_height volume
    (show Measurable (fun s => F (x,s)) from hF.comp measurable_prodMk_left) (hfF x)
  change (∫⁻ x, (∫⁻ s,ENNReal.ofReal |s| * (fiberStar F (x,s))^2) ∂μ) = _
  simp_rw [show ∀ x, (∫⁻ s, ENNReal.ofReal |s| *(fiberStar F (x,s))^2) =
    (∫⁻ r,∫⁻ t, (ENNReal.ofReal (min (F (x,r)) (F (x,t))))^2)/4 from hp,
    div_eq_mul_inv]
  rw [lintegral_mul_const' (4:ℝ≥0∞)⁻¹ _ (by norm_num)]
  congr 1
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro r
    apply lintegral_lintegral_swap
    exact (((hF.comp (measurable_fst.prodMk measurable_const)).min
      (hF.comp (measurable_fst.prodMk measurable_snd))).ennreal_ofReal.pow_const 2).aemeasurable
  · apply Measurable.aemeasurable
    apply Measurable.lintegral_prod_right
    exact (((hF.comp (measurable_fst.fst.prodMk measurable_fst.snd)).min
      (hF.comp (measurable_fst.fst.prodMk measurable_snd))).ennreal_ofReal.pow_const 2)

omit [MeasurableSpace X] in
lemma fiberStar_strip {F : X × ℝ → ℝ} {ell : ℝ}
    (hstrip : ∀ p,ell ≤ |p.2| → F p=0) {p : X × ℝ} (hp : ell ≤ |p.2|) :
    fiberStar F p=0 := by
  apply fiberStar_eq_zero_of_measure_le
  intro u
  calc
    volume (superlevel (fun r => F (p.1,r)) u) ≤ volume (Ioo (-ell) ell) := by
      apply measure_mono
      intro s hs
      change 0 < u ∧ u < F (p.1,s) at hs
      apply abs_lt.mp
      by_contra hn
      rw [hstrip (p.1,s) (not_lt.mp hn)] at hs
      linarith [hs.1,hs.2]
    _ = ENNReal.ofReal (2*ell) := by rw [Real.volume_Ioo]; congr 1; ring
    _ ≤ ENNReal.ofReal (2*|p.2|) := ENNReal.ofReal_le_ofReal (by linarith)

omit [SFinite μ] in
lemma fiberStar_height_integrable {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfn : ∀ p,0 ≤ F p) (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hiF : MemLp F 2 (μ.prod volume)) {ell : ℝ}
    (hstrip : ∀ p,ell ≤ |p.2| → F p=0) :
    Integrable (fun p => |p.2| *(fiberStar F p).toReal^2) (μ.prod volume) := by
  have hh := fiberStar_memLp hF hfn hfF hiF
  have hi := ((memLp_two_iff_integrable_sq hh.aestronglyMeasurable).mp hh).const_mul ell
  apply hi.mono' ((measurable_snd.abs.mul ((fiberStar_measurable hF).ennreal_toReal.pow_const 2)).aestronglyMeasurable)
  exact ae_of_all _ fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    by_cases hp : ell ≤ |p.2|
    · have hz : fiberStar F p = 0 := fiberStar_strip hstrip hp
      simp only [Pi.mul_apply,hz,ENNReal.toReal_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,le_refl]
    · exact mul_le_mul_of_nonneg_right (not_le.mp hp).le (sq_nonneg _)

lemma fiberStar_total_height_lower {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    {ell m : ℝ} (hell : 0 ≤ ell) (hm : 0 ≤ m)
    (hbound : ∀ r ∈ Ioo (-ell) ell, ∀ t ∈ Ioo (-ell) ell,
      ENNReal.ofReal m ≤ ∫⁻ x,(ENNReal.ofReal (min (F (x,r)) (F (x,t))))^2 ∂μ) :
    ENNReal.ofReal (ell^2*m) ≤
      ∫⁻ p,ENNReal.ofReal |p.2| * (fiberStar F p)^2 ∂μ.prod volume := by
  rw [fiberStar_total_height hF hfF]
  let I := Ioo (-ell) ell
  let G := fun r t => ∫⁻ x,(ENNReal.ofReal (min (F (x,r)) (F (x,t))))^2 ∂μ
  have hinner r (hr : r ∈ I) : ENNReal.ofReal m * volume I ≤ ∫⁻ t,G r t := by
    calc
      _ = ∫⁻ t in I,ENNReal.ofReal m := by simp
      _ ≤ ∫⁻ t in I,G r t := setLIntegral_mono' measurableSet_Ioo (hbound r hr)
      _ ≤ ∫⁻ t,G r t := setLIntegral_le_lintegral _ _
  have htotal : ENNReal.ofReal m * volume I * volume I ≤ ∫⁻ r,∫⁻ t,G r t := by
    calc
      _ = ∫⁻ r in I,ENNReal.ofReal m * volume I := by simp
      _ ≤ ∫⁻ r in I,∫⁻ t,G r t := setLIntegral_mono' measurableSet_Ioo hinner
      _ ≤ ∫⁻ r,∫⁻ t,G r t := setLIntegral_le_lintegral _ _
  have hvol : volume I = ENNReal.ofReal (2*ell) := by
    dsimp [I]
    rw [Real.volume_Ioo]
    congr 1
    ring
  have he : ENNReal.ofReal (ell^2*m) =
      (ENNReal.ofReal m * volume I * volume I)/4 := by
    rw [hvol,← ENNReal.ofReal_mul hm,
      ← ENNReal.ofReal_mul (mul_nonneg hm (by positivity)),
      show (4:ℝ≥0∞)=ENNReal.ofReal (4:ℝ) by norm_num,← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
    congr 1
    ring
  rw [he]
  exact ENNReal.div_le_div_right htotal 4

omit [SFinite μ] in
lemma fiberStar_total_real_height {F : X × ℝ → ℝ} (hF : Measurable F)
    (hfn : ∀ p,0 ≤ F p) (hfF : ∀ x u,volume (superlevel (fun s => F (x,s)) u) ≠ ⊤)
    (hiF : MemLp F 2 (μ.prod volume)) {ell : ℝ}
    (hstrip : ∀ p,ell ≤ |p.2| → F p=0) :
    ENNReal.ofReal (∫ p,|p.2| * (fiberStar F p).toReal^2 ∂μ.prod volume) =
      ∫⁻ p,ENNReal.ofReal |p.2| * (fiberStar F p)^2 ∂μ.prod volume := by
  rw [ofReal_integral_eq_lintegral_ofReal (fiberStar_height_integrable hF hfn hfF hiF hstrip)
    (ae_of_all _ fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  have hi : (∫⁻ p,(fiberStar F p)^2 ∂μ.prod volume) ≠ ⊤ := by
    rw [fiberStar_total_square hF hfF]
    exact ofReal_square_integral_ne_top hiF hfn
  apply lintegral_congr_ae
  filter_upwards [ae_finite_of_square (fiberStar_measurable hF) hi] with p hp
  rw [ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hp.ne]

end Height
end VerticalRearrangement

end

section

open MeasureTheory MeasureTheory.Measure Set
namespace VerticalRearrangement
section Overlap
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma min_square_lower (u v : ℝ) :
    (9/10:ℝ)*u^2-10*(u-v)^2 ≤ (min u v)^2 := by
  rcases le_total u v with h | h
  · rw [min_eq_left h]
    nlinarith [sq_nonneg u,sq_nonneg (u-v)]
  · rw [min_eq_right h]
    nlinarith [sq_nonneg (u-10*(u-v)),sq_nonneg (u-v)]

lemma min_square_integrable {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ∀ x,0 ≤ f x) (hgn : ∀ x,0 ≤ g x) :
    Integrable (fun x => (min (f x) (g x))^2) μ := by
  apply ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf).mono'
    ((hf.aestronglyMeasurable.aemeasurable.min hg.aestronglyMeasurable.aemeasurable).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (le_min (hfn x) (hgn x)) (min_le_left _ _) _

lemma min_square_integral_lower {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ∀ x,0 ≤ f x) (hgn : ∀ x,0 ≤ g x) :
    (9/10:ℝ)*(∫ x,f x^2 ∂μ)-10*(∫ x,(f x-g x)^2 ∂μ) ≤
      ∫ x,(min (f x) (g x))^2 ∂μ := by
  have hf2 := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hd2 := (memLp_two_iff_integrable_sq (hf.sub hg).aestronglyMeasurable).mp (hf.sub hg)
  simp only [Pi.sub_apply] at hd2
  rw [← integral_const_mul,← integral_const_mul,← integral_sub (hf2.const_mul _) (hd2.const_mul _)]
  exact integral_mono (hf2.const_mul _ |>.sub (hd2.const_mul _))
    (min_square_integrable hf hg hfn hgn) (fun x => min_square_lower (f x) (g x))

end Overlap
section Translate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma translate_pair_square (f : E → ℝ) (a b : E) :
    (∫ y,(f (y+a)-f (y+b))^2) = HeatL2.realDistance f (a-b) := by
  have hh := (measurePreserving_add_right volume b).integral_comp
    (Homeomorph.addRight b).measurableEmbedding (fun y => (f (y+(a-b))-f y)^2)
  simpa only [HeatL2.realDistance,show ∀ y:E,y+b+(a-b)=y+a by intro y; abel] using hh

lemma translate_min_square_lower {f : E → ℝ} (hf : MemLp f 2 volume)
    (hfn : ∀ x,0 ≤ f x) (hn : (∫ x,f x^2)=1) (a b : E)
    (hd : HeatL2.realDistance f (a-b) ≤ 3/500) :
    (21/25:ℝ) ≤ ∫ y,(min (f (y+a)) (f (y+b)))^2 := by
  have hh := min_square_integral_lower
    (hf.comp_measurePreserving (measurePreserving_add_right volume a))
    (hf.comp_measurePreserving (measurePreserving_add_right volume b))
    (fun y => hfn (y+a)) (fun y => hfn (y+b))
  simp only [Function.comp_apply] at hh
  rw [(measurePreserving_add_right volume a).integral_comp
    (Homeomorph.addRight a).measurableEmbedding (fun y => f y^2),
    translate_pair_square,hn] at hh
  linarith

end Translate
end VerticalRearrangement

end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace VerticalRearrangement
section LiftHeight
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma lift_min_square {ell c r t : ℝ} (hc : 0 ≤ c) (e : E) (f : E → ℝ)
    (hr : r ∈ Ioo (-ell) ell) (ht : t ∈ Ioo (-ell) ell) :
    (fun y => (min (liftFunction ell c e f (y,r)) (liftFunction ell c e f (y,t)))^2) =
      fun y => c^2 * (min (f (y+r • e)) (f (y+t • e)))^2 := by
  ext y
  simp only [liftFunction,indicator_of_mem hr,indicator_of_mem ht,← mul_min_of_nonneg _ _ hc,mul_pow]

lemma lift_height_lower {f : E → ℝ} (hm : Measurable f) (hf : MemLp f 2 volume)
    (hfn : ∀ x,0 ≤ f x) (hn : (∫ x,f x^2)=1) (e : E)
    (hd : ∀ r ∈ Ioo (-(5/2:ℝ)) (5/2),∀ t ∈ Ioo (-(5/2:ℝ)) (5/2),
      HeatL2.realDistance f ((r-t) • e) ≤ 3/500) :
    (21/20:ℝ) ≤ ∫ p,|p.2| * (fiberStar (liftFunction (5/2) (Real.sqrt (1/5)) e f) p).toReal^2
      ∂(volume : Measure E).prod volume := by
  let c := Real.sqrt (1/5:ℝ)
  let F := liftFunction (5/2) c e f
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c^2=(1/5:ℝ) := Real.sq_sqrt (by norm_num)
  have hFm : Measurable F := lift_measurable _ _ _ hm
  have hFn : ∀ p,0 ≤ F p := lift_nonneg _ hc _ hfn
  have hFi : MemLp F 2 (volume.prod volume) := lift_memLp _ _ _ hm hf
  have hFs := lift_strip (5/2:ℝ) c e f
  have hFfin := superlevel_measure_ne_top_of_strip hFs
  have hbound : ∀ r ∈ Ioo (-(5/2:ℝ)) (5/2),∀ t ∈ Ioo (-(5/2:ℝ)) (5/2),
      ENNReal.ofReal (c^2*(21/25:ℝ)) ≤
        ∫⁻ y,(ENNReal.ofReal (min (F (y,r)) (F (y,t))))^2 := by
    intro r hr t ht
    have hmin := translate_min_square_lower hf hfn hn (r • e) (t • e)
      (by simpa only [← sub_smul] using hd r hr t ht)
    have hmini := min_square_integrable
      (hf.comp_measurePreserving (measurePreserving_add_right volume (r • e)))
      (hf.comp_measurePreserving (measurePreserving_add_right volume (t • e)))
      (fun y => hfn (y+r • e)) (fun y => hfn (y+t • e))
    have hei := ofReal_integral_eq_lintegral_ofReal (hmini.const_mul (c^2))
      (ae_of_all _ fun y => mul_nonneg (sq_nonneg c) (sq_nonneg _))
    have he : (fun y => (min (F (y,r)) (F (y,t)))^2) =
        fun y => c^2*(min (f (y+r • e)) (f (y+t • e)))^2 := lift_min_square hc e f hr ht
    calc
      ENNReal.ofReal (c^2*(21/25:ℝ)) ≤ ENNReal.ofReal (c^2*(∫ y,(min (f (y+r • e)) (f (y+t • e)))^2)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmin (sq_nonneg c))
      _ = ∫⁻ y,ENNReal.ofReal (c^2*(min (f (y+r • e)) (f (y+t • e)))^2) := by
        rw [← integral_const_mul]
        exact hei
      _ = ∫⁻ y,(ENNReal.ofReal (min (F (y,r)) (F (y,t))))^2 := by
        apply lintegral_congr
        intro y
        rw [← congrFun he y]
        exact ENNReal.ofReal_pow (le_min (hFn _) (hFn _)) _
  have hH := fiberStar_total_height_lower hFm hFfin (by norm_num : (0:ℝ)≤5/2)
    (by positivity : 0 ≤ c^2*(21/25:ℝ)) hbound
  rw [hc2] at hH
  norm_num at hH
  rw [← fiberStar_total_real_height hFm hFn hFfin hFi hFs] at hH
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _)))).mp hH

end LiftHeight
end VerticalRearrangement

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
open VerticalRearrangement HeatL2 HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma lifted_test {K : Set (EuclideanSpace ℝ ι)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hB : Bound K hKm (1/10000)) (j : ι) {η ε : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1/4) (hε : 0 < ε) (hε1 : ε ≤ 1/10000) :
    ∃ f : EuclideanSpace ℝ ι → ℝ, ∃ hf : MemLp f 2 volume,
      (∀ i,energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf) < η*((1/10000)+ε)) ∧
      ∃ G : EuclideanSpace ℝ ι × ℝ → ℝ,
      Measurable G ∧ MemLp G 2 (volume.prod volume) ∧
      (∀ p,p.1 ∉ sectionDomain K (EuclideanSpace.single j 1) (5/2) |p.2| → G p=0) ∧
      (∫ p,G p^2 ∂volume.prod volume)=1 ∧
      Integrable (fun p => |p.2| *G p^2) (volume.prod volume) ∧
      (21/20:ℝ) ≤ ∫ p,|p.2| *G p^2 ∂volume.prod volume ∧
      ∀ a,(∫ p,(G (p.1+a,p.2)-G p)^2 ∂volume.prod volume) ≤ realDistance f a := by
  obtain ⟨f,hm,hfn,hfs,hf,hn,hE⟩ := simultaneous_real_density hB hη hε
  let e := EuclideanSpace.single j (1:ℝ)
  let c := Real.sqrt (1/5:ℝ)
  let F := liftFunction (5/2) c e f
  let G := fun p => (fiberStar F p).toReal
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c^2=(1/5:ℝ) := Real.sq_sqrt (by norm_num)
  have hFm : Measurable F := lift_measurable _ _ _ hm
  have hFn : ∀ p,0 ≤ F p := lift_nonneg _ hc _ hfn
  have hFi : MemLp F 2 (volume.prod volume) := lift_memLp _ _ _ hm hf
  have hFs := lift_strip (5/2:ℝ) c e f
  have hFfin := superlevel_measure_ne_top_of_strip hFs
  have hGn : (∫ p,G p^2 ∂volume.prod volume)=1 := by
    rw [fiberStar_total_real_square hFm hFn hFfin (ofReal_square_integral_ne_top hFi hFn),
      lift_total_square (by norm_num : (0:ℝ)≤5/2) c e f,hc2,hn]
    norm_num
  refine ⟨f,hf,hE,G,(fiberStar_measurable hFm).ennreal_toReal,
    fiberStar_memLp hFm hFn hFfin hFi,?_,hGn,?_,?_,?_⟩
  · intro p hp
    rw [show G p = (fiberStar (liftFunction (5/2) c e f) p).toReal from rfl,
      lifted_star_supported hKc hfs (5/2) c e hp,ENNReal.toReal_zero]
  · exact fiberStar_height_integrable hFm hFn hFfin hFi hFs
  · exact lift_height_lower hm hf hfn hn e (fun r hr t ht =>
      real_coordinate_distance hf hη hη1 hε1 (fun i => (hE i).le) j hr ht)
  · intro a
    have hh := fiberStar_horizontal_difference (by norm_num : (0:ℝ)≤5/2) hc e a hm hf hfn
    rw [hc2] at hh
    norm_num at hh
    exact hh

end ShiftedSections

end

end OAI
