import Mathlib
import OAI.Geometry.CubicTorus.Profiles.SmoothSeamProbability

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_ae_of_upper_half {P : AxisCircle → Prop}
    (hm : MeasurableSet {t | P t})
    (hs : ∀ t,P (-t) ↔ P t)
    (hP : ∀ᵐ t : ℝ ∂volume.restrict (Icc (1/2 : ℝ) 1),P (t : AxisCircle)) :
    ∀ᵐ t : AxisCircle,P t := by
  have hneg := ((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Icc).mp hP)
  have hlo : ∀ᵐ t : ℝ,t∈Icc 0 (1/2 : ℝ) → P (t : AxisCircle) := by
    filter_upwards [hneg] with t ht hmem
    have hh := ht ⟨by linarith [hmem.2],by linarith [hmem.1]⟩
    have he : ((1-t : ℝ) : AxisCircle)=-(t : AxisCircle) := by
      rw [AddCircle.coe_sub]
      simp
    rw [he] at hh
    exact (hs _).mp hh
  have hall : ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0 : ℝ) 1),P (t : AxisCircle) := by
    filter_upwards [ae_restrict_of_ae hlo,ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Icc).mp hP),
      ae_restrict_mem measurableSet_Ioc] with t hl hu ht
    by_cases h : t≤1/2
    · exact hl ⟨le_of_lt ht.1,h⟩
    · exact hu ⟨le_of_lt (lt_of_not_ge h),ht.2⟩
  have hp : MeasurePreserving (fun t : ℝ ↦ (t : AxisCircle)) (volume.restrict (Ioc (0 : ℝ) 1)) volume := by
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [←hp.map_eq]
  exact ae_map_iff hp.measurable.aemeasurable hm |>.mpr hall

theorem isMinimizerAt_planar_profile_circle {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) :
    ∀ᵐ t : AxisCircle,
      ENNReal.ofReal (unitPlanarProfile (volume.real (axialSlice (openRepresentative E) i t)))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i t) := by
  apply circle_ae_of_upper_half
  · apply measurableSet_le
    · apply Measurable.ennreal_ofReal
      have hc : Continuous unitPlanarProfile := by unfold unitPlanarProfile; fun_prop
      exact hc.measurable.comp (axialSliceVolume_measurable (isOpen_openRepresentative E).measurableSet i).ennreal_toReal
    · exact planarTorusPerimeter_slice_measurable (isOpen_openRepresentative E).measurableSet i
  · intro t
    rw [axialSlice_neg_of_reflection (reflection_invariant_openRepresentative hmin.1.1 hR)]
  · exact isMinimizerAt_planar_profile_ae hV hE hmin hR hd i

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nesting_improved_profile_circle {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E)
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    let δ := nestingDelta (H/2) s
    0<δ →∀ᵐ t : AxisCircle,
      let v := volume.real (axialSlice (openRepresentative E) i t)
      v∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2)) →
      ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v-Shape.u (H/2)+δ)/δ)))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i t) := by
  intro s δ hδpos
  apply circle_ae_of_upper_half
  · let v : AxisCircle →ℝ := fun t ↦ volume.real (axialSlice (openRepresentative E) i t)
    have hm : Measurable v := (axialSliceVolume_measurable (isOpen_openRepresentative E).measurableSet i).ennreal_toReal
    have hf : Measurable (fun t : AxisCircle ↦ ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v t-Shape.u (H/2)+δ)/δ)))) := by
      apply Measurable.ennreal_ofReal
      apply measurable_const.mul
      apply Real.continuous_sqrt.measurable.comp
      exact measurable_const.add (measurable_const.mul (Shape.continuous_shape.measurable.comp ((hm.sub_const _).add_const _ |>.div_const _)))
    have hi := measurableSet_le hf (planarTorusPerimeter_slice_measurable (isOpen_openRepresentative E).measurableSet i)
    have hr : MeasurableSet {t : AxisCircle | v t∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2))} := hm measurableSet_Icc
    convert hr.compl.union hi using 1
    ext t
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff]
    tauto
  · intro t
    rw [axialSlice_neg_of_reflection (reflection_invariant_openRepresentative hmin.1.1 hR)]
  · exact isMinimizerAt_nesting_improved_profile_ae hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1 hH hδpos

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sharpSectionWeight (H s : ℝ) : ℝ :=
  if s∈Ico 0 1 then Nesting.weight (H*s/unitPlanarProfile s) else Nesting.ell

lemma unitPlanarProfile_pos {s : ℝ} (hs : s∈Ioo 0 1) : 0<unitPlanarProfile s := by
  have hs0 : 0<s := hs.1
  unfold unitPlanarProfile
  apply lt_min
  · positivity
  · apply lt_min (by norm_num)
    have : 0<1-s := sub_pos.mpr hs.2
    positivity

lemma sharpSectionWeight_measurable (H : ℝ) : Measurable (sharpSectionWeight H) := by
  unfold sharpSectionWeight
  apply Measurable.ite (measurableSet_Ico) _ measurable_const
  unfold Nesting.weight Nesting.rawWeight unitPlanarProfile
  fun_prop

lemma sharpSectionWeight_nonneg {H : ℝ} (hH : 0≤H) (s : ℝ) : 0 ≤ sharpSectionWeight H s := by
  unfold sharpSectionWeight
  split_ifs with hs
  · exact (by norm_num [Nesting.ell] : (0 : ℝ)≤Nesting.ell).trans
      (Nesting.weight_mem (div_nonneg (mul_nonneg hH hs.1) (unitPlanarProfile_nonneg s))).1
  · norm_num [Nesting.ell]

lemma sharpSectionWeight_zero (H : ℝ) : sharpSectionWeight H 0=1 := by
  simp [sharpSectionWeight,Nesting.weight,Nesting.rawWeight,Nesting.cutoff_pos.le]

lemma sharpSectionWeight_one (H : ℝ) : sharpSectionWeight H 1=Nesting.ell := by
  simp [sharpSectionWeight]

lemma sharpSectionWeight_le {H s d : ℝ} (hH : 0≤H) (hs : s∈Icc 0 1)
    (hd : 0≤d) (hp : unitPlanarProfile s≤d) :
    sharpSectionWeight H s≤Nesting.weight (H*s/d) := by
  by_cases hz : s=0
  · subst s
    rw [sharpSectionWeight_zero]
    simp [Nesting.weight,Nesting.rawWeight,Nesting.cutoff_pos.le]
  by_cases ho : s=1
  · subst s
    rw [sharpSectionWeight_one]
    exact (Nesting.weight_mem (div_nonneg (mul_nonneg hH (by norm_num)) hd)).1
  have hs' : s∈Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 (Ne.symm hz),lt_of_le_of_ne hs.2 ho⟩
  have hpp := unitPlanarProfile_pos hs'
  rw [sharpSectionWeight,ite_eq_left ⟨hs.1,hs'.2⟩]
  apply Nesting.antitoneOn_weight
  · exact div_nonneg (mul_nonneg hH hs.1) hd
  · exact div_nonneg (mul_nonneg hH hs.1) hpp.le
  · exact div_le_div_of_nonneg_left (mul_nonneg hH hs.1) hpp hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def improvedSectionWeight (H δ v : ℝ) : ℝ :=
  if 0<δ ∧ v∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2)) then
    Nesting.weight ((H/2)*v/Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v-Shape.u (H/2)+δ)/δ)))
  else sharpSectionWeight H v

lemma improvedSectionWeight_measurable (H δ : ℝ) : Measurable (improvedSectionWeight H δ) := by
  unfold improvedSectionWeight
  apply Measurable.ite ((MeasurableSet.const _).inter measurableSet_Icc) _ (sharpSectionWeight_measurable _)
  unfold Nesting.weight Nesting.rawWeight Shape.shape
  fun_prop

lemma improvedSectionWeight_mem {H δ : ℝ} (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ))
    (hδ : δ∈Icc 0 Shape.dm) (v : ℝ) : improvedSectionWeight H δ v∈Icc 0 1 := by
  have hH0 : 0≤H := by linarith [hH.1]
  have hh0 : 0≤H/2 := by linarith [hH.1]
  have hplace := Shape.interval_placement hH
  unfold improvedSectionWeight
  split_ifs with hm
  · have hv : 0≤v := by linarith [hm.2.1,hδ.2,hplace.2.1]
    have hx : 0≤(H/2)*v/Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v-Shape.u (H/2)+δ)/δ)) :=
      div_nonneg (mul_nonneg hh0 hv) (Real.sqrt_nonneg _)
    exact ⟨(by norm_num [Nesting.ell] : (0 : ℝ)≤Nesting.ell).trans (Nesting.weight_mem hx).1,
      (Nesting.weight_mem hx).2⟩
  · refine ⟨sharpSectionWeight_nonneg hH0 v,?_⟩
    unfold sharpSectionWeight
    split_ifs with hs
    · exact (Nesting.weight_mem (div_nonneg (mul_nonneg hH0 hs.1) (unitPlanarProfile_nonneg _))).2
    · norm_num [Nesting.ell]

lemma improvedSectionWeight_le_density {H δ v d : ℝ}
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) (_hδ : δ∈Icc 0 Shape.dm)
    (hv : v∈Icc (0 : ℝ) 1) (hd : 0≤d) (hbase : unitPlanarProfile v≤d)
    (himp : 0<δ →v∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2)) →
      2*Real.sqrt (1+Shape.c*δ^2*Shape.shape ((v-Shape.u (H/2)+δ)/δ))≤d) :
    improvedSectionWeight H δ v≤Nesting.weight (H*v/d) := by
  have hH0 : 0≤H := by linarith [hH.1]
  unfold improvedSectionWeight
  split_ifs with hm
  · let q := (v-Shape.u (H/2)+δ)/δ
    have hq : q∈Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hm.2.1]) hm.1.le,
      (div_le_one hm.1).mpr (by linarith [hm.2.2])⟩
    have hK : 0≤Shape.c*δ^2*Shape.shape q := mul_nonneg (by norm_num [Shape.c]; positivity) (Shape.shape_nonneg hq)
    have hp : 0<2*Real.sqrt (1+Shape.c*δ^2*Shape.shape q) := by positivity
    have hw := Nesting.antitoneOn_weight (show H*v/d∈Ici 0 from div_nonneg (mul_nonneg hH0 hv.1) hd)
      (show H*v/(2*Real.sqrt (1+Shape.c*δ^2*Shape.shape q))∈Ici 0 from div_nonneg (mul_nonneg hH0 hv.1) hp.le)
      (div_le_div_of_nonneg_left (mul_nonneg hH0 hv.1) hp (himp hm.1 hm.2))
    convert hw using 1
    congr 1
    dsimp only [q]
    ring
  · exact sharpSectionWeight_le hH0 hv hd hbase

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma rational_quadratic_discriminant {a b c : ℝ}
    (h : ∀ q : ℚ,0≤a*(q : ℝ)^2-2*b*(q : ℝ)+c) : b^2≤a*c := by
  have hr (r : ℝ) : 0≤a*r^2-2*b*r+c := by
    exact Rat.denseRange_cast.induction_on r (isClosed_le continuous_const (by fun_prop)) h
  have hh := discrim_le_zero (a := a) (b := -2*b) (c := c) (fun r ↦ by
    have ht := hr r
    nlinarith only [ht])
  dsimp [discrim] at hh
  nlinarith only [hh]

theorem axial_moment_bounds {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t,axialSecondDensity μ i t≤axialAreaDensity μ i t ∧
      axialSecondDensity μ i t≤axialPerimeterDensity μ i t ∧
      (axialPerimeterDensity μ i t)^2≤axialAreaDensity μ i t*axialSecondDensity μ i t ∧
      (axialNormalDensity μ i t)^2≤axialAreaDensity μ i t*
        (axialAreaDensity μ i t-axialSecondDensity μ i t) := by
  have hta := axial_moment_nonneg_ae i ha 1 0 (-1) 0 (fun z ↦ by
    have hh := normalTransverseLength_sq i z
    nlinarith [sq_nonneg ((z.2 : Cover) i)])
  have htp := axial_moment_nonneg_ae i ha 0 1 (-1) 0 (fun z ↦ by
    have h0 := normalTransverseLength_nonneg i z
    have h1 := normalTransverseLength_le_one i z
    nlinarith)
  have hp : ∀ᵐ t,∀ q : ℚ,0≤axialAreaDensity μ i t*(q : ℝ)^2-
      2*axialPerimeterDensity μ i t*(q : ℝ)+axialSecondDensity μ i t := by
    apply ae_all_iff.mpr
    intro q
    have hh := axial_moment_nonneg_ae i ha ((q : ℝ)^2) (-2*q) 1 0 (fun z ↦ by
      nlinarith [sq_nonneg (normalTransverseLength i z-(q : ℝ))])
    filter_upwards [hh] with t ht
    nlinarith only [ht]
  have hd : ∀ᵐ t,∀ q : ℚ,0≤axialAreaDensity μ i t*(q : ℝ)^2-
      2*axialNormalDensity μ i t*(q : ℝ)+(axialAreaDensity μ i t-axialSecondDensity μ i t) := by
    apply ae_all_iff.mpr
    intro q
    have hh := axial_moment_nonneg_ae i ha ((q : ℝ)^2+1) 0 (-1) (-2*q) (fun z ↦ by
      have hh := normalTransverseLength_sq i z
      nlinarith [sq_nonneg (((z.2 : Cover) i)-(q : ℝ))])
    filter_upwards [hh] with t ht
    nlinarith only [ht]
  filter_upwards [hta,htp,hp,hd] with t hta htp hp hd
  exact ⟨by linarith,by linarith,rational_quadratic_discriminant hp,rational_quadratic_discriminant hd⟩

end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus.Nesting

lemma moment_weight_bound_pos {a p t d : ℝ} (ha : 0<a) (hp : 0<p)
    (ht : 0≤t) (hta : t≤a) (hp2 : p^2≤a*t) (hd2 : d^2≤a*(a-t)) :
    weight (t/p)*|d|≤a-lambda*t := by
  have hw := weight_mem (div_nonneg ht hp.le)
  have hw0 : 0≤weight (t/p) := (by norm_num [ell] : (0 : ℝ)≤ell).trans hw.1
  rcases lt_or_eq_of_le hta with hta|rfl
  · let q := Real.sqrt (t/a)
    have hq0 : 0≤q := Real.sqrt_nonneg _
    have hq2 : q^2=t/a := Real.sq_sqrt (div_nonneg ht ha.le)
    have haq : a*q^2=t := by rw [hq2]; field_simp
    have hq1 : q<1 := by
      have hh : t/a<1 := (div_lt_one ha).mpr hta
      nlinarith
    have hqp : q*p≤t := by
      have hb := mul_le_mul_of_nonneg_right hp2 (sq_nonneg q)
      have he : a*t*q^2=t^2 := by rw [show a*t*q^2=(a*q^2)*t by ring,haq]; ring
      rw [he] at hb
      nlinarith [mul_nonneg hq0 hp.le]
    have hqm : q≤t/p := (le_div_iff₀ hp).mpr hqp
    have hW := (antitoneOn_weight hq0 (div_nonneg ht hp.le) hqm).trans
      (weight_le_rawWeight ⟨hq0,hq1⟩)
    let s := Real.sqrt (1-q^2)
    have hs : 0<s := Real.sqrt_pos.mpr (by nlinarith)
    have hs2 : s^2=1-q^2 := Real.sq_sqrt (by nlinarith)
    have has : (a*s)^2=a*(a-t) := by
      linear_combination a^2*hs2-a*haq
    have hd : |d|≤a*s := by nlinarith [sq_abs d,abs_nonneg d,mul_pos ha hs]
    calc
      weight (t/p)*|d|≤weight (t/p)*(a*s) := mul_le_mul_of_nonneg_left hd hw0
      _≤rawWeight q*(a*s) := mul_le_mul_of_nonneg_right hW (mul_nonneg ha.le hs.le)
      _=a-lambda*t := by
        rw [show rawWeight q*(a*s)=a*(rawWeight q*s) by ring]
        have he : rawWeight q*s=1-lambda*q^2 := by
          exact div_mul_cancel₀ _ hs.ne'
        rw [he]
        rw [show a*(1-lambda*q^2)=a-lambda*(a*q^2) by ring,haq]
  · have hd : d=0 := by nlinarith [sq_nonneg d]
    rw [hd,abs_zero,mul_zero]
    norm_num [lambda]
    linarith

lemma moment_weight_bound {a p t d : ℝ} (ha : 0≤a) (hp : 0≤p)
    (ht : 0≤t) (hta : t≤a) (htp : t≤p) (hp2 : p^2≤a*t) (hd2 : d^2≤a*(a-t)) :
    weight (t/p)*|d|≤a-lambda*t := by
  rcases eq_or_lt_of_le ha with ha|ha
  · subst a
    have ht0 : t=0 := le_antisymm hta ht
    have hp0 : p=0 := by nlinarith [sq_nonneg p]
    have hd0 : d=0 := by nlinarith [sq_nonneg d]
    simp [ht0,hp0,hd0]
  rcases eq_or_lt_of_le hp with hp|hp
  · subst p
    have ht0 : t=0 := le_antisymm htp ht
    have hd : |d|≤a := by rw [ht0] at hd2; nlinarith [sq_abs d,abs_nonneg d]
    have hw : weight 0=1 := by simp [weight,min_eq_left cutoff_pos.le,rawWeight]
    simpa [ht0,hw] using hd
  · exact moment_weight_bound_pos ha hp ht hta hp2 hd2

lemma continuousOn_weight : ContinuousOn weight (Ici 0) := by
  apply continuousOn_rawWeight.comp (continuous_id.min continuous_const).continuousOn
  intro x hx
  exact ⟨le_min hx cutoff_pos.le,min_le_right _ _⟩

end CubicTorus.Nesting

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalized_real_pair (x y : ℝ) :
    let s := Real.sqrt (x^2+y^2)
    |x/s|≤1 ∧ |y/s|≤1 ∧ (x/s)^2+(y/s)^2≤1 ∧ x*(x/s)+y*(y/s)=s := by
  dsimp only
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hnon := Real.sqrt_nonneg (x^2+y^2)
  by_cases hz : Real.sqrt (x^2+y^2)=0
  · simp [hz]
  · have hp := lt_of_le_of_ne hnon (Ne.symm hz)
    have hx : |x|≤Real.sqrt (x^2+y^2) := by nlinarith [sq_abs x,sq_nonneg y,abs_nonneg x]
    have hy : |y|≤Real.sqrt (x^2+y^2) := by nlinarith [sq_abs y,sq_nonneg x,abs_nonneg y]
    refine ⟨?_,?_,?_,?_⟩
    · rw [abs_div,abs_of_nonneg hnon]
      exact (div_le_one hp).mpr hx
    · rw [abs_div,abs_of_nonneg hnon]
      exact (div_le_one hp).mpr hy
    · have he : (x / Real.sqrt (x^2+y^2))^2+(y / Real.sqrt (x^2+y^2))^2=1 := by
        field_simp
        nlinarith
      exact he.le
    · field_simp
      nlinarith

lemma real_pair_dot_le_one {a b f g : ℝ} (hab : a^2+b^2=1) (hfg : f^2+g^2≤1) :
    a*f+b*g≤1 := by
  have hh : (a*f+b*g)^2≤(a^2+b^2)*(f^2+g^2) := by
    nlinarith [sq_nonneg (a*g-b*f)]
  rw [hab,one_mul] at hh
  nlinarith

lemma integrable_mul_unit {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f g : α → ℝ} (hf : Integrable f ν) (hg : Measurable g) (hb : ∀ x,|g x|≤1) :
    Integrable (fun x ↦ f x*g x) ν := by
  apply Integrable.mono' hf.abs (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul]
  simpa using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x))

theorem axial_density_coarea_bound {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (∫ t,Real.sqrt ((axialPerimeterDensity μ i t)^2+(axialNormalDensity μ i t)^2))≤
      (μ.mass : ℝ) := by
  let p := axialPerimeterDensity μ i
  let d := axialNormalDensity μ i
  let s : AxisCircle → ℝ := fun t ↦ Real.sqrt ((p t)^2+(d t)^2)
  let f : AxisCircle → ℝ := fun t ↦ p t/s t
  let g : AxisCircle → ℝ := fun t ↦ d t/s t
  have hp : Measurable p := axialPerimeterDensity_measurable μ i
  have hd : Measurable d := axialNormalDensity_measurable μ i
  have hs : Measurable s := ((hp.pow_const 2).add (hd.pow_const 2)).sqrt
  have hf : Measurable f := hp.div hs
  have hg : Measurable g := hd.div hs
  have hfb (t : AxisCircle) : |f t|≤1 := (normalized_real_pair (p t) (d t)).1
  have hgb (t : AxisCircle) : |g t|≤1 := (normalized_real_pair (p t) (d t)).2.1
  have hfg (t : AxisCircle) : (f t)^2+(g t)^2≤1 := (normalized_real_pair (p t) (d t)).2.2.1
  have he (t : AxisCircle) : p t*f t+d t*g t=s t := (normalized_real_pair (p t) (d t)).2.2.2
  have hpi : Integrable p := axialPerimeterDensity_integrable μ i
  have hdi : Integrable d := axialNormalDensity_integrable μ i
  have hfi := integrable_mul_unit hpi hf hfb
  have hgi := integrable_mul_unit hdi hg hgb
  have hi (k : AxisCircle → ℝ) (hk : Measurable k) (hb : ∀ t,|k t|≤1) :
      Integrable (fun z : NormalBundle ↦ k (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
    Integrable.mono' (integrable_const (1 : ℝ))
      (hk.comp (normal_axisCircle_continuous i).measurable).aestronglyMeasurable (ae_of_all _ fun z ↦ hb _)
  have hαi : Integrable (fun z : NormalBundle ↦ normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle))
      (μ : Measure NormalBundle) :=
    integrable_mul_unit ((normalTransverseLength_continuous i).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (hf.comp (normal_axisCircle_continuous i).measurable) (fun z ↦ hfb _)
  have hni : Integrable (fun z : NormalBundle ↦ ((z.2 : Cover) i)*g (((z.1 : Cover) i) : AxisCircle))
      (μ : Measure NormalBundle) :=
    integrable_mul_unit ((normal_component_continuous i).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (hg.comp (normal_axisCircle_continuous i).measurable) (fun z ↦ hgb _)
  calc
    _ = ∫ t,s t := rfl
    _ = ∫ t,p t*f t+d t*g t := integral_congr_ae (ae_of_all _ fun t ↦ (he t).symm)
    _ = (∫ t,p t*f t)+(∫ t,d t*g t) := integral_add hfi hgi
    _ = (∫ z,normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle))+
        (∫ z,((z.2 : Cover) i)*g (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle)) := by
      rw [axialPerimeterDensity_pairing_bounded i ha hf hfb,axialNormalDensity_pairing_bounded i ha hg hgb]
    _ = ∫ z,normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle)+
        ((z.2 : Cover) i)*g (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) :=
      (integral_add hαi hni).symm
    _ ≤ ∫ _ : NormalBundle,(1 : ℝ) ∂(μ : Measure NormalBundle) :=
      integral_mono (hαi.add hni) (integrable_const _) (fun z ↦
        real_pair_dot_le_one (normalTransverseLength_sq i z) (hfg _))
    _ = _ := normalMeasure_integral_one μ

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_nesting_weight_comp {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (hf : Measurable f) (hn : ∀ x,0≤f x) : Measurable (fun x ↦ Nesting.weight (f x)) := by
  have hc : Continuous (fun t : ℝ ↦ Nesting.weight (max t 0)) :=
    Nesting.continuousOn_weight.comp_continuous (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)
  have hh := hc.measurable.comp hf
  convert hh using 1
  ext x
  exact congrArg Nesting.weight (max_eq_left (hn x)).symm

lemma axialAreaDensity_integral {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (∫ t,axialAreaDensity μ i t)=(μ.mass : ℝ) := by
  have hh := axialAreaDensity_pairing i ha (f := fun _ ↦ 1) continuous_const
  simpa only [mul_one,integral_const,smul_eq_mul,mul_one,Measure.real_def,
    ←FiniteMeasure.ennreal_mass,ENNReal.coe_toReal] using hh

lemma axialSecondDensity_integral {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (∫ t,axialSecondDensity μ i t)=axialTransverseMass μ i := by
  have hh := axialSecondDensity_pairing i ha (f := fun _ ↦ 1) continuous_const
  simp only [mul_one] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with z
  have he := normalTransverseLength_sq i z
  linarith

lemma axial_weighted_normal_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (fun t ↦ Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
      |axialNormalDensity μ i t|) := by
  have hf := measurable_nesting_weight_comp
    ((axialSecondDensity_measurable μ i).div (axialPerimeterDensity_measurable μ i))
    (fun t ↦ div_nonneg ENNReal.toReal_nonneg (axialPerimeterDensity_nonneg μ i t))
  apply Integrable.mono' (axialNormalDensity_integrable μ i).abs
    (hf.mul (axialNormalDensity_measurable μ i).abs).aestronglyMeasurable
  filter_upwards [] with t
  have hm := Nesting.weight_mem (div_nonneg (show 0≤axialSecondDensity μ i t from ENNReal.toReal_nonneg)
    (axialPerimeterDensity_nonneg μ i t))
  have hn : 0≤Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t) :=
    (by norm_num [Nesting.ell] : (0 : ℝ)≤Nesting.ell).trans hm.1
  change ‖Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
    |axialNormalDensity μ i t|‖≤|axialNormalDensity μ i t|
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hn,abs_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) hm.2

theorem axial_integrated_flux {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    Nesting.lambda*axialTransverseMass μ i+
      (∫ t,Nesting.weight (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*
        |axialNormalDensity μ i t|)≤(μ.mass : ℝ) := by
  have hh := integral_mono_ae (axial_weighted_normal_integrable μ i)
    ((axialAreaDensity_integrable μ i).sub ((axialSecondDensity_integrable μ i).const_mul Nesting.lambda)) ?_
  · simp only [Pi.sub_apply] at hh
    rw [integral_sub (axialAreaDensity_integrable μ i)
      ((axialSecondDensity_integrable μ i).const_mul Nesting.lambda),integral_const_mul,
      axialAreaDensity_integral i ha,axialSecondDensity_integral i ha] at hh
    linarith
  filter_upwards [axial_moment_bounds i ha] with t ht
  exact Nesting.moment_weight_bound ENNReal.toReal_nonneg (axialPerimeterDensity_nonneg μ i t)
    ENNReal.toReal_nonneg ht.1 ht.2.1 ht.2.2.1 ht.2.2.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma one_lipschitz_comp_ac {P f : ℝ → ℝ} (hP : LipschitzWith 1 P)
    {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ P (f t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hh⟩ := hf ε hε
  refine ⟨δ,hδ,fun E hE hsum ↦ lt_of_le_of_lt ?_ (hh E hE hsum)⟩
  apply Finset.sum_le_sum
  intro i hi
  simpa using hP.dist_le_mul (f (E.2 i).1) (f (E.2 i).2)

lemma bounded_primitive_lipschitz {γ : ℝ → ℝ} (hc : Continuous γ)
    (hb : ∀ x,|γ x|≤1) : LipschitzWith 1 (fun r ↦ ∫ s in (0 : ℝ)..r,γ s) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hh := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (a := 0) (b := y)) (hc.intervalIntegrable (μ := volume) (a := y) (b := x))
  have hbb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := y) (b := x) (f := γ) (fun z hz ↦ by simpa only [Real.norm_eq_abs] using hb z)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,Real.norm_eq_abs] at hbb ⊢
  rw [show (∫ s in (0 : ℝ)..x,γ s)-(∫ s in (0 : ℝ)..y,γ s)=∫ s in y..x,γ s by linarith only [hh] ]
  exact hbb

theorem circle_ac_weighted_oscillation {f : ℝ → ℝ} {g : AxisCircle → ℝ}
    (hp : Function.Periodic f 1) (hc : Continuous f)
    (hf : ∀ a b,AbsolutelyContinuousOnInterval f a b) (hgi : Integrable g)
    (hd : ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt f (g (t : AxisCircle)) t)
    {γ : ℝ → ℝ} (hγ : Continuous γ) (hγb : ∀ x,γ x∈Icc 0 1)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    2*|∫ y in f 0..f t,γ y|≤∫ s,γ (hp.lift s)*|g s| := by
  let P : ℝ → ℝ := fun r ↦ ∫ s in (0 : ℝ)..r,γ s
  have hPb (x : ℝ) : |γ x|≤1 := by rw [abs_of_nonneg (hγb x).1]; exact (hγb x).2
  have hP : LipschitzWith 1 P := bounded_primitive_lipschitz hγ hPb
  have hPd (x : ℝ) : HasDerivAt P (γ x) x :=
    intervalIntegral.integral_hasDerivAt_right (hγ.intervalIntegrable (μ := volume) 0 x)
      hγ.stronglyMeasurable.stronglyMeasurableAtFilter hγ.continuousAt
  have hFp : Function.Periodic (fun t ↦ P (f t)) 1 := fun t ↦ congrArg P (hp t)
  have hFi (a b : ℝ) := one_lipschitz_comp_ac hP (hf a b)
  have hgm : Measurable (fun s : AxisCircle ↦ γ (hp.lift s)) :=
    hγ.measurable.comp (continuous_periodic_lift hp hc).measurable
  have hwi : Integrable (fun s : AxisCircle ↦ γ (hp.lift s)*g s) := by
    simpa only [mul_comm] using integrable_mul_unit hgi hgm (fun s ↦ hPb _)
  have hwd : ∀ᵐ r : ℝ,r∈Icc (0 : ℝ) 1 → HasDerivAt (fun t ↦ P (f t))
      (γ (hp.lift (r : AxisCircle))*g (r : AxisCircle)) r := by
    filter_upwards [hd] with r hr hri
    exact (hPd (f r)).comp r (hr hri)
  have hh := circle_ac_oscillation_bound hFp hFi hwi hwd ht
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hγ.intervalIntegrable (μ := volume) (a := 0) (b := f 0)) (hγ.intervalIntegrable (μ := volume) (a := f 0) (b := f t))
  have hPe : P (f t)-P (f 0)=∫ y in f 0..f t,γ y := by
    dsimp only [P]
    linarith only [he]
  rw [hPe] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with s
  rw [abs_mul,abs_of_nonneg (hγb _).1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axial_integrated_flux_actual {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    Nesting.lambda*axialTransverseMass μ i+
      (∫ t,Nesting.weight (actualAxialFlux E μ H i t/axialPerimeterDensity μ i t)*
        |axialNormalDensity μ i t|)≤(perimeter E).toReal := by
  have hh := axial_integrated_flux i ha
  rw [hμ.1] at hh
  convert hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [axialSurface_density_eq_flux hE hH i] with t ht
  rw [←ht]
  rfl

theorem isMinimizerAt_weighted_area_bound {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {γ : ℝ → ℝ} (hγ : Continuous γ) (hγb : ∀ x,γ x∈Icc 0 1)
    (hγw : ∀ᵐ t,γ ((axialSliceVolume (openRepresentative E) i t).toReal)≤
      Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/axialPerimeterDensity μ i t))
    {τ : ℝ} (hτ : τ∈Icc (0 : ℝ) 1) :
    Nesting.lambda*axialTransverseMass μ i+
      2*|∫ y in (axialSliceVolume (openRepresentative E) i 0).toReal..
        (axialSliceVolume (openRepresentative E) i (τ : AxisCircle)).toReal,γ y|≤
      (perimeter E).toReal := by
  let O := openRepresentative E
  have hO : MeasurableSet O := (isOpen_openRepresentative E).measurableSet
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμO := hμ.congr_ae hOE.symm
  have hHO (D : Periodic.Variation) : Periodic.normalFirstVariation μ D=
      H*directionalFlux O D.coordinate D.function := by rw [directionalFlux_congr_ae hOE]; exact hH D
  let v : AxisCircle → ℝ := fun t ↦ (axialSliceVolume O i t).toReal
  have hv : Continuous v := axialSliceVolume_continuous_of_boundary_null hO i
    (isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha)
  have hp : Function.Periodic (fun t : ℝ ↦ v (t : AxisCircle)) 1 := by
    intro t
    change v (((t+1 : ℝ) : AxisCircle))=v (t : AxisCircle)
    rw [AddCircle.coe_add_period]
  have hc : Continuous (fun t : ℝ ↦ v (t : AxisCircle)) := hv.comp (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨hac,hd⟩ := isMinimizerAt_slice_absolutelyContinuous hV hE hmin hμ i ha
  have hb := circle_ac_weighted_oscillation hp hc hac (axialNormalDensity_integrable μ i).neg hd hγ hγb hτ
  have hlift (t : AxisCircle) : hp.lift t=v t := by
    induction t using Quotient.inductionOn with | h t => rfl
  simp only [hlift,Pi.neg_apply,abs_neg,AddCircle.coe_zero] at hb
  have hsmall : Integrable (fun t ↦ γ (v t)*|axialNormalDensity μ i t|) := by
    simpa only [mul_comm,Function.comp_apply] using integrable_mul_unit (axialNormalDensity_integrable μ i).abs
      (hγ.comp hv).measurable (fun t ↦ by change |γ (v t)|≤1; rw [abs_of_nonneg (hγb _).1]; exact (hγb _).2)
  have hwEq : (fun t ↦ Nesting.weight (actualAxialFlux O μ H i t/axialPerimeterDensity μ i t)*
      |axialNormalDensity μ i t|)=ᵐ[volume](fun t ↦ Nesting.weight
        (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*|axialNormalDensity μ i t|) := by
    filter_upwards [axialSurface_density_eq_flux hO hHO i] with t ht
    rw [←ht]
    rfl
  have hlarge := (axial_weighted_normal_integrable μ i).congr hwEq.symm
  have him := integral_mono_ae hsmall hlarge (by
    filter_upwards [hγw] with t ht
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _))
  have hflux := axial_integrated_flux_actual hO hμO hHO i ha
  rw [perimeter_congr_ae hOE] at hflux
  change _≤(perimeter E).toReal
  have hh := hb.trans him
  exact (add_le_add le_rfl hh).trans hflux

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma real_measure_le_of_unit_continuous {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hh : ∀ f : ℝ → ℝ,Continuous f → (∀ x,f x∈Icc 0 1) →
      (∫ x,f x ∂μ)≤∫ x,f x ∂ν) : μ≤ν := by
  have hcompact ⦃K : Set ℝ⦄ (hK : IsCompact K) : μ K≤ν K := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hν ↦ ?_
    have hνK : ν K≠⊤ := hν.ne
    have hμK : μ K≠⊤ := hK.measure_lt_top.ne
    obtain ⟨V,pV1,pV2,pV3⟩ : ∃ V⊇K,IsOpen V ∧ ν V≤ν K+ε :=
      exists_isOpen_le_add K ν (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
    suffices μ.real K≤ν.real K+ε by
      rwa [←ENNReal.toReal_le_toReal,ENNReal.toReal_add,ENNReal.coe_toReal]
      all_goals finiteness
    obtain ⟨f,hf1,hf2,hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK pV2 pV1
    have hfiμ : Integrable f μ := (f.continuous.integrable_of_hasCompactSupport (hasCompactSupport_def.mpr hf2))
    have hfiν : Integrable f ν := (f.continuous.integrable_of_hasCompactSupport (hasCompactSupport_def.mpr hf2))
    have hfV (x : ℝ) : f x≤V.indicator 1 x := by
      by_cases hx : x∈tsupport f
      · simp [(hf3.1 hx),(hf3.2 x).2]
      · simp [image_eq_zero_of_notMem_tsupport hx,Set.indicator_nonneg]
    have hfK (x : ℝ) : K.indicator 1 x≤f x := by
      by_cases hx : x∈K
      · simp [hx,hf1 hx]
      · simp [hx,(hf3.2 x).1]
    calc
      μ.real K=(∫ x,K.indicator 1 x ∂μ) := (integral_indicator_one hK.measurableSet).symm
      _≤∫ x,f x ∂μ := integral_mono
        ((integrable_const (1 : ℝ)).indicator hK.measurableSet) hfiμ hfK
      _≤∫ x,f x ∂ν := hh f f.continuous hf3.2
      _≤∫ x,V.indicator 1 x ∂ν := integral_mono hfiν
        ((integrable_const (1 : ℝ)).indicator pV2.measurableSet) hfV
      _≤(ν K).toReal+↑ε := by
        rwa [integral_indicator_one pV2.measurableSet,measureReal_def,
          ←ENNReal.coe_toReal,←ENNReal.toReal_add,ENNReal.toReal_le_toReal]
        all_goals finiteness
  intro s
  apply (measure_mono (subset_toMeasurable ν s)).trans
  have hsm := measurableSet_toMeasurable ν s
  rw [hsm.measure_eq_iSup_isCompact μ]
  apply iSup_le
  intro K
  apply iSup_le
  intro hKs
  apply iSup_le
  intro hK
  exact (hcompact hK).trans (by simpa only [measure_toMeasurable] using measure_mono (μ := ν) hKs)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem circle_ac_measurable_weight_integrable {f : ℝ → ℝ} {g : AxisCircle → ℝ}
    (hp : Function.Periodic f 1) (hc : Continuous f)
    (hf : ∀ a b,AbsolutelyContinuousOnInterval f a b) (hgi : Integrable g)
    (hd : ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt f (g (t : AxisCircle)) t)
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγn : ∀ x,0≤γ x)
    (hγgi : Integrable (fun s ↦ γ (hp.lift s)*|g s|))
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    2*|∫ y in f 0..f t,γ y|≤∫ s,γ (hp.lift s)*|g s| := by
  let ρ : Measure AxisCircle := volume.withDensity (fun s ↦ ENNReal.ofReal |g s|)
  have hfin : (∫⁻ s,ENNReal.ofReal |g s|)≠⊤ :=
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun s ↦ abs_nonneg (g s)))).mp hgi.abs.2).ne
  let : IsFiniteMeasure ρ := isFiniteMeasure_withDensity hfin
  let ν : Measure ℝ := Measure.map hp.lift ρ
  let μ : Measure ℝ := (2 : ℝ≥0∞) • volume.restrict (uIoc (f 0) (f t))
  have : IsFiniteMeasure (volume.restrict (uIoc (f 0) (f t))) := by
    unfold uIoc
    infer_instance
  have : IsFiniteMeasure μ := by
    exact Measure.smul_finite _ (by norm_num)
  have hpc : Continuous hp.lift := continuous_periodic_lift hp hc
  have hpair (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
      (∫ y,ψ y ∂ν)=∫ s,ψ (hp.lift s)*|g s| := by
    rw [show ν=Measure.map hp.lift ρ from rfl,
      integral_map hpc.measurable.aemeasurable hψ.aestronglyMeasurable]
    rw [show ρ=volume.withDensity (fun s ↦ ENNReal.ofReal |g s|) from rfl,
      integral_withDensity_eq_integral_toReal_smul₀ hgi.aemeasurable.abs.ennreal_ofReal
        (Eventually.of_forall (fun s ↦ ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,mul_comm]
  have hleft (ψ : ℝ → ℝ) (hn : ∀ x,0≤ψ x) :
      (∫ y,ψ y ∂μ)=2*|∫ y in f 0..f t,ψ y| := by
    rw [show μ=(2 : ℝ≥0∞) • volume.restrict (uIoc (f 0) (f t)) from rfl,
      integral_smul_measure,intervalIntegral.abs_integral_eq_abs_integral_uIoc,
      abs_of_nonneg (integral_nonneg hn)]
    norm_num
  have horder : μ≤ν := by
    apply real_measure_le_of_unit_continuous
    intro ψ hψ hb
    rw [hpair ψ hψ.measurable,hleft ψ (fun x ↦ (hb x).1)]
    exact circle_ac_weighted_oscillation hp hc hf hgi hd hψ hb ht
  have hγi : Integrable γ ν := by
    apply (integrable_map_measure hγ.aestronglyMeasurable hpc.measurable.aemeasurable).mpr
    apply (integrable_withDensity_iff_integrable_smul₀'
      hgi.aemeasurable.abs.ennreal_ofReal
      (Eventually.of_forall (fun s ↦ ENNReal.ofReal_lt_top))).mpr
    simpa only [Function.comp_apply,ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,mul_comm] using hγgi
  have hh := integral_mono_measure horder (Eventually.of_forall hγn) hγi
  rwa [hpair γ hγ,hleft γ hγn] at hh

theorem circle_ac_measurable_weight {f : ℝ → ℝ} {g : AxisCircle → ℝ}
    (hp : Function.Periodic f 1) (hc : Continuous f)
    (hf : ∀ a b,AbsolutelyContinuousOnInterval f a b) (hgi : Integrable g)
    (hd : ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt f (g (t : AxisCircle)) t)
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγb : ∀ x,γ x∈Icc 0 1)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    2*|∫ y in f 0..f t,γ y|≤∫ s,γ (hp.lift s)*|g s| := by
  apply circle_ac_measurable_weight_integrable hp hc hf hgi hd hγ (fun x ↦ (hγb x).1) ?_ ht
  simpa only [mul_comm,Function.comp_apply] using integrable_mul_unit hgi.abs
    (hγ.comp (continuous_periodic_lift hp hc).measurable)
    (fun x ↦ by change |γ (hp.lift x)|≤1; rw [abs_of_nonneg (hγb _).1]; exact (hγb _).2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
