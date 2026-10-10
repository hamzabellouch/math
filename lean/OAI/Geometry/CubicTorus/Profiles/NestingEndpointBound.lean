import Mathlib
import OAI.Geometry.CubicTorus.Profiles.SectionExtentBounds

namespace OAI

section
section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Shape

theorem uniform_coefficient {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    min ((134 / 1000 : ℝ) * h ^ 3) (36 / 100 : ℝ) ≤
      ((91 / 100 : ℝ) * c * moment / Real.sqrt p₂ ^ 3) *
        (h * (u h - (1 - meanQ) * dm)) ^ 3 := by
  let d₀ : ℝ := (1 - meanQ) * dm
  have hd0 : 0 ≤ d₀ := mul_nonneg (by linarith [meanQ_mem.2]) (by norm_num [dm])
  have hd : d₀ ≤ (6363 / 100000 : ℝ) := by
    dsimp [d₀, dm]
    linarith [moment_bounds.2.1]
  have hh0 : 0 < h := by linarith [hh.1]
  have hc := coefficient_lower
  by_cases hbranch : 1 - 1 / Real.pi ≤ (24 / 25 : ℝ) / h
  · have hip : 1 / Real.pi ≤ (1 / (314 / 100) : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [Real.pi_gt_d2])
    have hb : (617 / 1000 : ℝ) ≤ 1 - 1 / Real.pi - d₀ := by linarith
    have hbase : (617 / 1000 : ℝ) * h ≤ h * (u h - d₀) := by
      dsimp [u]
      rw [min_eq_left hbranch]
      nlinarith [mul_le_mul_of_nonneg_left hb (le_of_lt hh0)]
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (617 / 1000 : ℝ) * h) hbase 3
    have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 574 / 1000)
    have hmc := mul_le_mul_of_nonneg_right (le_of_lt hc)
      (pow_nonneg (le_trans (by positivity : (0 : ℝ) ≤ (617 / 1000 : ℝ) * h) hbase) 3)
    apply le_trans (min_le_left _ _) _
    change (134 / 1000 : ℝ) * h ^ 3 ≤ _ * (h * (u h - d₀)) ^ 3
    nlinarith only [hm, hmc, pow_pos hh0 3]
  · have hbranch' : (24 / 25 : ℝ) / h ≤ 1 - 1 / Real.pi := le_of_not_ge hbranch
    have hprod : h * d₀ ≤ (81 / 50 : ℝ) * (6363 / 100000 : ℝ) :=
      mul_le_mul hh.2 hd hd0 (by norm_num)
    have hbase : (856 / 1000 : ℝ) ≤ h * (u h - d₀) := by
      dsimp [u]
      rw [min_eq_right hbranch']
      have heq : h * ((24 / 25 : ℝ) / h - d₀) = 24 / 25 - h * d₀ := by
        field_simp
      rw [heq]
      linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 856 / 1000) hbase 3
    have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 574 / 1000)
    have hmc := mul_le_mul_of_nonneg_right (le_of_lt hc)
      (pow_nonneg (by linarith : 0 ≤ h * (u h - d₀)) 3)
    apply le_trans (min_le_right _ _) _
    change (36 / 100 : ℝ) ≤ _ * (h * (u h - d₀)) ^ 3
    nlinarith only [hm, hmc]

end CubicTorus.Shape

namespace CubicTorus.NestingGain
open CubicTorus.Nesting CubicTorus.Shape

lemma continuousOn_weight : ContinuousOn weight (Ici 0) := by
  exact Nesting.continuousOn_rawWeight.comp
    (continuous_id.min continuous_const).continuousOn
    (fun x hx => ⟨le_min hx (le_of_lt cutoff_pos), min_le_right _ _⟩)

lemma nesting_parameters {h δ q : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
    (hδ : δ ∈ Icc 0 dm) (hq : q ∈ Icc 0 1) :
    h * (u h - δ + δ * q) ∈ Icc 0 (24 / 25 : ℝ) ∧
      0 ≤ c * δ ^ 2 * shape q ∧ 1 + c * δ ^ 2 * shape q ≤ p₂ := by
  have hu := interval_placement hh
  have hh0 : 0 ≤ h := by linarith [hh.1]
  have hv0 : 0 ≤ u h - δ + δ * q := by
    have := mul_nonneg hδ.1 hq.1
    linarith [hu.2.1, hδ.2]
  have hv1 : u h - δ + δ * q ≤ u h := by
    have := mul_le_mul_of_nonneg_left hq.2 hδ.1
    linarith
  have hK0 : 0 ≤ c * δ ^ 2 * shape q := by
    exact mul_nonneg (mul_nonneg (by norm_num [c]) (sq_nonneg δ)) (shape_nonneg hq)
  have hK1 : c * δ ^ 2 * shape q ≤ c * dm ^ 2 * theta ^ 2 := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hδ.1 hδ.2 2) (by norm_num [c])) (shape_max hq)
      (shape_nonneg hq) (by norm_num [c, dm])
  exact ⟨⟨mul_nonneg hh0 hv0,
    le_trans (mul_le_mul_of_nonneg_left hv1 hh0) hu.2.2.2.2.2⟩,
    hK0, by dsimp [p₂]; linarith⟩

lemma pointwise_uniform_gain {h δ q : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
    (hδ : δ ∈ Icc 0 dm) (hq : q ∈ Icc 0 1) :
    ((91 / 100 : ℝ) * c * δ ^ 2 * h ^ 3 / Real.sqrt p₂ ^ 3) *
        ((u h - δ + δ * q) ^ 3 * shape q) ≤
      weight ((h * (u h - δ + δ * q)) / Real.sqrt (1 + c * δ ^ 2 * shape q)) -
        weight (h * (u h - δ + δ * q)) := by
  have hp := nesting_parameters hh hδ hq
  have hlow := pointwise_weight_gain hp.1 hp.2.1
  apply le_trans _ hlow
  have hnum : 0 ≤ (91 / 100 : ℝ) * (h * (u h - δ + δ * q)) ^ 3 *
      (c * δ ^ 2 * shape q) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp.1.1 3)) hp.2.1
  have hden : (Real.sqrt (1 + c * δ ^ 2 * shape q)) ^ 3 ≤ Real.sqrt p₂ ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hp.2.2) 3
  have hden0 : 0 < (Real.sqrt (1 + c * δ ^ 2 * shape q)) ^ 3 := by
    apply pow_pos
    apply Real.sqrt_pos.2
    linarith [hp.2.1]
  convert div_le_div_of_nonneg_left hnum hden0 hden using 1
  ring

theorem integrated_uniform_gain {h δ : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) (hδ : δ ∈ Icc 0 dm) :
    min ((134 / 1000 : ℝ) * h ^ 3) (36 / 100 : ℝ) * δ ^ 3 ≤
      δ * ∫ q in (0 : ℝ)..1,
        (weight ((h * (u h - δ + δ * q)) / Real.sqrt (1 + c * δ ^ 2 * shape q)) -
          weight (h * (u h - δ + δ * q))) := by
  let v : ℝ → ℝ := fun q => u h - δ + δ * q
  let K : ℝ → ℝ := fun q => c * δ ^ 2 * shape q
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hK : Continuous K := by dsimp [K]; exact continuous_const.mul continuous_shape
  have hc1 : ContinuousOn (fun q => weight ((h * v q) / Real.sqrt (1 + K q))) (Icc 0 1) := by
    apply continuousOn_weight.comp
    · apply (continuous_const.mul hv).continuousOn.div
        (Real.continuous_sqrt.comp (continuous_const.add hK)).continuousOn
      intro q hq
      exact ne_of_gt (Real.sqrt_pos.2 (by
        change 0 < 1 + c * δ ^ 2 * shape q
        linarith [(nesting_parameters hh hδ hq).2.1]))
    · intro q hq
      exact div_nonneg (nesting_parameters hh hδ hq).1.1 (Real.sqrt_nonneg _)
  have hc2 : ContinuousOn (fun q => weight (h * v q)) (Icc 0 1) :=
    continuousOn_weight.comp (continuous_const.mul hv).continuousOn
      (fun q hq => (nesting_parameters hh hδ hq).1.1)
  have hright : IntervalIntegrable (fun q => weight ((h * v q) / Real.sqrt (1 + K q)) -
      weight (h * v q)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (hc1.sub hc2)
  let A : ℝ := (91 / 100 : ℝ) * c * δ ^ 2 * h ^ 3 / Real.sqrt p₂ ^ 3
  have hleft : IntervalIntegrable (fun q => A * (v q ^ 3 * shape q)) volume 0 1 :=
    (continuous_const.mul ((hv.pow 3).mul continuous_shape)).intervalIntegrable 0 1
  have hmon := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    hleft hright (fun q hq => pointwise_uniform_gain hh hδ hq)
  rw [intervalIntegral.integral_const_mul] at hmon
  have hA : 0 ≤ A := by
    have hh0 : 0 ≤ h := by linarith [hh.1]
    dsimp [A, c]
    positivity
  have hu : dm ≤ u h := by linarith [(interval_placement hh).2.1]
  have hcubic := mul_le_mul_of_nonneg_left (cubic_shape_lower_dm hδ hu) hA
  have hδlower := mul_le_mul_of_nonneg_left (le_trans hcubic hmon) hδ.1
  have hcoeff := mul_le_mul_of_nonneg_right (uniform_coefficient hh) (pow_nonneg hδ.1 3)
  apply le_trans hcoeff
  convert hδlower using 1
  dsimp [A, v, K]
  ring

end CubicTorus.NestingGain

end
end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSectionCenter_complement (b : Fin 3 →Bool) (i : Fin 3) (y : TransverseProduct) :
    (fun j ↦ y j+((1/2 : ℝ) : AxisCircle))+axialSectionCenter (fun k ↦ !b k) i=
      y+axialSectionCenter b i := by
  ext j
  simp only [Pi.add_apply,axialSectionCenter]
  by_cases hb : b (i.succAbove j)=true
  · simp [hb]
  · have hf : b (i.succAbove j)=false := Bool.eq_false_iff.mpr hb
    simp only [hf,Bool.not_false,ite_true,Bool.false_eq_true,ite_false,add_zero]
    rw [add_assoc,←AddCircle.coe_add]
    norm_num [AddCircle.coe_period]

theorem isMinimizerAt_nested_edge_bound {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (j : Fin 2) {L : ℝ}
    (hfill : ∀ y : TransverseProduct,(∀ k : Fin 2,k≠j →y k=0) →2*‖y j‖<L →
      y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (octantHeight b i 0 : AxisCircle))
    {z : ℝ} (hz : z∈Icc (0 : ℝ) 1) {y : TransverseProduct}
    (hy : y∈closure (centeredAxialSlice (openRepresentative E) b i (octantHeight b i z : AxisCircle)))
    (hedge : ∀ k : Fin 2,k≠j →y k=((1/2 : ℝ) : AxisCircle)) :
    2*‖y j‖≤1-L := by
  have hsub : centeredAxialSlice (openRepresentative E) b i (octantHeight b i z : AxisCircle)⊆
      centeredAxialSlice (openRepresentative E) b i (octantHeight b i 0 : AxisCircle) :=
    preimage_mono (isMinimizerAt_axialSlice_antitone hV hmin hR hd i ⟨by norm_num,by norm_num⟩ hz hz.1)
  have hy0 := centeredAxialSlice_closure_subset (openRepresentative E) b i (octantHeight b i 0 : AxisCircle)
    (closure_mono hsub hy)
  by_contra hn
  have hh : 2*‖y j+((1/2 : ℝ) : AxisCircle)‖<L := by
    rw [axisCircle_norm_add_half]
    linarith
  have hyc := hfill (fun k ↦ y k+((1/2 : ℝ) : AxisCircle)) (fun k hk ↦ by
    rw [hedge k hk,←AddCircle.coe_add]
    norm_num [AddCircle.coe_period]) hh
  rw [openRepresentative_compl_eq hV hmin] at hyc
  change (torusAxialSplit i).symm ((octantHeight b i 0 : AxisCircle),
    (fun k ↦ y k+((1/2 : ℝ) : AxisCircle))+axialSectionCenter (fun k ↦ !b k) i)∉closure (openRepresentative E) at hyc
  rw [axialSectionCenter_complement] at hyc
  exact hyc hy0

theorem isMinimizerAt_bottom_nested_endpoint {V : ℝ} (hV : V∈Ioo 0 1)
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
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    ∀ j : Fin 2,∀ z∈Icc (0 : ℝ) 1,∀ y∈closure (centeredAxialSlice (openRepresentative E) b i (octantHeight b i z : AxisCircle)),
      (∀ k : Fin 2,k≠j →y k=((1/2 : ℝ) : AxisCircle)) →
      2*‖y j‖≤1-2/Real.pi*((H/2)*s-Real.sqrt ((H/2)^2*s^2-Real.pi*(1-s))) := by
  intro s j z hz y hy hedge
  obtain ⟨_,_,hb⟩ := isMinimizerAt_bottom_both_extents hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1
  obtain ⟨L,hL,hband,hfill,hcal⟩ := hb j
  have he := isMinimizerAt_nested_edge_bound hV hmin hR hd i j hfill hz hy hedge
  have hlow := Shape.extent_lower_bound hL.1 hcal
  dsimp only [s]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def nestingEndpointBound (h s : ℝ) : ℝ :=
  1-2*h*Shape.t h/Real.pi+(2/Real.pi)*Real.sqrt (Real.pi+2*h^2*Shape.t h)*Real.sqrt (s-Shape.t h)

def nestingDelta (h s : ℝ) : ℝ := min Shape.dm (max (Shape.u h-nestingEndpointBound h s) 0)

lemma nestingDelta_mem (h s : ℝ) : nestingDelta h s∈Icc 0 Shape.dm := by
  exact ⟨le_min (by norm_num [Shape.dm]) (le_max_right _ _),min_le_left _ _⟩

lemma nestingDelta_gap {h s : ℝ} (hh : h∈Icc (51/50 : ℝ) (81/50 : ℝ))
    (hd : 0<nestingDelta h s) : max 0 (nestingEndpointBound h s)≤Shape.u h-nestingDelta h s := by
  have hpos : 0<Shape.u h-nestingEndpointBound h s := by
    have hm : 0 < max (Shape.u h-nestingEndpointBound h s) 0 :=
      hd.trans_le (min_le_right _ _)
    exact (lt_max_iff.mp hm).resolve_right (lt_irrefl _)
  have hsub : nestingDelta h s≤Shape.u h-nestingEndpointBound h s := by
    dsimp only [nestingDelta]
    rw [max_eq_left hpos.le]
    exact min_le_right _ _
  have hplace := (Shape.interval_placement hh).2.1
  have hcap := (nestingDelta_mem h s).2
  apply max_le <;> linarith

lemma source_root_le_of_bottom {h s : ℝ} (hh : 0<h) (hs : 0 ≤ s)
    (hdisc : Real.pi*(1-s)≤(h*s)^2) : Shape.t h ≤ s := by
  have ht := Shape.t_spec hh
  by_contra hn
  have hst : s<Shape.t h := lt_of_not_ge hn
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 2) (sq_nonneg h)
  have hp := mul_lt_mul_of_pos_left hst Real.pi_pos
  nlinarith [ht.2.2]

lemma nestingEndpointBound_ge_exact {h s : ℝ} (hh : 0<h) (hs : 0 ≤ s)
    (hdisc : Real.pi*(1-s)≤(h*s)^2) :
    1-2/Real.pi*(h*s-Real.sqrt (h^2*s^2-Real.pi*(1-s)))≤nestingEndpointBound h s := by
  have ht := Shape.t_spec hh
  have hts := source_root_le_of_bottom hh hs hdisc
  have hb := Shape.endpoint_slack_bound hh.le ht.1.le hts ht.2.2
  simpa only [nestingEndpointBound] using hb

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_graph_axis_boundary_isolated {O : Set Torus} {a n : Cover}
    (hn : ‖n‖=1) (i : Fin 3) (hz : ∀ k : Fin 3,k≠i →n k=0)
    {f : Plane →ℝ} (hf : f 0=0)
    (hchart : ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (a+v)∈frontier O ↔
      normalGraph n f (normalPlaneCoordinates n v)=v) :
    ∀ᶠ u in 𝓝 (a i),quotientMap (a+(u-a i) • EuclideanSpace.single i 1)∈frontier O →u=a i := by
  have hni : n i≠0 := by
    intro hh
    have he : n=0 := by ext k; by_cases hk : k=i; subst k; exact hh; simpa using hz k hk
    rw [he,norm_zero] at hn
    norm_num at hn
  let v : ℝ → Cover := fun u ↦ (u-a i) • EuclideanSpace.single i 1
  have hv (u : ℝ) : v u=((u-a i)/n i) • n := by
    ext k
    by_cases hk : k=i
    · subst k
      simp only [v,PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
      field_simp
    · simp [v,hk,hz k hk]
  have hc : Tendsto v (𝓝 (a i)) (𝓝 (0 : Cover)) := by
    have hcv : Continuous v := by dsimp only [v]; fun_prop
    simpa [v] using hcv.tendsto (a i)
  filter_upwards [hc.eventually hchart] with u hu hmem
  have he := hu.mp hmem
  have hzero : normalGraph n f (normalPlaneCoordinates n (v u))=0 := by
    rw [hv,map_smul,normalPlaneCoordinates_normal hn,smul_zero]
    change (normalPlaneLinearIsometry n) 0+f 0 • n=0
    rw [map_zero,hf,zero_smul,add_zero]
  change normalGraph n f (normalPlaneCoordinates n (v u))=v u at he
  rw [hzero] at he
  have hh := congrArg (fun x : Cover ↦ x i) he
  simp [v] at hh
  linarith

lemma axialSectionCorner_motion (b : Fin 3 →Bool) (i : Fin 3) (t u : ℝ) (n : Fin 2 →Bool) :
    axialSectionCorner b i u n=axialSectionCorner b i t n+(u-t) • EuclideanSpace.single i 1 := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨j,rfl⟩
  · simp
  · simp [Fin.succAbove_ne]

lemma octantHeight_endpoint_fixed (b : Fin 3 →Bool) (k : Fin 3) (c : Bool) :
    -((octantHeight b k (if c then 1 else 0) : ℝ) : AxisCircle)=
      ((octantHeight b k (if c then 1 else 0) : ℝ) : AxisCircle) := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [←AddCircle.coe_add]
  cases hb : b k <;> cases c <;> norm_num [octantHeight,hb,AddCircle.coe_period] <;> exact ⟨(2 : ℤ),by norm_num⟩

lemma axialSectionCorner_fixed (b : Fin 3 →Bool) (i : Fin 3) (t : ℝ) (n : Fin 2 →Bool) (j : Fin 2) :
    (axisReflection (i.succAbove j)).torus (quotientMap (axialSectionCorner b i t n))=
      quotientMap (axialSectionCorner b i t n) := by
  ext k
  rw [axisReflection_torus_apply]
  split_ifs with hk
  · subst k
    change -((axialSectionCorner b i t n (i.succAbove j) : ℝ) : AxisCircle)=((axialSectionCorner b i t n (i.succAbove j) : ℝ) : AxisCircle)
    rw [axialSectionCorner_other]
    exact octantHeight_endpoint_fixed b _ _
  · rfl

theorem isMinimizerAt_corner_boundary_heights_discrete {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool) (i : Fin 3) (n : Fin 2 →Bool) :
    IsDiscrete {t : ℝ | quotientMap (axialSectionCorner b i t n)∈frontier (openRepresentative E)} := by
  obtain ⟨μ,H,N,hN,hp,hμ,haN,hb,hs,hj,hu⟩ := Periodic.isMinimizerAt_H1_translation_jacobi hV hE hmin
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro t ht
  let a := axialSectionCorner b i t n
  have ha : quotientMap a∈frontier (openRepresentative E) := ht
  have hz (k : Fin 3) (hk : k≠i) : N a k=0 := by
    rcases Fin.eq_self_or_eq_succAbove i k with hi|⟨j,rfl⟩
    · exact (hk hi).elim
    · exact isMinimizerAt_axis_fixed_normal_zero hV hE hmin _ (hR _) hμ hN hp haN a ha
        (axialSectionCorner_fixed b i t n j)
  obtain ⟨f,hf,hf0,hgrad,hg,hchart⟩ := isMinimizerAt_normalized_CMC_chart hV hE hmin hμ hN hp haN (fun x hx ↦ ⟨(hb x hx).1,(hb x hx).2.1⟩) a ha
  have hlocal := normal_graph_axis_boundary_isolated (hb a ha).1.self_of_nhds i hz hf0 hchart
  have hl : ∀ᶠ u in 𝓝 t,quotientMap (axialSectionCorner b i u n)∈frontier (openRepresentative E) →u=t := by
    simpa only [a,axialSectionCorner_same,←axialSectionCorner_motion] using hlocal
  obtain ⟨U,hUs,hU,htU⟩ := _root_.mem_nhds_iff.mp hl
  refine ⟨U,hU,?_⟩
  ext u
  constructor
  · intro hu
    exact mem_singleton_iff.mpr (hUs hu.1 hu.2)
  · rintro rfl
    exact ⟨htU,ht⟩

theorem isMinimizerAt_corner_boundary_heights_null {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool) (i : Fin 3) (n : Fin 2 →Bool) :
    volume {t : ℝ | quotientMap (axialSectionCorner b i t n)∈frontier (openRepresentative E)}=0 := by
  have hd := isMinimizerAt_corner_boundary_heights_discrete hV hE hmin hR b i n
  exact (IsLindelof.countable_of_isDiscrete (IsLindelof.of_coe) hd).measure_zero volume

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def unitPlanarProfile (s : ℝ) : ℝ :=
  min (2*Real.sqrt (Real.pi*s)) (min 2 (2*Real.sqrt (Real.pi*(1-s))))

lemma unitPlanarProfile_zero : unitPlanarProfile 0=0 := by
  simp [unitPlanarProfile,le_min (by norm_num : (0 : ℝ)≤2) (by positivity : 0≤2*Real.sqrt Real.pi)]

lemma unitPlanarProfile_one : unitPlanarProfile 1=0 := by
  simp [unitPlanarProfile,Real.sqrt_nonneg]

lemma unitPlanarProfile_nonneg (s : ℝ) : 0≤unitPlanarProfile s := by
  dsimp only [unitPlanarProfile]
  exact le_min (by positivity) (le_min (by norm_num) (by positivity))

lemma open_outside_closure_of_not_frontier {X : Type*} [TopologicalSpace X]
    {O : Set X} (ho : IsOpen O) {x : X} (hx : x∉frontier O) (hn : x∉O) : x∉closure O := by
  intro hc
  exact hx ⟨hc,by simpa only [ho.interior_eq] using hn⟩

theorem isMinimizerAt_section_planar_profile {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) {t : ℝ} (ht : t∈Icc (1/2 : ℝ) 1)
    (hc : ∀ n : Fin 2 →Bool,quotientMap (axialSectionCorner b i t n)∉frontier (openRepresentative E))
    (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0) :
    ENNReal.ofReal (unitPlanarProfile (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))))≤
      planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  let A := centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)
  have hr : PlanarRadialDownset A := isMinimizerAt_centered_section_radial hV hmin hR hd i _
  have hv : volume.real A=volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)) :=
    centeredAxialSlice_volume _ b i _
  have hcorner (n : Fin 2 →Bool) : planarSquareCorner n∈A ↔
      quotientMap (axialSectionCorner b i t n)∈openRepresentative E := by
    change (torusAxialSplit i).symm ((t : AxisCircle),planarSquareCorner n+axialSectionCenter b i)∈openRepresentative E ↔ _
    rw [centered_section_corner]
  have hout (n : Fin 2 →Bool) (hn : quotientMap (axialSectionCorner b i t n)∉openRepresentative E) :
      quotientMap (axialSectionCorner b i t n)∉closure (openRepresentative E) :=
    open_outside_closure_of_not_frontier (isOpen_openRepresentative E) (hc n) hn
  by_cases hnear : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E
  · by_cases hfar : quotientMap (axialSectionCorner b i t (fun _ ↦ true))∈openRepresentative E
    · have hAu : A=univ := by
        apply eq_univ_of_forall
        intro y
        apply hr _ _ (fun j ↦ ?_) ((hcorner _).mpr hfar)
        simp only [planarSquareCorner,ite_true]
        rw [axisCircle_norm_coe_small (by norm_num : |(1/2 : ℝ)|≤1/2)]
        simpa using axisCircle_norm_le_half (y j)
      have hs : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))=1 := by
        rw [←hv,hAu]; simp
      rw [hs,unitPlanarProfile_one,ENNReal.ofReal_zero]
      exact bot_le
    · by_cases h0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∈openRepresentative E
      · by_cases h1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∈openRepresentative E
        · obtain ⟨L,hL,hband,hcal,hp⟩ := isMinimizerAt_section_complement_calibration hV hmin hR hd i t (hout _ hfar) h0 h1 hn
          exact (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_right _ _))).trans hp
        · have he0 : (fun k : Fin 2 ↦ if k=1 then false else true)=(fun k ↦ k==0) := by
            funext k; fin_cases k <;> decide
          have he1 : (fun k : Fin 2 ↦ if k=1 then true else false)=(fun k ↦ k==1) := by
            funext k; fin_cases k <;> decide
          have hp := isMinimizerAt_section_strip_perimeter hV hmin hR hd i 1 ht (by rwa [he0]) (by rw [he1]; exact hout _ h1)
          exact (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _))).trans (by simpa using hp)
      · by_cases h1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∈openRepresentative E
        · have he0 : (fun k : Fin 2 ↦ if k=0 then false else true)=(fun k ↦ k==1) := by
            funext k; fin_cases k <;> decide
          have he1 : (fun k : Fin 2 ↦ if k=0 then true else false)=(fun k ↦ k==0) := by
            funext k; fin_cases k <;> decide
          have hp := isMinimizerAt_section_strip_perimeter hV hmin hR hd i 0 ht (by rwa [he0]) (by rw [he1]; exact hout _ h0)
          exact (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _))).trans (by simpa using hp)
        · exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans
            (isMinimizerAt_section_disk_perimeter hV hmin hR hd i t hnear (hout _ h0) (hout _ h1))
  · have hAe : A=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      apply hnear
      apply (hcorner _).mp
      apply hr _ _ _ hy
      intro j
      simp only [planarSquareCorner,Bool.false_eq_true,ite_false,norm_zero]
      exact norm_nonneg _
    have hs : volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))=0 := by
      rw [←hv,hAe]; simp
    rw [hs,unitPlanarProfile_zero,ENNReal.ofReal_zero]
    exact bot_le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planarTorusPerimeter_ge_weighted_derivative_flux
    {A : Set TransverseProduct} (hA : MeasurableSet A)
    {T : Set AxisCircle} (hT : MeasurableSet T)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ y,0≤u y) (huv : ∀ y,(u y)^2+(v y)^2≤1)
    {b : ℝ → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbi : Integrable b volume)
    (hb0 : ∀ t,0≤b t) (hb1 : ∫ t,b t=1)
    {r a c : ℝ} (hs : tsupport b ⊆ Icc (-r) r) (hac : a≤c)
    (hshort : c-a+2*r<1)
    (hin : ∀ t : ℝ,b (t-a)≠0 → ∀ y : TransverseProduct,y 0=(t : AxisCircle) → y 1∈T → y∈A)
    (hout : ∀ t : ℝ,b (t-c)≠0 → ∀ y : TransverseProduct,y 0=(t : AxisCircle) → y∉A)
    : ENNReal.ofReal ((∫ y in A,(real_periodic_deriv pv).lift (y 1))+
        2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  let H := intervalSmoothHat b a c
  let d := (a+c)/2
  have hHs : tsupport H ⊆ Ioo (d-1/2) (d+1/2) := by
    apply (intervalSmoothHat_support hb.continuous hs hac).trans
    intro x hx
    dsimp only [d]
    constructor <;> linarith [hx.1,hx.2]
  have hHc : HasCompactSupport H :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport H)
      (intervalSmoothHat_support hb.continuous hs hac)
  let B : ℝ → ℝ := fun t ↦ b (t-a)
  have hBs : tsupport B ⊆ Ioo (d-1/2) (d+1/2) := by
    intro t ht
    have hh := hs (tsupport_comp_subset_preimage b (continuous_id.sub continuous_const) ht)
    change -r≤t-a ∧ t-a≤r at hh
    dsimp only [d]
    constructor <;> linarith [hh.1,hh.2]
  have hBc : HasCompactSupport B :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport B)
      (fun _ ht ↦ ⟨(hBs ht).1.le,(hBs ht).2.le⟩)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hb.comp (contDiff_id.sub contDiff_const)
  let ψ : ℝ → ℝ := fun t ↦ 2*circlePeriodize H t-1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (contDiff_const.mul (circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc)).sub contDiff_const
  have hp : Function.Periodic ψ 1 := fun t ↦ by
    dsimp only [ψ]
    rw [circlePeriodize_periodic H t]
  have hbψ (t : ℝ) : |ψ t|≤1 := by
    have hh := circlePeriodize_unit_bounds hHs (fun t ↦
      ⟨intervalSmoothHat_nonneg hb.continuous hb0 hac t,
        intervalSmoothHat_le_one hb.continuous hbi hb0 hb1 hac t⟩) t
    apply abs_le.mpr
    dsimp only [ψ]
    constructor <;> linarith [hh.1,hh.2]
  have hd (t : ℝ) (ht : t∈Icc (d-1/2) (d+1/2)) : deriv ψ t=2*(b (t-a)-b (t-c)) := by
    have he := circlePeriodize_eventuallyEq hHc hHs ht
    dsimp only [ψ]
    rw [deriv_sub_const,deriv_const_mul 2
      ((circlePeriodize_contDiff (intervalSmoothHat_contDiff hb a c) hHc).differentiable (by simp) t),
      he.deriv_eq,(intervalSmoothHat_hasDerivAt hb.continuous a c t).deriv]
  let β : AxisCircle → ℝ := (circlePeriodize_periodic B).lift
  have hβ : Continuous β := continuous_periodic_lift _ (circlePeriodize_contDiff hB hBc).continuous
  have hβi : (∫ t,β t)=1 := by
    rw [circlePeriodize_integral_short hBc hBs]
    exact (integral_sub_right_eq_self b a).trans hb1
  have huC : Continuous (pu.lift : AxisCircle → ℝ) := continuous_periodic_lift _ hu.continuous
  have hvC : Continuous ((real_periodic_deriv pv).lift : AxisCircle → ℝ) :=
    continuous_periodic_lift _ (hv.continuous_deriv (by simp))
  have hσC : Continuous ((real_periodic_deriv hp).lift : AxisCircle → ℝ) :=
    continuous_periodic_lift _ (hψ.continuous_deriv (by simp))
  have huL (t : AxisCircle) : 0≤pu.lift t := by
    induction t using Quotient.inductionOn with | h t => exact hu0 t
  have he (y : TransverseProduct) :
      2*β (y 0)*(T.indicator pu.lift (y 1))≤
        A.indicator (fun y : TransverseProduct ↦ (real_periodic_deriv hp).lift (y 0)*pu.lift (y 1)) y := by
    let t : ℝ := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y 0) : ℝ)
    have ht0 := ((AddCircle.equivIco (1 : ℝ) (d-1/2)) (y 0)).property
    have ht : t∈Icc (d-1/2) (d+1/2) := by
      change d-1/2≤t ∧ t<d-1/2+1 at ht0
      constructor <;> linarith [ht0.1,ht0.2]
    have hty : (t : AxisCircle)=y 0 := (AddCircle.equivIco (1 : ℝ) (d-1/2)).symm_apply_apply _
    have hBt : β (y 0)=b (t-a) := by
      rw [←hty]
      exact (circlePeriodize_eventuallyEq hBc hBs ht).eq_of_nhds
    rw [hBt]
    by_cases hy : y∈A
    · have hc0 : b (t-c)=0 := by
        by_contra hnc
        exact hout t hnc y hty.symm hy
      rw [indicator_of_mem hy]
      have hd' : (real_periodic_deriv hp).lift (y 0)=2*b (t-a) := by
        rw [←hty]
        change deriv ψ t=2*b (t-a)
        rw [hd t ht,hc0,sub_zero]
      rw [hd']
      by_cases hyT : y 1∈T
      · rw [indicator_of_mem hyT]
      · rw [indicator_of_notMem hyT,mul_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (hb0 _)) (huL _)
    · rw [indicator_of_notMem hy]
      by_cases hyT : y 1∈T
      · have ha0 : b (t-a)=0 := by
          by_contra hna
          exact hy (hin t hna y hty.symm hyT)
        rw [ha0,mul_zero,zero_mul]
      · rw [indicator_of_notMem hyT,mul_zero]
  have hiR : Integrable (fun y : TransverseProduct ↦
      (real_periodic_deriv hp).lift (y 0)*pu.lift (y 1)) :=
    ((hσC.comp (continuous_apply 0)).mul (huC.comp (continuous_apply 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiL : Integrable (fun y : TransverseProduct ↦ 2*β (y 0)*T.indicator pu.lift (y 1)) := by
    have hbase : Integrable (fun y : TransverseProduct ↦ 2*β (y 0)*pu.lift (y 1)) :=
      ((continuous_const.mul (hβ.comp (continuous_apply 0))).mul (huC.comp (continuous_apply 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    apply (hbase.indicator (hT.preimage (measurable_pi_apply 1))).congr
    filter_upwards [] with y
    by_cases hy : y 1∈T <;> simp [hy]
  have hle := integral_mono hiL (hiR.indicator hA) he
  have hlow : (∫ y : TransverseProduct,2*β (y 0)*T.indicator pu.lift (y 1))=
      2*(∫ t in T,pu.lift t) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul,transverse_integral_mul,hβi,one_mul,integral_indicator hT]
  rw [hlow,integral_indicator hA] at hle
  have hvI : Integrable (fun y : TransverseProduct ↦ (real_periodic_deriv pv).lift (y 1)) :=
    (hvC.comp (continuous_apply 1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hflux := planarTorusPerimeter_ge_product_flux A hψ hu hv hp pu pv hbψ huv
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hflux
  rw [integral_add hiR.integrableOn hvI.integrableOn]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planarTorusPerimeter_ge_open_derivative_flux
    {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T)
    {u v : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ y,0≤u y) (huv : ∀ y,(u y)^2+(v y)^2≤1)
    {a c : ℝ} (hac : a≤c) (hshort : c-a<1)
    (hin : ∀ y : TransverseProduct,y 0=(a : AxisCircle) →y 1∈T →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=(c : AxisCircle) →y∉closure A)
    : ENNReal.ofReal ((∫ y in A,(real_periodic_deriv pv).lift (y 1))+
        2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  obtain ⟨ε,hε,hεA⟩ := planar_open_partial_fiber_collar hA hT a hin
  obtain ⟨δ,hδ,hδA⟩ := planar_open_fiber_collar isClosed_closure.isOpen_compl 0 c hout
  let r : ℝ := min (min ε δ) (1-(c-a))/4
  have hr : 0<r := by dsimp [r]; positivity
  have hrε : r<ε := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_left ε δ)
    dsimp only [r]; linarith
  have hrδ : r<δ := by
    have hh := (min_le_left (min ε δ) (1-(c-a))).trans (min_le_right ε δ)
    dsimp only [r]; linarith
  have hrc : c-a+2*r<1 := by
    have hh := min_le_right (min ε δ) (1-(c-a))
    dsimp only [r]; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r/2,r,half_pos hr,by linarith⟩
  apply planarTorusPerimeter_ge_weighted_derivative_flux hA.measurableSet hT.measurableSet
    hu hv pu pv hu0 huv b.contDiff_normed b.integrable_normed (fun t ↦ b.nonneg_normed t)
    b.integral_normed (r := r) (a := a) (c := c) _ hac hrc _ _
  · rw [b.tsupport_normed_eq,Real.closedBall_eq_Icc]
    simp only [sub_eq_add_neg,zero_add]
    exact Subset.rfl
  · intro t ht y hy hyT
    have hs : t-a∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]; exact ht
    have hab : |t-a|<r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hεA t (hab.trans hrε) y hy hyT
  · intro t ht y hy hya
    have hs : t-c∈Metric.ball (0 : ℝ) r := by
      rw [←b.support_normed_eq (μ := volume)]; exact ht
    have hab : |t-c|<r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hs
    exact hδA t (hab.trans hrδ) y hy (subset_closure hya)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_closed_edge_collar {A : Set TransverseProduct} {e : ℝ}
    (he : ∀ y∈closure A,y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e)
    {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ y∈closure A,
      dist (y 1) ((1/2 : ℝ) : AxisCircle)<δ →2*‖y 0‖<e+ε := by
  let K : Set TransverseProduct := closure A∩{y | e+ε≤2*‖y 0‖}
  have hK : IsCompact K := (isClosed_closure.inter
    (isClosed_le continuous_const (continuous_const.mul (continuous_apply 0).norm))).isCompact
  have ho : IsOpen (Function.eval (1 : Fin 2) '' K)ᶜ :=
    (hK.image (continuous_apply 1)).isClosed.isOpen_compl
  have hh : ((1/2 : ℝ) : AxisCircle)∈(Function.eval (1 : Fin 2) '' K)ᶜ := by
    rintro ⟨y,hy,hy1⟩
    have hh := he y hy.1 hy1
    have hh' := hy.2
    change e+ε≤2*‖y 0‖ at hh'
    linarith
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp ho _ hh
  refine ⟨δ,hδ,fun y hy hyd ↦ ?_⟩
  by_contra h
  exact hball hyd ⟨y,⟨hy,le_of_not_gt h⟩,rfl⟩

lemma planar_seam_probability_bound {A : Set TransverseProduct}
    (hA : MeasurableSet A) {β : AxisCircle →ℝ} (hβ : Continuous β)
    (hβ0 : ∀ t,0≤β t) (hβ1 : (∫ t,β t)=1) {r : ℝ} (hr : 0≤r)
    (hband : ∀ y∈A,β (y 1)≠0 →2*‖y 0‖≤r) :
    (∫ y in A,β (y 1))≤r := by
  let B : Set AxisCircle := Metric.closedBall 0 (r/2)
  have hB : MeasurableSet B := measurableSet_closedBall
  have hi : Integrable (fun y : TransverseProduct ↦ β (y 1)) :=
    (hβ.comp (continuous_apply (1 : Fin 2))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun y : TransverseProduct ↦ B.indicator (fun _ ↦ (1 : ℝ)) (y 0)*β (y 1)) := by
    apply (hi.indicator (hB.preimage (measurable_pi_apply 0))).congr
    filter_upwards [] with y
    by_cases hy : y 0∈B <;> simp [hy]
  have hle : (fun y : TransverseProduct ↦ A.indicator (fun y ↦ β (y 1)) y)≤
      (fun y : TransverseProduct ↦ B.indicator (fun _ ↦ (1 : ℝ)) (y 0)*β (y 1)) := by
    intro y
    dsimp only
    by_cases hy : y∈A
    · rw [indicator_of_mem hy]
      by_cases hz : β (y 1)=0
      · simp [hz]
      have hyB : y 0∈B := by
        change dist (y 0) 0≤r/2
        rw [dist_zero_right]
        linarith [hband y hy hz]
      simp only [indicator_of_mem hyB,one_mul,le_refl]
    · rw [indicator_of_notMem hy]
      exact mul_nonneg (indicator_nonneg (fun _ _ ↦ zero_le_one) _) (hβ0 _)
  have h := integral_mono (hi.indicator hA) hj hle
  rw [integral_indicator hA,transverse_integral_mul,hβ1,mul_one,integral_indicator hB,
    setIntegral_const,smul_eq_mul,mul_one] at h
  apply h.trans
  change (volume B).toReal≤r
  rw [AddCircle.volume_closedBall]
  have he : 2*(r/2)=r := by ring
  rw [he,ENNReal.toReal_ofReal (le_min zero_le_one hr)]
  exact min_le_right _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem planarTorusPerimeter_ge_strip_seam_calibration
    {A : Set TransverseProduct} (hA : IsOpen A)
    {T : Set AxisCircle} (hT : IsCompact T)
    {u v : ℝ →ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (pu : Function.Periodic u 1) (pv : Function.Periodic v 1)
    (hu0 : ∀ t,0≤u t) (huv : ∀ t,(u t)^2+(v t)^2≤1)
    (hin : ∀ y : TransverseProduct,y 0=0 →y 1∈T →y∈A)
    (hout : ∀ y : TransverseProduct,y 0=((1/2 : ℝ) : AxisCircle) →y∉closure A)
    {β : AxisCircle →ℝ} (hβ : Continuous β) (hβ0 : ∀ t,0≤β t)
    (hβ1 : (∫ t,β t)=1) {k r : ℝ} (hk : 0≤k) (hr : 0≤r)
    (hd : ∀ t,deriv v t=2*k*(1-β (t : AxisCircle)))
    (hband : ∀ y∈A,β (y 1)≠0 →2*‖y 0‖≤r) :
    ENNReal.ofReal (2*k*(volume.real A-r)+2*(∫ t in T,pu.lift t))≤planarTorusPerimeter A := by
  have hseam := planar_seam_probability_bound hA.measurableSet hβ hβ0 hβ1 hr hband
  have hβi : Integrable (fun y : TransverseProduct ↦ β (y 1)) :=
    (hβ.comp (continuous_apply (1 : Fin 2))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd' (t : AxisCircle) : (real_periodic_deriv pv).lift t=2*k*(1-β t) := by
    induction t using Quotient.inductionOn with | h t => exact hd t
  have hid : (∫ y in A,(real_periodic_deriv pv).lift (y 1))=
      2*k*(volume.real A-∫ y in A,β (y 1)) := by
    simp_rw [hd']
    rw [integral_const_mul,integral_sub (integrable_const (1 : ℝ)).integrableOn hβi.integrableOn,
      setIntegral_const,smul_eq_mul,mul_one]
  have hcal := planarTorusPerimeter_ge_open_derivative_flux hA hT hu hv pu pv hu0 huv
    (a := 0) (c := 1/2) (by norm_num) (by norm_num) (by simpa only [AddCircle.coe_zero] using hin) hout
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hcal
  rw [hid]
  have h := mul_le_mul_of_nonneg_left (sub_le_sub_left hseam (volume.real A))
    (show 0≤2*k by positivity)
  linarith

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
