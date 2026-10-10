import Mathlib
import OAI.Geometry.CubicTorus.Estimates.SurfaceJet
import OAI.Geometry.CubicTorus.Reflection.CoordinateReflection

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma mem_coordinateHalf_quotient (i : Fin 3) (a : ℝ) (x : Cover) :
    quotientMap x∈coordinateHalf i a ↔ Real.sin (2*Real.pi*(x i-a))<0 := by
  let q : Cover → ℝ := fun y => coordinateSine i (y-a • EuclideanSpace.single i 1)
  have hp : ∀ n y,q (y+latticeVector n)=q y := by
    intro n y
    dsimp [q]
    rw [show y+latticeVector n-a • EuclideanSpace.single i 1=
      (y-a • EuclideanSpace.single i 1)+latticeVector n by abel,coordinateSine_periodic]
  have he := periodic_representative hp x
  simp only [q,coordinateSine,PiLp.sub_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,
    smul_eq_mul,mul_one] at he
  change Real.sin (2*Real.pi*((representative (quotientMap x)) i-a))<0 ↔ _
  rw [he]

lemma coordinateHalf_zero (i : Fin 3) : coordinateHalf i 0=sublevelRegion (coordinateSine i) 0 := by
  ext z
  simp only [coordinateHalf,sublevelRegion,coordinateSine,sub_zero,mem_ofPred_eq]

lemma coordinateHalf_one_half (i : Fin 3) :
    coordinateHalf i (1/2)=sublevelRegion (fun x => -coordinateSine i x) 0 := by
  ext z
  rw [show (1/2 : ℝ)=0+1/2 by ring,coordinateHalf_halfturn]
  simp [sublevelRegion,coordinateSine]

lemma coordinateHalf_translation (i : Fin 3) (a : ℝ) (z : Torus) :
    z+quotientMap (a • EuclideanSpace.single i 1)∈coordinateHalf i a ↔ z∈coordinateHalf i 0 := by
  obtain ⟨x,rfl⟩ := quotientMap_surjective z
  rw [← quotientMap_add,mem_coordinateHalf_quotient,mem_coordinateHalf_quotient]
  simp

lemma volume_translated_half (i : Fin 3) (a : ℝ) {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume ((fun z => z+quotientMap (a • EuclideanSpace.single i 1)) ⁻¹' E∩coordinateHalf i 0)=
      torusVolume (E∩coordinateHalf i a) := by
  have he : (fun z => z+quotientMap (a • EuclideanSpace.single i 1)) ⁻¹' E∩coordinateHalf i 0=
      (fun z => z+quotientMap (a • EuclideanSpace.single i 1)) ⁻¹' (E∩coordinateHalf i a) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,coordinateHalf_translation]
  rw [he,volume_translation (hE.inter (coordinateHalf_measurable i a)).nullMeasurableSet]

theorem isMinimizerAt_exists_bisecting_reflection_measurable {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) (i : Fin 3) :
    ∃ a∈Icc (0 : ℝ) (1/2),let F := (fun z => z+quotientMap (a • EuclideanSpace.single i 1)) ⁻¹' E
      MeasurableSet F ∧ IsMinimizerAt V F ∧
      ∃ μ : FiniteMeasure NormalBundle,IsNormalMeasure F μ ∧
        IsMinimizerAt V (reflectionCompetitor i F (sublevelRegion (coordinateSine i) 0)) ∧
        IsMinimizerAt V (reflectionCompetitor i F (sublevelRegion (fun x => -coordinateSine i x) 0)) ∧
        (μ : Measure NormalBundle) {z | coordinateSine i z.1=0}=0 := by
  obtain ⟨a,ha,hbis⟩ := exists_coordinateHalf_bisects i hE
  let F := (fun z : Torus => z+quotientMap (a • EuclideanSpace.single i 1)) ⁻¹' E
  have hF : MeasurableSet F := (continuous_add_const _).measurable hE
  have hmF : IsMinimizerAt V F := isMinimizerAt_translation hmin _
  have hv : torusVolume.real E=V := by rw [Measure.real_def,hmin.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hvF : torusVolume.real F=V := by rw [Measure.real_def,hmF.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hm : torusVolume.real (F∩coordinateHalf i 0)=V/2 := by
    rw [Measure.real_def,volume_translated_half i a hE,← Measure.real_def,hbis,hv]
  have hp : torusVolume.real (F∩coordinateHalf i (1/2))=V/2 := by
    have hh := coordinateHalf_volume_sum i 0 hF
    norm_num only [zero_add] at hh
    rw [hm,hvF] at hh
    linarith
  have hem : 2*torusVolume (F∩sublevelRegion (coordinateSine i) 0)=ENNReal.ofReal V := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal hV.1.le,
      ← coordinateHalf_zero,← Measure.real_def,hm]
    ring
  have hep : 2*torusVolume (F∩sublevelRegion (fun x => -coordinateSine i x) 0)=ENNReal.ofReal V := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal hV.1.le,
      ← coordinateHalf_one_half,← Measure.real_def,hp]
    ring
  obtain ⟨μ,hμ,hflux⟩ := exists_normalMeasure hF hmF.1.2.ne
  have hnormal : IsNormalMeasure F μ := ⟨hμ,hflux⟩
  exact ⟨a,ha,hF,hmF,μ,hnormal,isMinimizerAt_reflection_competitors hF hmF hnormal i hem hep⟩

theorem isMinimizerAt_exists_bisecting_reflection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (i : Fin 3) :
    ∃ a∈Icc (0 : ℝ) (1/2),∃ F : Set Torus,
      F =ᵐ[torusVolume] ((fun z => z+quotientMap (a • EuclideanSpace.single i 1)) ⁻¹' E) ∧
      MeasurableSet F ∧ IsMinimizerAt V F ∧
      ∃ μ : FiniteMeasure NormalBundle,IsNormalMeasure F μ ∧
        IsMinimizerAt V (reflectionCompetitor i F (sublevelRegion (coordinateSine i) 0)) ∧
        IsMinimizerAt V (reflectionCompetitor i F (sublevelRegion (fun x => -coordinateSine i x) 0)) ∧
        (μ : Measure NormalBundle) {z | coordinateSine i z.1=0}=0 := by
  let E' := toMeasurable torusVolume E
  have hae : E' =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hE' : MeasurableSet E' := measurableSet_toMeasurable _ _
  have hmE' : IsMinimizerAt V E' := (isMinimizerAt_congr_ae hae).mpr hmin
  obtain ⟨a,ha,hF,hmF,hrest⟩ := isMinimizerAt_exists_bisecting_reflection_measurable hV hE' hmE' i
  refine ⟨a,ha,_,?_,hF,hmF,hrest⟩
  exact (measurePreserving_add_right torusVolume _).quasiMeasurePreserving.preimage_ae_eq hae

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateHalf_open (i : Fin 3) : IsOpen (coordinateHalf i 0) := by
  rw [coordinateHalf_zero]
  change IsOpen {z : Torus | coordinateSine i (representative z)<0}
  exact isOpen_lt (continuous_periodic_descent (coordinateSine_contDiff i).continuous
    (coordinateSine_periodic i)) continuous_const

lemma coordinateHalf_eq_slab_image (i : Fin 3) : coordinateHalf i 0=
    quotientMap '' {x : Cover | (1/2 : ℝ)<x i ∧ x i<1} := by
  ext z
  constructor
  · intro hz
    refine ⟨representative z,?_,quotientMap_representative z⟩
    have hr := (representative_mem_fundamentalCube z) i
    change 0≤representative z i ∧ representative z i<1 at hr
    refine ⟨?_,hr.2⟩
    by_contra hn
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (mul_nonneg (by positivity : 0≤2*Real.pi) hr.1)
      (show 2*Real.pi*representative z i≤Real.pi by nlinarith [Real.pi_pos,le_of_not_gt hn])
    change Real.sin (2*Real.pi*(representative z i-0))<0 at hz
    simp only [sub_zero] at hz
    exact not_lt_of_ge hs hz
  · rintro ⟨x,hx,rfl⟩
    rw [mem_coordinateHalf_quotient,sub_zero]
    have hs := Real.sin_neg_of_neg_of_neg_pi_lt
      (show 2*Real.pi*x i-2*Real.pi<0 by nlinarith [Real.pi_pos,hx.2])
      (show -Real.pi<2*Real.pi*x i-2*Real.pi by nlinarith [Real.pi_pos,hx.1])
    simpa only [Real.sin_sub_two_pi] using hs

lemma coordinateHalf_preconnected (i : Fin 3) : IsPreconnected (coordinateHalf i 0) := by
  rw [coordinateHalf_eq_slab_image]
  have hc : Convex ℝ {x : Cover | (1/2 : ℝ)<x i ∧ x i<1} := by
    exact (convex_Ioo (1/2 : ℝ) 1).linear_preimage (EuclideanSpace.proj i).toLinearMap
  exact hc.isPreconnected.image _ continuous_quotientMap.continuousOn

lemma coordinateReflection_preimage_half (i : Fin 3) :
    coordinateReflection i ⁻¹' coordinateHalf i 0=coordinateHalf i (1/2) := by
  ext z
  obtain ⟨x,rfl⟩ := quotientMap_surjective z
  simp only [mem_preimage]
  rw [← quotientMap_coordinateReflection,mem_coordinateHalf_quotient,mem_coordinateHalf_quotient]
  simp only [sub_zero,coverCoordinateReflection_apply,ite_true,mul_neg,Real.sin_neg]
  rw [show 2*Real.pi*(x i-1/2)=2*Real.pi*x i-Real.pi by ring,Real.sin_sub_pi]

lemma coordinateHalf_realVolume (i : Fin 3) : torusVolume.real (coordinateHalf i 0)=1/2 := by
  have hh := coordinateHalf_volume_sum i 0 MeasurableSet.univ
  simp only [univ_inter,zero_add] at hh
  have he : torusVolume (coordinateHalf i (1/2))=torusVolume (coordinateHalf i 0) := by
    rw [← coordinateReflection_preimage_half]
    exact (coordinateReflection_measurePreserving i).measure_preimage (coordinateHalf_measurable i 0).nullMeasurableSet
  have her : torusVolume.real (coordinateHalf i (1/2))=torusVolume.real (coordinateHalf i 0) :=
    congrArg ENNReal.toReal he
  rw [her] at hh
  have hu : torusVolume.real univ=1 := by simp [Measure.real_def]
  rw [hu] at hh
  linarith

lemma reflectionCompetitor_retained (i : Fin 3) (E : Set Torus) {B : Set Torus}
    (hd : Disjoint B (coordinateReflection i ⁻¹' B)) :
    E∩B=reflectionCompetitor i E B∩B := by
  ext z
  constructor
  · exact fun hz => ⟨Or.inl hz,hz.2⟩
  · rintro ⟨hz,hzB⟩
    rcases hz with hh|hh
    · exact hh
    · exact False.elim (disjoint_left.mp hd hzB hh.2)

lemma reflectionCompetitor_invariant (i : Fin 3) (E B : Set Torus) :
    coordinateReflection i ⁻¹' reflectionCompetitor i E B=reflectionCompetitor i E B := by
  ext z
  simp only [reflectionCompetitor,mem_preimage,mem_union,mem_inter_iff,coordinateReflection_involutive]
  tauto

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_continuous_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    (f : BoundedContinuousFunction Cover ℝ) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*f z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*f (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let M : ℝ := ‖f‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let f₀ : Cover → ℝ := fun x => f x / M
  have hfc : Continuous f₀ := f.continuous.div_const M
  have hfb (x : Cover) : |f₀ x| ≤ 1 := by
    rw [show f₀ x = f x / M from rfl, abs_div, abs_of_pos hM]
    apply (div_le_one hM).mpr
    exact (f.norm_coe_le_norm x).trans (by dsimp [M]; linarith)
  have he := cutoff_graph_patch_limit_mass hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb
    (fun i => smoothApprox_contDiff hfc.measurable hfb i)
    (fun i x => smoothApprox_bound hfb i x)
    (fun x _ => ContDiffBump.convolution_tendsto_right_of_continuous
      mollifier_rOut_tendsto hfc x)
  have he' := congrArg (fun t : ℝ => M * t) he
  rw [← integral_const_mul, ← integral_const_mul] at he'
  convert he' using 1 <;> congr 1 <;> funext x <;> dsimp only [f₀] <;> field_simp [ne_of_gt hM]

theorem cutoff_graph_patch_measure {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    Measure.map Prod.fst
      (((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}).withDensity
        (fun z => ENNReal.ofReal (φ z.1))) =
    Measure.map (fun y : Plane => a + normalGraph n g y)
      (volume.withDensity (fun y => ENNReal.ofReal
        (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hI : Integrable (fun z : BlowupNormalBundle => φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hφb _).1]; exact (hφb _).2)
  have hG := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy => (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hGc := graph_weighted_continuous a hn hg.continuous hφ.continuous hφR
    (fun y hy => (graphAreaVector_continuousAt n (hc y hy)).norm)
  let := isFiniteMeasure_withDensity_ofReal hI.hasFiniteIntegral
  let := isFiniteMeasure_withDensity_ofReal hG.hasFiniteIntegral
  have hchart : Continuous (fun y : Plane => a + normalGraph n g y) := by
    simpa only [id_eq] using graph_trace_continuous a n hg.continuous continuous_id
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable measurable_fst f.continuous.stronglyMeasurable,
    integral_map_of_stronglyMeasurable
      hchart.measurable
      f.continuous.stronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
      (f := fun z : BlowupNormalBundle => ENNReal.ofReal (φ z.1))
      (hφ.continuous.comp continuous_fst).measurable.ennreal_ofReal
      (ae_of_all μ fun _ => ENNReal.ofReal_lt_top) _,
    integral_withDensity_eq_integral_toReal_smul hGc.measurable.ennreal_ofReal
      (ae_of_all volume fun _ => ENNReal.ofReal_lt_top) _]
  simp_rw [ENNReal.toReal_ofReal (hφb _).1, smul_eq_mul,
    ENNReal.toReal_ofReal (mul_nonneg (hφb _).1 (norm_nonneg _))]
  convert cutoff_graph_patch_continuous_mass hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb f using 1
  congr 1
  funext y
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphUnitNormalExtension_measurable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) : Measurable (graphUnitNormalExtension a n g) := by
  have hm : Measurable (gradient g) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
  exact (graphSlopeNormal_contDiff hn).continuous.measurable.comp
    (hm.comp ((normalPlaneCoordinates n).continuous.measurable.comp (measurable_id.sub measurable_const)))

def graphNormalSection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) : BlowupNormalBundle :=
  (x, ⟨graphUnitNormalExtension a n g x, graphUnitNormalExtension_unit a hn g x⟩)

lemma graphNormalSection_measurable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) : Measurable (graphNormalSection a hn g) :=
  measurable_id.prodMk (graphUnitNormalExtension_measurable a hn g).subtype_mk

lemma weighted_bundle_section {μ : Measure BlowupNormalBundle} {φ : Cover → ℝ}
    (hφ : Measurable φ) {s : Cover → BlowupNormalBundle} (hs : Measurable s)
    (hae : ∀ᵐ z ∂μ, 0 < φ z.1 → s z.1 = z) :
    μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map s (Measure.map Prod.fst (μ.withDensity (fun z => ENNReal.ofReal (φ z.1)))) := by
  rw [Measure.map_map hs measurable_fst]
  symm
  calc
    _ = Measure.map id (μ.withDensity (fun z => ENNReal.ofReal (φ z.1))) := by
      apply Measure.map_congr
      apply (ae_withDensity_iff (hφ.comp measurable_fst).ennreal_ofReal).mpr
      filter_upwards [hae] with z hz hpos
      exact hz (ENNReal.ofReal_ne_zero_iff.mp hpos)
    _ = _ := Measure.map_id

theorem cutoff_graph_patch_bundle_measure {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}).withDensity
      (fun z => ENNReal.ofReal (φ z.1))) =
    Measure.map (fun y : Plane => graphNormalSection a hn g (a + normalGraph n g y))
      (volume.withDensity (fun y => ENNReal.ofReal
        (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  have ha := cutoff_graph_patch_normal_ae hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb
  have hs := weighted_bundle_section hφ.continuous.measurable
    (graphNormalSection_measurable a hn g) (show ∀ᵐ z ∂(ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O},
      0 < φ z.1 → graphNormalSection a hn g z.1 = z from by
        filter_upwards [ha] with z hz hpos
        refine Prod.ext ?_ ?_
        · rfl
        · exact Subtype.ext (hz hpos).symm)
  rw [hs, cutoff_graph_patch_measure hA a hn hg hc hgraph hsat hflux
    hφ hsφ hφU hφO hφR hφb]
  have hchart : Measurable (fun y : Plane => a + normalGraph n g y) := by
    simpa only [id_eq] using (graph_trace_continuous a n hg.continuous continuous_id).measurable
  exact Measure.map_map (graphNormalSection_measurable a hn g) hchart

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def clampCell (x : Cover) : CompactCell :=
  ⟨WithLp.toLp 2 (fun i => max 0 (min 1 (x i))),
    ⟨fun i => max 0 (min 1 (x i)),
      ⟨fun _ => le_max_left _ _, fun _ => max_le zero_le_one (min_le_left _ _)⟩, rfl⟩⟩

lemma continuous_clampCell : Continuous clampCell := by
  apply Continuous.subtype_mk
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
    (continuous_pi (fun i => continuous_const.max (continuous_const.min (by fun_prop))))

lemma clampCell_coe (x : CompactCell) : clampCell (x : Cover) = x := by
  apply Subtype.ext
  ext i
  change max 0 (min 1 ((x : Cover) i)) = (x : Cover) i
  rw [min_eq_right (compactCell_coordinates x i).2,
    max_eq_right (compactCell_coordinates x i).1]

def normalCellProjection (z : BlowupNormalBundle) : NormalBundle :=
  (clampCell z.1, z.2)

lemma continuous_normalCellProjection : Continuous normalCellProjection :=
  (continuous_clampCell.comp continuous_fst).prodMk continuous_snd

lemma normalCellProjection_cover (z : NormalBundle) :
    normalCellProjection (normalCoverMap z) = z := by
  change (clampCell (z.1 : Cover), z.2) = z
  rw [clampCell_coe]

lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    (Measure.map f μ).withDensity w = Measure.map f (μ.withDensity (w ∘ f)) := by
  apply Measure.ext
  intro s hs
  rw [withDensity_apply _ hs, Measure.map_apply hf hs,
    withDensity_apply _ (hs.preimage hf), setLIntegral_map hs hw hf]
  rfl

lemma withDensity_restrict_of_support {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ≥0∞} {S : Set α} (hS : MeasurableSet S)
    (hs : ∀ x, x ∉ S → w x = 0) :
    (μ.restrict S).withDensity w = μ.withDensity w := by
  rw [← withDensity_indicator hS]
  congr 1
  apply Set.indicator_eq_self.2
  intro x hx
  by_contra hn
  exact hx (hs x hn)

def actualNormalGraphChart (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : NormalBundle :=
  normalCellProjection (graphNormalSection a hn g (a + normalGraph n g y))

lemma actualNormalGraphChart_measurable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) : Measurable (actualNormalGraphChart a hn g) := by
  apply continuous_normalCellProjection.measurable.comp
  apply (graphNormalSection_measurable a hn g).comp
  simpa only [id_eq] using (graph_trace_continuous a n hg continuous_id).measurable

theorem normalMeasure_graph_area_measure {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {R : ℝ}
    (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U →
      (quotientMap x ∈ E ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
    Measure.map (actualNormalGraphChart a hn g)
      (volume.withDensity (fun y => ENNReal.ofReal
        (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))) := by
  let O : Set Cover := {x | ∀ i, 0 < x i ∧ x i < 1}
  have hmO : MeasurableSet {z : BlowupNormalBundle | z.1 ∈ O} := by
    change MeasurableSet {z : BlowupNormalBundle | ∀ i, 0 < z.1 i ∧ z.1 i < 1}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun z : BlowupNormalBundle => z.1 i) := by fun_prop
    exact (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const)
  have hf (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F ⊆ O) (_hb : ∀ x, ‖F x‖ ≤ 1) :=
    normalCoverMeasure_local_flux hE hμ hF hs hO
  have he := cutoff_graph_patch_bundle_measure (hE.preimage measurable_quotientMap)
    a hn hg hc hgraph (normalMeasure_cutoff_saturation hμ O) hf
    hφ hsφ hφU hφO hφR hφb
  rw [withDensity_restrict_of_support hmO (fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h)), ENNReal.ofReal_zero])] at he
  have hcmap : (normalCoverMeasure μ : Measure BlowupNormalBundle) =
      Measure.map normalCoverMap (μ : Measure NormalBundle) := FiniteMeasure.toMeasure_map μ normalCoverMap
  rw [hcmap, map_withDensity_comp _ continuous_normalCoverMap.measurable
    (w := fun z : BlowupNormalBundle => ENNReal.ofReal (φ z.1))
    ((hφ.continuous.comp continuous_fst).measurable.ennreal_ofReal)] at he
  have hp := congrArg (Measure.map normalCellProjection) he
  rw [Measure.map_map continuous_normalCellProjection.measurable continuous_normalCoverMap.measurable] at hp
  have hid : normalCellProjection ∘ normalCoverMap = id := funext normalCellProjection_cover
  rw [hid, Measure.map_id] at hp
  have hchart : Measurable (fun y : Plane => graphNormalSection a hn g (a+normalGraph n g y)) := by
    apply (graphNormalSection_measurable a hn g).comp
    simpa only [id_eq] using (graph_trace_continuous a n hg.continuous continuous_id).measurable
  rw [Measure.map_map continuous_normalCellProjection.measurable hchart] at hp
  exact hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def lpPullbackLE {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ν : Measure α} {μ : Measure β} {f : α → β}
    (hf : Measurable f) (hle : Measure.map f ν ≤ μ) :
    Lp F 2 μ →L[ℝ] Lp F 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℝ f ⟨hf,rfl⟩).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using hle))

lemma lpPullbackLE_ae {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ν : Measure α} {μ : Measure β} {f : α → β}
    (hf : Measurable f) (hle : Measure.map f ν ≤ μ) (u : Lp F 2 μ) :
    lpPullbackLE hf hle u =ᵐ[ν] u ∘ f := by
  have hmp : MeasurePreserving f ν (Measure.map f ν) := ⟨hf,rfl⟩
  have hr := Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1)
    (by simp : (1 : ℝ≥0∞) ≠ ∞) (by simpa using hle) u
  exact (Lp.coeFn_compMeasurePreserving _ hmp).trans (hmp.quasiMeasurePreserving.ae_eq_comp hr)

lemma lpPullbackLE_congr_ae {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ν : Measure α} {μ : Measure β} {f : α → β}
    (hf : Measurable f) (hle : Measure.map f ν ≤ μ) {u v : β → F}
    (huv : u =ᵐ[μ] v) : u ∘ f =ᵐ[ν] v ∘ f := by
  exact (show Measure.QuasiMeasurePreserving f ν μ from
    ⟨hf,Measure.absolutelyContinuous_of_le hle⟩).ae_eq_comp huv

lemma graphAreaVector_norm_ge_one {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : 1 ≤ ‖graphAreaVector n g y‖ := by
  have hs := graphAreaVector_norm_sq hn g y
  nlinarith [norm_nonneg (graphAreaVector n g y), sq_nonneg ‖gradient g y‖]

lemma graph_chart_measure_le {μ : Measure NormalBundle}
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ}
    (hg : Continuous g) {φ : Cover → ℝ} (hφ : ∀ x, φ x ∈ Icc 0 1)
    (hm : μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {S : Set Plane} (hS : MeasurableSet S)
    (hunit : ∀ y ∈ S, φ (a+normalGraph n g y)=1) :
    Measure.map (actualNormalGraphChart a hn g) (volume.restrict S) ≤ μ := by
  have hd : volume.restrict S ≤ volume.withDensity (fun y => ENNReal.ofReal
      (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
    rw [← withDensity_indicator_one hS]
    apply withDensity_mono
    filter_upwards [] with y
    by_cases hy : y∈S
    · simp only [Set.indicator_of_mem hy, Pi.one_apply, hunit y hy, one_mul]
      simpa using ENNReal.ofReal_le_ofReal (graphAreaVector_norm_ge_one hn g y)
    · simp [hy]
  have hcut : μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) ≤ μ := by
    conv_rhs => rw [← withDensity_one (μ := μ)]
    apply withDensity_mono
    exact ae_of_all _ (fun z => by simpa using ENNReal.ofReal_le_ofReal (hφ z.1).2)
  exact ((Measure.map_mono hd (actualNormalGraphChart_measurable a hn hg)).trans_eq hm.symm).trans hcut

def graphCovector (n : Cover) (g : Plane → ℝ) (y : Plane) : Cover →L[ℝ] Plane :=
  normalPlaneCoordinates n + (innerSL ℝ n).smulRight (gradient g y)

lemma graphCovector_apply (n : Cover) (g : Plane → ℝ) (y : Plane) (v : Cover) :
    graphCovector n g y v = normalPlaneCoordinates n v + ⟪n,v⟫ • gradient g y := rfl

lemma measurable_graphCovector (n : Cover) (g : Plane → ℝ) :
    Measurable (graphCovector n g) := by
  have hm : Measurable (gradient g) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
  exact measurable_const.add ((ContinuousLinearMap.smulRightL ℝ Cover Plane (innerSL ℝ n)).continuous.measurable.comp hm)

lemma graphCovector_norm_le {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ}
    {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    ‖graphCovector n g y‖ ≤ 1+K := by
  calc
    _ ≤ ‖normalPlaneCoordinates n‖+‖(innerSL ℝ n).smulRight (gradient g y)‖ := norm_add_le _ _
    _ ≤ 1+‖innerSL ℝ n‖*‖gradient g y‖ := add_le_add (norm_normalPlaneCoordinates_le n) (ContinuousLinearMap.norm_smulRight_apply _ _).le
    _ ≤ 1+K := by
      rw [innerSL_apply_norm,hn,one_mul]
      apply add_le_add le_rfl
      simpa only [gradient, LinearIsometryEquiv.norm_map] using norm_fderiv_le_of_lipschitz ℝ hg (x₀ := y)

lemma graphCovector_memLp {ν : Measure Plane} {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    MemLp (graphCovector n g) ∞ ν :=
  memLp_top_of_bound (measurable_graphCovector n g).aestronglyMeasurable (1+K)
    (ae_of_all _ (graphCovector_norm_le hn hg))

def graphCovectorLp {ν : Measure Plane} {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    Lp Cover 2 ν →L[ℝ] Lp Plane 2 ν :=
  (ContinuousLinearMap.id ℝ (Cover →L[ℝ] Plane)).holderL ν ∞ 2 2
    ((graphCovector_memLp (ν := ν) hn hg).toLp (graphCovector n g))

lemma graphCovectorLp_ae {ν : Measure Plane} {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (u : Lp Cover 2 ν) :
    graphCovectorLp hn hg u =ᵐ[ν] fun y => graphCovector n g y (u y) := by
  have ha := (graphCovector_memLp (ν := ν) hn hg).coeFn_toLp
  have hb := (ContinuousLinearMap.id ℝ (Cover →L[ℝ] Plane)).coeFn_holder
    ((graphCovector_memLp (ν := ν) hn hg).toLp (graphCovector n g)) u (r := 2)
  filter_upwards [ha,hb] with y ha hb
  change (graphCovectorLp hn hg u) y = _ at hb
  simpa only [ContinuousLinearMap.id_apply,ha] using hb

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphCovector_duality {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ)
    (y v : Plane) (w : Cover) :
    ⟪graphCovector n g y w,v⟫ =
      ⟪w,normalPlaneEmbedding n v+⟪gradient g y,v⟫ • n⟫ := by
  rw [graphCovector_apply,inner_add_left,real_inner_smul_left,
    inner_add_right,inner_smul_right]
  have he : ⟪normalPlaneCoordinates n w,v⟫=⟪w,normalPlaneEmbedding n v⟫ := by
    calc
      _ = ⟪v,normalPlaneCoordinates n w⟫ := real_inner_comm _ _
      _ = ⟪normalPlaneEmbedding n v,w⟫ := (normalPlaneEmbedding_inner_coordinates hn v w).symm
      _ = _ := real_inner_comm _ _
  rw [he]
  have hi : ⟪n,w⟫=⟪w,n⟫ := real_inner_comm _ _
  rw [hi]
  ring

lemma graphCovector_normal_zero {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (y : Plane) :
    graphCovector n g y (graphSlopeNormal n (gradient g y))=0 := by
  rw [graphSlopeNormal_weight hn,map_smul,map_sub,graphCovector_apply,
    graphCovector_apply,normalPlaneCoordinates_normal hn,
    normalPlaneCoordinates_embedding,real_inner_self_eq_norm_sq,hn,one_pow,
    normalPlaneEmbedding_inner hn,one_smul,zero_smul,zero_add,add_zero,sub_self,smul_zero]

lemma gradient_graph_trace (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {y : Plane} (hg : DifferentiableAt ℝ g y)
    {f : Cover → ℝ} (hf : DifferentiableAt ℝ f (a+normalGraph n g y)) :
    gradient (fun z => f (a+normalGraph n g z)) y =
      graphCovector n g y (gradient f (a+normalGraph n g y)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,graphCovector_duality hn]
  have hc := hf.hasFDerivAt.comp y ((normalGraph_hasFDerivAt hg).const_add a)
  change (fderiv ℝ (f ∘ fun x => a+normalGraph n g x) y) v = _
  rw [hc.fderiv,ContinuousLinearMap.comp_apply,← inner_gradient_left]
  congr 1
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    inner_gradient_left]
  rfl

lemma actualNormalGraphChart_position (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) {y : Plane}
    (hy : ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1) :
    ((actualNormalGraphChart a hn g y).1 : Cover)=a+normalGraph n g y := by
  change ((clampCell (a+normalGraph n g y)) : Cover)=_
  ext i
  change max 0 (min 1 ((a+normalGraph n g y) i))=(a+normalGraph n g y) i
  rw [min_eq_right (hy i).2,max_eq_right (hy i).1]

lemma actualNormalGraphChart_normal (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (y : Plane) :
    ((actualNormalGraphChart a hn g y).2 : Cover)=graphSlopeNormal n (gradient g y) :=
  graphUnitNormalExtension_graph a hn g g y

lemma smoothScalarGradient_graph_covector (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (f : smoothPeriodicScalars) {g : Plane → ℝ} {y : Plane}
    (hgy : DifferentiableAt ℝ g y)
    (hy : ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1) :
    graphCovector n g y (smoothScalarGradient f (actualNormalGraphChart a hn g y))=
      gradient (fun z => f.val (a+normalGraph n g z)) y := by
  change graphCovector n g y (gradient f.val (actualNormalGraphChart a hn g y).1-
    ⟪((actualNormalGraphChart a hn g y).2 : Cover),gradient f.val (actualNormalGraphChart a hn g y).1⟫ •
      ((actualNormalGraphChart a hn g y).2 : Cover))=_
  rw [actualNormalGraphChart_position a hn g hy,actualNormalGraphChart_normal,
    map_sub,map_smul,graphCovector_normal_zero hn,smul_zero,sub_zero]
  exact (gradient_graph_trace a hn hgy (f.property.1.differentiable (by simp) _)).symm

def PlaneWeakGradientOn (S : Set Plane) (u : Plane → ℝ) (G : Plane → Plane) : Prop :=
  ∀ (v : Plane) (ψ : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ⊆S → (∫ y in S, ⟪G y,v⟫*ψ y)= -(∫ y in S,u y*fderiv ℝ ψ y v)

lemma PlaneWeakGradientOn.congr {S : Set Plane} {u u' : Plane → ℝ}
    {G G' : Plane → Plane} (h : PlaneWeakGradientOn S u G)
    (hu : u'=ᵐ[volume.restrict S] u) (hG : G'=ᵐ[volume.restrict S] G) :
    PlaneWeakGradientOn S u' G' := by
  intro v ψ hψ hc hs
  have hleft : (∫ y in S, ⟪G' y,v⟫*ψ y)=(∫ y in S, ⟪G y,v⟫*ψ y) :=
    integral_congr_ae (hG.mono (fun _ he => by dsimp only; rw [he]))
  have hright : (∫ y in S, u' y*fderiv ℝ ψ y v)=(∫ y in S, u y*fderiv ℝ ψ y v) :=
    integral_congr_ae (hu.mono (fun _ he => by dsimp only; rw [he]))
  rw [hleft,hright]
  exact h v ψ hψ hc hs

lemma C1_weak_gradient_on {S : Set Plane} (hS : IsOpen S)
    {f : Plane → ℝ} (hf : Continuous f) (hfc : ContDiffOn ℝ 1 f S) :
    PlaneWeakGradientOn S f (gradient f) := by
  intro v ψ hψ hc hs
  have hi₁ : (∫ y in S, ⟪gradient f y,v⟫*ψ y)=(∫ y, ⟪gradient f y,v⟫*ψ y) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)),mul_zero]
  have hi₂ : (∫ y in S, f y*fderiv ℝ ψ y v)=(∫ y, f y*fderiv ℝ ψ y v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport
      (fun h => hy (hs ((tsupport_fderiv_apply_subset (f := ψ) ℝ v) h))),mul_zero]
  rw [hi₁,hi₂]
  simpa only [inner_gradient_left] using C1_local_integration_by_parts hS hf hfc
    (hψ.of_le (by simp)) hc hs v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_pair_scalar_measure {ν : Measure Plane} {u : Lp ℝ 2 ν} {φ : Plane → ℝ}
    (hφ : MemLp φ 2 ν) : ⟪u,hφ.toLp φ⟫=(∫ y,u y*φ y ∂ν) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with y hy
  simp only [hy,RCLike.inner_apply,conj_trivial]
  ring

lemma L2_pair_vector_measure {ν : Measure Plane} {G : Lp Plane 2 ν}
    {f : Plane → Plane} (hf : MemLp f 2 ν) :
    ⟪G,hf.toLp f⟫=(∫ y,⟪G y,f y⟫ ∂ν) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy]

lemma PlaneWeakGradientOn.L2_limit {S : Set Plane}
    {u : ℕ → Lp ℝ 2 (volume.restrict S)}
    {G : ℕ → Lp Plane 2 (volume.restrict S)}
    {u₀ : Lp ℝ 2 (volume.restrict S)} {G₀ : Lp Plane 2 (volume.restrict S)}
    (hu : Tendsto u atTop (𝓝 u₀)) (hG : Tendsto G atTop (𝓝 G₀))
    (hweak : ∀ i,PlaneWeakGradientOn S (u i) (G i)) :
    PlaneWeakGradientOn S u₀ G₀ := by
  intro v ψ hψ hc hs
  let a : Plane → Plane := fun y => ψ y • v
  have ha : MemLp a 2 (volume.restrict S) :=
    ((hψ.continuous.smul continuous_const).memLp_of_hasCompactSupport
      hc.smul_right (p := 2) (μ := volume)).mono_measure Measure.restrict_le_self
  let A := ha.toLp a
  let b : Plane → ℝ := fun y => fderiv ℝ ψ y v
  have hb : MemLp b 2 (volume.restrict S) :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v) (p := 2) (μ := volume)).mono_measure Measure.restrict_le_self
  let B := hb.toLp b
  have hi (W : Lp Plane 2 (volume.restrict S)) :
      ⟪W,A⟫=(∫ y in S,⟪W y,v⟫*ψ y) := by
    rw [L2_pair_vector_measure ha]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [a,inner_smul_right]
    ring
  have he (i : ℕ) : ⟪G i,A⟫= -⟪u i,B⟫ := by
    rw [hi,L2_pair_scalar_measure hb]
    exact hweak i v ψ hψ hc hs
  have hleft := hG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := A))
  have hright := (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := B))).neg
  have hh := tendsto_nhds_unique (hleft.congr' (Eventually.of_forall he)) hright
  rw [hi,L2_pair_scalar_measure hb] at hh
  exact hh

lemma graph_trace_contDiffOn_C1 (a n : Cover) {g : Plane → ℝ} {S : Set Plane}
    (hg : ContDiffOn ℝ 1 g S) {f : Cover → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiffOn ℝ 1 (fun y => f (a+normalGraph n g y)) S := by
  have hgraph : ContDiffOn ℝ 1 (fun y => a+normalGraph n g y) S :=
    contDiffOn_const.add ((normalPlaneLinearIsometry n).contDiff.contDiffOn.add
      (hg.smul contDiffOn_const))
  exact hf.comp_contDiffOn hgraph

lemma surfaceSmoothJet_chart_weak_gradient (μ : FiniteMeasure NormalBundle)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {S : Set Plane} (hS : IsOpen S)
    (hgc : ContDiffOn ℝ 1 g S)
    (hcell : ∀ y ∈ S, ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1)
    (hdom : Measure.map (actualNormalGraphChart a hn g) (volume.restrict S) ≤
      (μ : Measure NormalBundle)) (f : smoothPeriodicScalars) :
    PlaneWeakGradientOn S
      (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom
        (surfaceSmoothJet μ f).1)
      (graphCovectorLp hn hg
        (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom
          (surfaceSmoothJet μ f).2)) := by
  let chart := actualNormalGraphChart a hn g
  have hchart : Measurable chart := actualNormalGraphChart_measurable a hn hg.continuous
  have hv := (lpPullbackLE_ae hchart hdom (surfaceSmoothJet μ f).1).trans
    (lpPullbackLE_congr_ae hchart hdom
      ((smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)))
  have hw := (lpPullbackLE_ae hchart hdom (surfaceSmoothJet μ f).2).trans
    (lpPullbackLE_congr_ae hchart hdom
      ((smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)))
  have hv' : lpPullbackLE hchart hdom (surfaceSmoothJet μ f).1 =ᵐ[volume.restrict S]
      (fun y => f.val (a+normalGraph n g y)) := by
    filter_upwards [hv,ae_restrict_mem hS.measurableSet] with y hy hSy
    change (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).1) y = f.val (chart y).1 at hy
    rw [hy]
    change f.val (actualNormalGraphChart a hn g y).1 = _
    rw [actualNormalGraphChart_position a hn g (hcell y hSy)]
  have hw' : graphCovectorLp hn hg (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).2)
      =ᵐ[volume.restrict S] gradient (fun y => f.val (a+normalGraph n g y)) := by
    filter_upwards [graphCovectorLp_ae hn hg
      (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).2),hw,
      ae_restrict_mem hS.measurableSet] with y hmap hy hSy
    change (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).2) y = smoothScalarGradient f (chart y) at hy
    rw [hmap,hy]
    exact smoothScalarGradient_graph_covector a hn f
      (((hgc y hSy).contDiffAt (hS.mem_nhds hSy)).differentiableAt (by simp)) (hcell y hSy)
  exact (C1_weak_gradient_on hS
    (graph_trace_continuous a n hg.continuous f.property.1.continuous)
    (graph_trace_contDiffOn_C1 a n hgc (f.property.1.of_le (by simp)))).congr hv' hw'

theorem surfaceH1_chart_weak_gradient (μ : FiniteMeasure NormalBundle)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {S : Set Plane} (hS : IsOpen S)
    (hgc : ContDiffOn ℝ 1 g S)
    (hcell : ∀ y ∈ S, ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1)
    (hdom : Measure.map (actualNormalGraphChart a hn g) (volume.restrict S) ≤
      (μ : Measure NormalBundle)) {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    PlaneWeakGradientOn S
      (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom u.1)
      (graphCovectorLp hn hg
        (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom u.2)) := by
  obtain ⟨w,hw,hl⟩ := mem_closure_iff_seq_limit.mp hu
  let hchart := actualNormalGraphChart_measurable a hn hg.continuous
  apply PlaneWeakGradientOn.L2_limit
    (((lpPullbackLE hchart hdom).continuous.tendsto _).comp ((continuous_fst.tendsto u).comp hl))
    (((graphCovectorLp hn hg).continuous.tendsto _).comp
      (((lpPullbackLE hchart hdom).continuous.tendsto _).comp ((continuous_snd.tendsto u).comp hl)))
  intro i
  obtain ⟨f,hf⟩ := hw i
  simp only [Function.comp_apply]
  rw [← hf]
  exact surfaceSmoothJet_chart_weak_gradient μ a hn hg hS hgc hcell hdom f

end CubicTorus

end
end

end OAI
