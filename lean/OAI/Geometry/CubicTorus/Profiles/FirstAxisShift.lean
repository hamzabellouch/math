import Mathlib
import OAI.Geometry.CubicTorus.Profiles.FirstSeamFunction

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def firstAxisShift (t : ℝ) : Cover := t • EuclideanSpace.single 0 1

def firstHalfMass (E : Set Torus) (t : ℝ) : ℝ :=
  ∫ z in E,characteristic (sublevelRegion firstSeamFunction 0)
    (z+quotientMap (firstAxisShift t)) ∂torusVolume

lemma integrable_shifted_characteristic {A : Set Torus} (hA : MeasurableSet A) (a : Torus) :
    Integrable (fun z ↦ characteristic A (z+a)) torusVolume :=
  Integrable.of_bound ((measurable_characteristic hA).comp (measurable_id.add_const a)).aestronglyMeasurable
    1 (Eventually.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using characteristic_bound A (z+a))

lemma firstHalfMass_lipschitz {E : Set Torus} (hE : MeasurableSet E) (hP : perimeter E≠⊤) :
    LipschitzWith ⟨(perimeter E).toReal,ENNReal.toReal_nonneg⟩ (firstHalfMass E) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  rw [Real.dist_eq,Real.dist_eq]
  have hB := measurableSet_sublevelRegion firstSeamFunction_contDiff.continuous.measurable 0
  let g : Torus → ℝ := fun z ↦ characteristic (sublevelRegion firstSeamFunction 0)
    (z+quotientMap (firstAxisShift s))
  have hg : Measurable g := (measurable_characteristic hB).comp (measurable_id.add_const _)
  have hb : ∀ z,|g z|≤1 := fun z ↦ characteristic_bound _ _
  have hh := torus_test_translation_bound hE hP hg hb (firstAxisShift t-firstAxisShift s)
  have he (z : Torus) : g (z+quotientMap (firstAxisShift t-firstAxisShift s))=
      characteristic (sublevelRegion firstSeamFunction 0) (z+quotientMap (firstAxisShift t)) := by
    dsimp [g]
    rw [quotientMap_sub]
    congr 1
    abel
  simp_rw [he] at hh
  rw [integral_sub (integrable_shifted_characteristic hB _).integrableOn
    (integrable_shifted_characteristic hB _).integrableOn] at hh
  have he2 : ‖firstAxisShift t-firstAxisShift s‖=|t-s| := by
    rw [firstAxisShift,firstAxisShift,← sub_smul,norm_smul,Real.norm_eq_abs]
    simp
  rw [he2] at hh
  change |firstHalfMass E t-firstHalfMass E s|≤(perimeter E).toReal*|t-s|
  change |firstHalfMass E t-firstHalfMass E s|≤|t-s| * (perimeter E).toReal at hh
  simpa only [mul_comm] using hh

lemma firstSeam_shift_half (z : Torus) :
    firstSeamFunction (representative (z+quotientMap (firstAxisShift (1/2))))=
      -firstSeamFunction (representative z) := by
  rw [← quotientMap_representative z,← quotientMap_add,
    periodic_representative firstSeamFunction_periodic,
    periodic_representative firstSeamFunction_periodic]
  unfold firstSeamFunction firstAxisShift
  simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
  convert Real.sin_add_pi (2*Real.pi*representative z 0) using 1
  congr 1
  ring

lemma firstHalfMass_pair (E : Set Torus) :
    firstHalfMass E 0+firstHalfMass E (1/2)=(torusVolume E).toReal := by
  have hB := measurableSet_sublevelRegion firstSeamFunction_contDiff.continuous.measurable 0
  have hi0 := (integrable_shifted_characteristic hB (quotientMap (firstAxisShift 0))).integrableOn (s := E)
  have hi1 := (integrable_shifted_characteristic hB (quotientMap (firstAxisShift (1/2)))).integrableOn (s := E)
  rw [firstHalfMass,firstHalfMass,← integral_add hi0 hi1]
  have he : ∀ᵐ z ∂torusVolume,
      characteristic (sublevelRegion firstSeamFunction 0) (z+quotientMap (firstAxisShift 0))+
      characteristic (sublevelRegion firstSeamFunction 0) (z+quotientMap (firstAxisShift (1/2)))=1 := by
    have hn : ∀ᵐ z ∂torusVolume,firstSeamFunction (representative z)≠0 := by
      simpa only [ae_iff,not_not] using firstSeam_null
    filter_upwards [hn] with z hz
    have hz0 : quotientMap (firstAxisShift 0)=0 := by ext i; simp [firstAxisShift,quotientMap]
    rw [hz0,add_zero]
    have he := firstSeam_shift_half z
    classical
    rcases lt_or_gt_of_ne hz with hneg | hpos
    · have hm : z∈sublevelRegion firstSeamFunction 0 := hneg
      have hnm : z+quotientMap (firstAxisShift (1/2))∉sublevelRegion firstSeamFunction 0 := by
        change ¬firstSeamFunction (representative (z+quotientMap (firstAxisShift (1/2))))<0
        rw [he]; linarith
      simp only [characteristic,indicator_of_mem hm,indicator_of_notMem hnm,add_zero]
    · have hnm : z∉sublevelRegion firstSeamFunction 0 := not_lt.mpr hpos.le
      have hm : z+quotientMap (firstAxisShift (1/2))∈sublevelRegion firstSeamFunction 0 := by
        change firstSeamFunction (representative (z+quotientMap (firstAxisShift (1/2))))<0
        rw [he]; linarith
      simp only [characteristic,indicator_of_mem hm,indicator_of_notMem hnm,zero_add]
  rw [integral_congr_ae (ae_restrict_of_ae he),setIntegral_const]
  simp [Measure.real_def]

lemma firstHalfMass_eq_volume {E : Set Torus} (hE : MeasurableSet E) (t : ℝ) :
    firstHalfMass E t=(torusVolume
      (((fun z ↦ z-quotientMap (firstAxisShift t)) ⁻¹' E)∩sublevelRegion firstSeamFunction 0)).toReal := by
  let a := quotientMap (firstAxisShift t)
  let E' := (fun z : Torus ↦ z-a) ⁻¹' E
  have hE' : MeasurableSet E' := hE.preimage (measurable_id.sub_const a)
  have hB := measurableSet_sublevelRegion firstSeamFunction_contDiff.continuous.measurable 0
  have he : E=(fun z : Torus ↦ z+a) ⁻¹' E' := by ext z; simp [E']
  unfold firstHalfMass
  change (∫ z in E,characteristic (sublevelRegion firstSeamFunction 0) (z+a) ∂torusVolume)=_
  conv_lhs => rw [he]
  rw [(measurePreserving_add_right torusVolume a).setIntegral_preimage_emb
    (Homeomorph.addRight a).measurableEmbedding]
  change (∫ z in E',characteristic (sublevelRegion firstSeamFunction 0) z ∂torusVolume)=_
  change (∫ z in E',(sublevelRegion firstSeamFunction 0).indicator (fun _ ↦ (1:ℝ)) z ∂torusVolume)=_
  rw [integral_indicator hB,Measure.restrict_restrict hB,setIntegral_const]
  simp only [smul_eq_mul,mul_one,Measure.real_def]
  rw [inter_comm]

theorem exists_first_half_bisection {E : Set Torus} (hE : MeasurableSet E)
    (hP : perimeter E≠⊤) :
    ∃ a : Torus,(torusVolume (((fun z ↦ z+a) ⁻¹' E)∩sublevelRegion firstSeamFunction 0)).toReal=
      (torusVolume E).toReal/2 := by
  have hc := (firstHalfMass_lipschitz hE hP).continuous
  have hv := firstHalfMass_pair E
  have hr : (torusVolume E).toReal/2∈Set.range (firstHalfMass E) := by
    by_cases h : firstHalfMass E 0≤(torusVolume E).toReal/2
    · exact intermediate_value_univ 0 (1/2) hc ⟨h,by linarith⟩
    · exact intermediate_value_univ (1/2) 0 hc ⟨by linarith,by linarith⟩
  obtain ⟨t,ht⟩ := hr
  refine ⟨-quotientMap (firstAxisShift t),?_⟩
  simpa only [firstHalfMass_eq_volume hE,sub_eq_add_neg] using ht

theorem exists_bisected_reflection_minimizers {V : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ a : Torus,let E' := (fun z ↦ z+a) ⁻¹' E
      IsMinimizerAt V (reflectionClosure (E'∩sublevelRegion firstSeamFunction 0)) ∧
      IsMinimizerAt V (reflectionClosure (E'\sublevelRegion firstSeamFunction 0)) := by
  obtain ⟨a,ha⟩ := exists_first_half_bisection hE hmin.1.2.ne
  refine ⟨a,bisected_reflection_minimizers (hE.preimage (measurable_id.add_const a))
    (isMinimizerAt_translation hmin a) ?_⟩
  rw [volume_translation hE.nullMeasurableSet]
  exact ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma firstSeam_sign {t : ℝ} (ht : t∈Ico (0:ℝ) 1) :
    Real.sin (2*Real.pi*t)<0 ↔ (1/2:ℝ)<t := by
  rcases ht with ⟨ht0,ht1⟩
  constructor
  · intro hs
    by_contra hn
    have h := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity : 0≤2*Real.pi*t)
      (by nlinarith [Real.pi_pos] : 2*Real.pi*t≤Real.pi)
    linarith
  · intro ht'
    have h : 0<Real.sin (2*Real.pi*t-Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    have he : Real.sin (2*Real.pi*t)= -Real.sin (2*Real.pi*t-Real.pi) := by
      convert Real.sin_add_pi (2*Real.pi*t-Real.pi) using 1
      congr 1
      ring
    rw [he]
    linarith

lemma first_half_image : sublevelRegion firstSeamFunction 0=
    quotientMap '' {x : Cover | x 0∈Ioo (1/2:ℝ) 1} := by
  ext z
  constructor
  · intro hz
    have ht := representative_mem_fundamentalCube z 0
    refine ⟨representative z,?_,quotientMap_representative z⟩
    exact ⟨(firstSeam_sign ht).mp hz,ht.2⟩
  · rintro ⟨x,hx,rfl⟩
    rw [mem_sublevelRegion_quotient firstSeamFunction_periodic]
    exact (firstSeam_sign ⟨by linarith [hx.1],hx.2⟩).mpr hx.1

lemma isOpen_first_half : IsOpen (sublevelRegion firstSeamFunction 0) :=
  isOpen_lt (continuous_periodic_descent firstSeamFunction_contDiff.continuous
    firstSeamFunction_periodic) continuous_const

lemma isPreconnected_first_half : IsPreconnected (sublevelRegion firstSeamFunction 0) := by
  rw [first_half_image]
  apply IsPreconnected.image
  · exact ((convex_Ioo (1/2:ℝ) 1).linear_preimage
      (EuclideanSpace.proj (0 : Fin 3) : Cover →L[ℝ] ℝ).toLinearMap).isPreconnected
  · exact continuous_quotientMap.continuousOn

lemma first_half_volume : (torusVolume (sublevelRegion firstSeamFunction 0)).toReal=1/2 := by
  have h0 := firstHalfMass_eq_volume MeasurableSet.univ (0:ℝ)
  have h1 := firstHalfMass_eq_volume MeasurableSet.univ (1/2:ℝ)
  simp only [preimage_univ,univ_inter] at h0 h1
  have hh := firstHalfMass_pair (univ : Set Torus)
  rw [h0,h1,torusVolume_univ,ENNReal.toReal_one] at hh
  linarith

lemma reflected_half_agrees (E : Set Torus) (z : Torus)
    (hz : z∈sublevelRegion firstSeamFunction 0) :
    z∈E ↔ z∈reflectionClosure (E∩sublevelRegion firstSeamFunction 0) := by
  constructor
  · intro he; exact Or.inl ⟨he,hz⟩
  · rintro (he|he)
    · exact he.1
    · have hs : firstSeamFunction (representative z)<0 := hz
      have ht : firstSeamFunction (representative (torusFirstReflection z))<0 := he.2
      rw [firstSeam_representative_reflection] at ht
      linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma reflectionClosure_invariant (A : Set Torus) :
    torusFirstReflection ⁻¹' reflectionClosure A=reflectionClosure A := by
  ext z
  simp only [reflectionClosure,mem_preimage,mem_union,torusFirstReflection_involutive]
  tauto

theorem isMinimizerAt_eq_bisected_reflection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hcE : IsPreconnected (frontier (openRepresentative E)))
    (hhalf : (torusVolume (E∩sublevelRegion firstSeamFunction 0)).toReal=
      (torusVolume E).toReal/2) :
    E=ᵐ[torusVolume]reflectionClosure (E∩sublevelRegion firstSeamFunction 0) := by
  let O := sublevelRegion firstSeamFunction 0
  have hO : MeasurableSet O := isOpen_first_half.measurableSet
  have hv : (torusVolume E).toReal=V := by rw [hmE.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hp : 0<torusVolume (O∩E) := by
    apply (ENNReal.toReal_pos_iff.mp ?_).1
    rw [inter_comm]
    change 0<(torusVolume (E∩sublevelRegion firstSeamFunction 0)).toReal
    rw [hhalf,hv]
    exact half_pos hV.1
  have hn : 0<torusVolume (O∩Eᶜ) := by
    have hs : (torusVolume (O∩E)).toReal+(torusVolume (O∩Eᶜ)).toReal=
        (torusVolume O).toReal := by
      rw [←ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      congr 1
      simpa only [sdiff_eq] using measure_inter_add_sdiff O hE
    have hh : (torusVolume (O∩E)).toReal=V/2 := by
      rw [inter_comm]
      exact hhalf.trans (by rw [hv])
    have ho : (torusVolume O).toReal=1/2 := first_half_volume
    have hr : 0<(torusVolume (O∩Eᶜ)).toReal := by rw [hh,ho] at hs; linarith [hV.2]
    exact (ENNReal.toReal_pos_iff.mp hr).1
  apply isMinimizerAt_local_region_rigidity hV hV hE
    (measurableSet_reflectionClosure (hE.inter hO)) hmE
    (bisected_reflection_minimizers hE hmE hhalf).1 hcE isOpen_first_half
    isPreconnected_first_half hp hn
  exact Eventually.of_forall (fun z hz ↦ reflected_half_agrees E z hz)

theorem isMinimizerAt_bisected_reflection_invariant {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    (hcE : IsPreconnected (frontier (openRepresentative E)))
    (hhalf : (torusVolume (E∩sublevelRegion firstSeamFunction 0)).toReal=
      (torusVolume E).toReal/2) : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E) := by
  have he := isMinimizerAt_eq_bisected_reflection hV hE hmE hcE hhalf
  have hh := torusFirstReflection_measurePreserving.quasiMeasurePreserving.preimage_ae_eq he
  rw [reflectionClosure_invariant] at hh
  exact he.trans hh.symm

theorem isMinimizerAt_exists_first_reflection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmE : IsMinimizerAt V E)
    (hcE : IsPreconnected (frontier (openRepresentative E))) :
    ∃ a : Torus,let E' := (fun z : Torus ↦ z+a) ⁻¹' E
      E'=ᵐ[torusVolume](torusFirstReflection ⁻¹' E') := by
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hae : F=ᵐ[torusVolume]E := hmE.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hae).mpr hmE
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    rwa [openRepresentative_congr_ae hae]
  obtain ⟨a,ha⟩ := exists_first_half_bisection hF hmF.1.2.ne
  have hcFt : IsPreconnected (frontier (openRepresentative ((fun z : Torus ↦ z+a) ⁻¹' F))) := by
    rw [frontier_openRepresentative_translation hF]
    exact (Homeomorph.addRight a).isPreconnected_preimage.mpr hcF
  have ht := isMinimizerAt_bisected_reflection_invariant hV (hF.preimage (measurable_id.add_const a))
    (isMinimizerAt_translation hmF a) hcFt (by simp only [id_eq]; rw [volume_translation hF.nullMeasurableSet]; exact ha)
  have htAE := (measurePreserving_add_right torusVolume a).quasiMeasurePreserving.preimage_ae_eq hae
  refine ⟨a,htAE.symm.trans (ht.trans ?_)⟩
  exact torusFirstReflection_measurePreserving.quasiMeasurePreserving.preimage_ae_eq htAE

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma reflectionPullback_normal_ae {μ : FiniteMeasure NormalBundle}
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∀ᵐ z ∂((μ.map sibling_reflectNormal) : Measure NormalBundle),
      reflectionPullback N z.1=(z.2 : Cover) := by
  rw [FiniteMeasure.toMeasure_map]
  have hc : Continuous (fun z : NormalBundle ↦ reflectionPullback N z.1) :=
    (reflectionPullback_contDiff hN).continuous.comp normalEmbedding_continuous.fst
  apply (ae_map_iff sibling_measurable_reflectNormal.aemeasurable
    (isClosed_eq hc continuous_normalUnit).measurableSet).mpr
  filter_upwards [hae] with z hz
  change reflectionPullback N (sibling_reflectNormal z).1=firstReflection (z.2 : Cover)
  rw [sibling_reflectNormal_periodic_eval (reflectionPullback_periodic hp)]
  change firstReflection (N (firstReflection (firstReflection z.1)))=_
  rw [firstReflection_involutive,hz]

theorem isMinimizerAt_reflection_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    N (firstReflection x)=firstReflection (N x) := by
  let M := reflectionPullback N
  have hM : ContDiff ℝ (⊤ : ℕ∞) M := reflectionPullback_contDiff hN
  have hpM : ∀ m x,M (x+latticeVector m)=M x := reflectionPullback_periodic hp
  have hμR : IsNormalMeasure E (μ.map sibling_reflectNormal) :=
    (isNormalMeasure_firstReflection hE hμ).congr_ae hR.symm
  have haeM := reflectionPullback_normal_ae hN hp hae
  obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique hV hE hmin x hx
  have he := (hw μ hμ N hN hp hae).trans (hw (μ.map sibling_reflectNormal) hμR M hM hpM haeM).symm
  change N x=firstReflection (N (firstReflection x)) at he
  have hh := congrArg firstReflection he
  simpa only [firstReflection_involutive] using hh.symm

theorem isMinimizerAt_reflection_seam_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E))
    (hfix : torusFirstReflection (quotientMap x)=quotientMap x) : N x 0=0 := by
  have he := isMinimizerAt_reflection_normal hV hE hmin hR hμ hN hp hae x hx
  have hq : quotientMap (firstReflection x)=quotientMap x := by rw [firstReflection_quotient,hfix]
  obtain ⟨m,hm⟩ := same_quotient_lattice hq
  rw [hm,hp] at he
  have hc := congrArg (fun v : Cover ↦ v 0) he
  simp only [firstReflection_apply,ite_true] at hc
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma firstSeam_zero_fixed (x : Cover) (hx : firstSeamFunction x=0) :
    torusFirstReflection (quotientMap x)=quotientMap x := by
  let n := round (2*x 0)
  have hb := firstSeam_distance_bound (x 0)
  change 4*|x 0-(n:ℝ)/2|≤|firstSeamFunction x| at hb
  rw [hx,abs_zero] at hb
  have he : x 0=(n:ℝ)/2 := by
    have hh : |x 0-(n:ℝ)/2|=0 := le_antisymm (by linarith) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hh)
  have hr : firstReflection x=x+latticeVector (Pi.single 0 (-n)) := by
    ext i
    by_cases hi : i=0
    · subst i
      simp only [firstReflection_apply,ite_true,PiLp.add_apply,latticeVector,
        Pi.single_eq_same,Int.cast_neg,he]
      ring
    · simp [firstReflection_apply,hi,latticeVector,Pi.single_apply]
  rw [←firstReflection_quotient,hr,quotientMap_add,quotientMap_latticeVector,add_zero]

theorem isMinimizerAt_reflection_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E)) (x : Torus) :
    torusFirstReflection x∈frontier (openRepresentative E) ↔
      x∈frontier (openRepresentative E) := by
  let F := torusFirstReflection ⁻¹' E
  have hF : MeasurableSet F := hE.preimage torusFirstReflection.continuous.measurable
  have hminF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hR).mp hmin
  have he : quotientMap ⁻¹' F=firstReflection ⁻¹' (quotientMap ⁻¹' E) := by
    ext y
    simp only [mem_preimage,firstReflection_quotient,F]
  have hh := isMinimizerAt_lifted_boundary_global hV hF hminF (representative x)
  rw [he] at hh
  have hcover : representative x∈coverEssentialBoundary
      (firstReflection ⁻¹' (quotientMap ⁻¹' E)) ↔
      firstReflection (representative x)∈coverEssentialBoundary (quotientMap ⁻¹' E) :=
    cover_boundary_measurePreserving_homeomorph firstReflection.toHomeomorph
      firstReflection.measurePreserving _
  rw [hcover] at hh
  rw [isMinimizerAt_lifted_boundary_global hV hE hmin,
    firstReflection_quotient,quotientMap_representative] at hh
  rw [←openRepresentative_congr_ae hR] at hh
  exact hh

lemma isMinimizerAt_reflection_normal_scalar {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Torus) (hx : x∈frontier (openRepresentative E)) :
    N (representative (torusFirstReflection x)) 0= -N (representative x) 0 := by
  have hh := isMinimizerAt_reflection_normal hV hE hmin hR hμ hN hp hae
    (representative x) (by simpa only [quotientMap_representative] using hx)
  have hc := congrArg (fun v : Cover ↦ v 0) hh
  simp only [firstReflection_apply,ite_true] at hc
  have hr : N (representative (torusFirstReflection x))=N (firstReflection (representative x)) := by
    have hq : torusFirstReflection x=quotientMap (firstReflection (representative x)) := by
      rw [firstReflection_quotient,quotientMap_representative]
    rw [hq,periodic_representative hp]
  rw [hr]
  exact hc

lemma isMinimizerAt_firstSeam_normal_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Torus) (hx : x∈frontier (openRepresentative E))
    (hz : firstSeamFunction (representative x)=0) : N (representative x) 0=0 := by
  exact isMinimizerAt_reflection_seam_normal hV hE hmin hR hμ hN hp hae
    (representative x) (by simpa only [quotientMap_representative] using hx)
    (firstSeam_zero_fixed _ hz)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positive_derivative_negative_on_left {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hd : 0<d) (hf0 : f 0=0) :
    ∀ᶠ t in 𝓝[<] (0 : ℝ),f t<0 := by
  have ht := hf.tendsto_slope_zero_left.eventually (isOpen_Ioi.mem_nhds hd)
  filter_upwards [ht,self_mem_nhdsWithin] with t hq hn
  have htneg : t<0 := hn
  have hqt : 0<f t/t := by
    simpa only [zero_add,hf0,sub_zero,smul_eq_mul,← div_eq_inv_mul] using hq
  rcases (div_pos_iff.mp hqt) with ⟨_,hpos⟩|⟨hneg,_⟩
  · exact (not_lt_of_ge htneg.le hpos).elim
  · exact hneg

lemma differentiable_piece_contradiction {f g : ℝ → ℝ} {d c : ℝ}
    (hf : HasDerivAt f d 0) (hd : 0<d) (hf0 : f 0=0)
    (hg : DifferentiableAt ℝ g 0) (hg0 : g 0=0) (hc : c≠0)
    (hplus : g=ᶠ[𝓝[>] (0 : ℝ)] fun t ↦ c*f t)
    (hminus : ∀ᶠ t in 𝓝[<] (0 : ℝ),f t<0 → g t=0) : False := by
  have hleft : g=ᶠ[𝓝[<] (0 : ℝ)] fun _ ↦ (0 : ℝ) := by
    filter_upwards [positive_derivative_negative_on_left hf hd hf0,hminus] with t ht hm
    exact hm ht
  have hl : Tendsto (fun t : ℝ ↦ t⁻¹*(g t-g 0)) (𝓝[<] 0) (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hleft] with t ht
    simp only [ht,hg0,sub_self,mul_zero]
  have hgl : Tendsto (fun t : ℝ ↦ t⁻¹*(g t-g 0)) (𝓝[<] 0) (𝓝 (deriv g 0)) := by
    simpa only [zero_add,smul_eq_mul] using hg.hasDerivAt.tendsto_slope_zero_left
  have hdz : deriv g 0=0 := tendsto_nhds_unique hgl hl
  have hgradR : Tendsto (fun t : ℝ ↦ t⁻¹*(g t-g 0)) (𝓝[>] 0) (𝓝 (deriv g 0)) := by
    simpa only [zero_add,smul_eq_mul] using hg.hasDerivAt.tendsto_slope_zero_right
  have hfr : Tendsto (fun t : ℝ ↦ t⁻¹*(c*f t-c*f 0)) (𝓝[>] 0) (𝓝 (c*d)) := by
    simpa only [zero_add,smul_eq_mul] using (hf.const_mul c).tendsto_slope_zero_right
  have hgr : Tendsto (fun t : ℝ ↦ t⁻¹*(g t-g 0)) (𝓝[>] 0) (𝓝 (c*d)) := by
    apply hfr.congr'
    filter_upwards [hplus] with t ht
    simp only [ht,hf0,hg0,mul_zero]
  have he : deriv g 0=c*d := tendsto_nhds_unique hgradR hgr
  exact (mul_ne_zero hc hd.ne') (he.symm.trans hdz)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma line_to_ball_inside {a x : Plane} {R t : ℝ} (hR : 0<R)
    (hx : ‖x-a‖=R) (ht : 0<t) (ht1 : t<1) :
    x+t • (a-x)∈Metric.ball a R := by
  have he : x+t • (a-x)-a=(1-t) • (x-a) := by module
  simp only [Metric.mem_ball,dist_eq_norm,he,norm_smul,Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr ht1),hx]
  nlinarith

theorem cmc_nodal_piece_C1_impossible {p : Plane → Plane} {f g : Plane → ℝ}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {s c : ℝ} (hs : 0<s) (hc : c≠0)
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 s))
    (hpb : ∀ y∈Metric.ball (0 : Plane) s,‖p y‖≤1)
    (hLf : ∀ y∈Metric.ball (0 : Plane) s,
      planeDivergence (fun z ↦ cmcJacobian (p z) (gradient f z)) y=0)
    {O : Set Plane} (hO : IsOpen O) (hcl : (0 : Plane)∈closure O) (hzero : (0 : Plane)∉O)
    (hpos : ∀ y∈O,0<f y)
    (hboundary : ∀ y∈closure O,y∈Metric.ball (0 : Plane) s → y∉O → f y=0)
    (hmul : ∀ y∈O,y∈Metric.ball (0 : Plane) s → g y=c*f y)
    (hvanish : ∀ y∈Metric.ball (0 : Plane) s,f y≤0 → g y=0) : False := by
  obtain ⟨a,x,R,hR,hxR,hxcl,hxO,hBO,hBS⟩ := plane_interior_tangent_ball hO hcl hzero hs
  have hxball : x∈Metric.closedBall a R := by simp only [Metric.mem_closedBall,dist_eq_norm,hxR,le_refl]
  have hxS := hBS hxball
  have hfx : f x=0 := hboundary x hxcl hxS hxO
  have hdf := cmc_hopf_inward_derivative hp hf hR hxR hfx
    (fun y hy ↦ hpb y (hBS hy)) (fun y hy ↦ hpos y (hBO hy))
    (fun y hy ↦ hLf y (hBS (Metric.ball_subset_closedBall hy)))
  let v := a-x
  let l : ℝ → Plane := fun t ↦ x+t • v
  have hl : HasDerivAt l v 0 := by
    simpa only [l,id_eq,one_smul,zero_smul,add_zero,zero_add] using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hfl : HasDerivAt (fun t ↦ f (l t)) (fderiv ℝ f x v) 0 := by
    have hd := (hf.differentiable (by simp) (l 0)).hasFDerivAt.comp_hasDerivAt 0 hl
    simpa only [l,zero_smul,add_zero,Function.comp_def] using hd
  have hgD : DifferentiableAt ℝ g x :=
    ((hg x hxS).contDiffAt (Metric.isOpen_ball.mem_nhds hxS)).differentiableAt (by norm_num)
  have hgl : DifferentiableAt ℝ (fun t ↦ g (l t)) 0 := by
    have hd : DifferentiableAt ℝ g (l 0) := by simpa only [l,zero_smul,add_zero] using hgD
    exact hd.comp 0 hl.differentiableAt
  have hLS : ∀ᶠ t in 𝓝 (0 : ℝ),l t∈Metric.ball (0 : Plane) s := by
    apply hl.continuousAt.preimage_mem_nhds
    simpa only [l,zero_smul,add_zero] using Metric.isOpen_ball.mem_nhds hxS
  apply differentiable_piece_contradiction hfl hdf
    (by simpa only [l,zero_smul,add_zero]) hgl
    (by simpa only [l,zero_smul,add_zero] using hvanish x hxS hfx.le) hc
  · have ht1 : ∀ᶠ t in 𝓝[>] (0 : ℝ),t<1 :=
      (eventually_lt_nhds (show (0 : ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [ht1,self_mem_nhdsWithin,hLS.filter_mono nhdsWithin_le_nhds] with t ht1 ht htS
    exact hmul (l t) (hBO (line_to_ball_inside hR hxR ht ht1)) htS
  · filter_upwards [hLS.filter_mono nhdsWithin_le_nhds] with t ht hn
    exact hvanish (l t) ht hn.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem CenteredJacobiChart.nodal_truncation_impossible
    {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (c : CenteredJacobiChart E μ N)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q (surfaceSmoothJet μ f) v=0)
    (hjw : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp c.n)) v=0)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ q u v=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (haeF : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z))
    {D : Set Torus} (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D)
    (hcl : quotientMap cubeCenter∈closure D) (hnot : quotientMap cubeCenter∉D)
    {k : ℝ} (hk : k≠0)
    (hFD : ∀ a∈D,F a=k*f.val (representative a))
    (hFzero : ∀ a∈frontier (openRepresentative E),f.val (representative a)≤0 → F a=0) : False := by
  obtain ⟨s,hs,hsr,hC1⟩ := c.boundary_continuous_C1 hE hμ hN hp haeN q hu hju hjw hFm hF haeF
  let O : Set Plane := Metric.ball 0 c.r∩(fun y ↦ quotientMap (c.parameter y)) ⁻¹' D
  let f' : Plane → ℝ := fun y ↦ c.weight y*f.val (c.parameter y)
  let g' : Plane → ℝ := fun y ↦ c.weight y*F (quotientMap (c.parameter y))
  have hsrad : s≤c.r := by linarith [c.r_pos]
  have hs₂ : s≤c.r/2 := by linarith [c.r_pos]
  have hwb (y : Plane) : 0<c.weight y := cmcWeight_pos _
  have hball {y : Plane} (hy : y∈Metric.ball (0 : Plane) s) : y∈Metric.ball (0 : Plane) c.r :=
    Metric.ball_subset_ball hsrad hy
  have hclO : (0 : Plane)∈closure O := c.closure_pullback
    (positiveNodalPiece_subset f hD) hcl c.r_pos
  have hO : IsOpen O := c.positive_piece_pullback_open f hD
  have hzero : (0 : Plane)∉O := by
    intro h0
    apply hnot
    have hh : quotientMap (c.parameter 0)∈D := h0.2
    rwa [c.parameter_zero] at hh
  have hLf := c.classical_ground_state hE hμ hN hp haeN q f hjf hjw
  apply cmc_nodal_piece_C1_impossible (plane_gradient_contDiff c.smooth)
    (c.weight_smooth.mul (f.property.1.comp c.parameter_smooth)) hs hk
    ((c.weight_smooth.of_le (by simp)).contDiffOn.mul hC1)
    (fun y hy ↦ (c.slope_disk y (Metric.ball_subset_closedBall (hball hy))).trans (by norm_num))
    (fun y hy ↦ hLf y (Metric.ball_subset_ball hs₂ hy)) hO hclO hzero
  · intro y hy
    have hpos := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1 _ hy.2
    rw [periodic_representative f.property.2] at hpos
    exact mul_pos (hwb y) hpos
  · intro y hy hyS hyO
    have hycl : quotientMap (c.parameter y)∈closure D := by
      have hsub : O⊆(fun y ↦ quotientMap (c.parameter y)) ⁻¹' closure D := by
        intro z hz
        exact subset_closure hz.2
      exact closure_minimal hsub (isClosed_closure.preimage
        (continuous_quotientMap.comp c.parameter_smooth.continuous)) hy
    have hyD : quotientMap (c.parameter y)∉D := fun h ↦ hyO ⟨hball hyS,h⟩
    have hz := positiveNodalPiece_boundary_zero f isClosed_frontier hD hycl hyD
    rw [periodic_representative f.property.2] at hz
    change c.weight y*f.val (c.parameter y)=0
    rw [hz,mul_zero]
  · intro y hy _
    have he := hFD _ hy.2
    rw [periodic_representative f.property.2] at he
    change c.weight y*F (quotientMap (c.parameter y))=k*(c.weight y*f.val (c.parameter y))
    rw [he]
    ring
  · intro y hy hle
    have hfle : f.val (c.parameter y)≤0 := by
      by_contra! hh
      exact (mul_pos (hwb y) hh).not_ge hle
    have hb : quotientMap (c.parameter y)∈frontier (openRepresentative E) :=
      c.boundary_disk y (Metric.ball_subset_closedBall (hball hy))
    have he := hFzero _ hb
      (by simpa only [periodic_representative f.property.2] using hfle)
    change c.weight y*F (quotientMap (c.parameter y))=0
    rw [he,mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nodal_truncation_impossible {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (haeN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hjN : ∀ w : Cover,∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (directionalNormalScalar N hN hp w)) v=0)
    (f : smoothPeriodicScalars)
    (hjf : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ f) v=0)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hju : ∀ v∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u v=0)
    {F : Torus → ℝ} (hFm : Measurable F)
    (hF : ContinuousOn F (frontier (openRepresentative E)))
    (haeF : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z))
    {D : Set Torus} (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D)
    {x : Torus} (hcl : x∈closure D) (hnot : x∉D)
    {k : ℝ} (hk : k≠0)
    (hFD : ∀ a∈D,F a=k*f.val (representative a))
    (hFzero : ∀ a∈frontier (openRepresentative E),f.val (representative a)≤0 → F a=0) : False := by
  let a : Cover := representative x-cubeCenter
  have hshift : quotientMap cubeCenter+quotientMap a=x := by
    dsimp [a]
    rw [quotientMap_sub,quotientMap_representative]
    abel
  let E' : Set Torus := (fun b ↦ b+quotientMap a) ⁻¹' E
  let D' : Set Torus := (fun b ↦ b+quotientMap a) ⁻¹' D
  let μ' := μ.map (translateNormal a)
  let N' := normalTranslateField a N
  let hN' := normalTranslateField_smooth a hN
  let hp' := normalTranslateField_periodic a hp
  let F' : Torus → ℝ := fun b ↦ F (b+quotientMap a)
  let f' := sibling_smoothScalarTranslate a f
  have hE' : MeasurableSet E' := hE.preimage (measurable_id.add measurable_const)
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin (quotientMap a)
  have hμ' : IsNormalMeasure E' μ' := isNormalMeasure_translation hE hμ a
  have haeN' := normalTranslateField_ae μ a hN.continuous hp haeN
  have hS' : frontier (openRepresentative E')=(fun b ↦ b+quotientMap a) ⁻¹'
      frontier (openRepresentative E) := frontier_openRepresentative_translation hE _
  have hxS : x∈frontier (openRepresentative E) :=
    isClosed_frontier.closure_subset_iff.mpr (positiveNodalPiece_subset f hD) hcl
  have hcenter : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [hS']
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rwa [hshift]
  obtain ⟨c⟩ := isMinimizerAt_centeredJacobiChart hV hE' hmin' hcenter hμ' hN' hp' haeN'
  obtain ⟨u',hu',he⟩ := normalTranslateJet_surjective_H1 μ a hu
  have hD' : IsPositiveNodalPiece f' (frontier (openRepresentative E')) D' := by
    rw [hS']
    exact positiveNodalPiece_translation a f hD
  have hcl' : quotientMap cubeCenter∈closure D' := by
    change quotientMap cubeCenter∈closure ((Homeomorph.addRight (quotientMap a)) ⁻¹' D)
    rw [← (Homeomorph.addRight (quotientMap a)).preimage_closure]
    change quotientMap cubeCenter+quotientMap a∈closure D
    rwa [hshift]
  have hn' : quotientMap cubeCenter∉D' := by
    change quotientMap cubeCenter+quotientMap a∉D
    rwa [hshift]
  refine c.nodal_truncation_impossible hE' hμ' hN' hp' haeN'
    (surfaceCurvatureLp μ' N' hN') f'
    (normalTranslate_smooth_weakJacobi μ a hN hp f hjf) ?_
    hu' (normalTranslate_weakJacobi μ a hN hp hju he)
    (hFm.comp (measurable_id.add measurable_const)) ?_
    (normalTranslateJet_scalar_representative μ a he hFm haeF) hD' hcl' hn' hk ?_ ?_
  · change ∀ v∈surfaceH1 μ',surfaceJacobiB μ' (surfaceCurvatureLp μ' N' hN')
      (surfaceSmoothJet μ' (directionalNormalScalar N' hN' hp' c.n)) v=0
    rw [normalTranslate_directional a hN hp]
    exact normalTranslate_smooth_weakJacobi μ a hN hp _ (hjN c.n)
  · change ContinuousOn F' (frontier (openRepresentative E'))
    rw [hS']
    exact hF.comp (continuous_id.add continuous_const).continuousOn (fun _ h ↦ h)
  · intro b hb
    change F (b+quotientMap a)=k*(sibling_smoothScalarTranslate a f).val (representative b)
    rw [smoothScalarTranslate_descent]
    exact hFD _ hb
  · intro b hb hle
    apply hFzero
    · rwa [hS'] at hb
    · rwa [smoothScalarTranslate_descent] at hle

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma sibling_directionalNormalScalar_mean_zero {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover) :
    surfaceMean μ (surfaceSmoothJet μ (directionalNormalScalar N hN hp v))=0 := by
  simp only [directionalNormalScalar,map_sum,map_smul,
    normalComponentScalar_mean_zero hμ hN hp hae,smul_zero,Finset.sum_const_zero]

lemma isMinimizerAt_trace_has_negative {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) (hm : surfaceMean μ (surfaceSmoothJet μ f)=0)
    (hpos : ∃ x∈frontier (openRepresentative E),0<f.val (representative x)) :
    ∃ x∈frontier (openRepresentative E),f.val (representative x)<0 := by
  by_contra! hn
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hnonneg : ∀ᵐ z ∂(μ : Measure NormalBundle),0≤f.val z.1 := by
    filter_upwards [hbd] with z hz
    have hh := hn (normalProjection z) hz
    change 0≤f.val (representative (quotientMap z.1)) at hh
    rwa [periodic_representative f.property.2] at hh
  have hi : Integrable (fun z : NormalBundle ↦ f.val z.1) (μ : Measure NormalBundle) :=
    (smoothScalarValue f).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [surfaceMean_of_smooth] at hm
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hm
  obtain ⟨x,hx,hxp⟩ := hpos
  have hx0 := isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ f.property.1.continuous
    continuous_const f.property.2 (fun _ _ ↦ rfl) hae (representative x)
    (by simpa only [quotientMap_representative] using hx)
  exact hxp.ne' hx0

lemma isMinimizerAt_negative_unused_patch {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (f : smoothPeriodicScalars) (hm : surfaceMean μ (surfaceSmoothJet μ f)=0)
    {D A : Set Torus}
    (hD : IsPositiveNodalPiece f (frontier (openRepresentative E)) D)
    (hA : IsPositiveNodalPiece f (frontier (openRepresentative E)) A) (hDn : D.Nonempty) :
    ∃ U : Set Torus,IsOpen U ∧ (U∩frontier (openRepresentative E)).Nonempty ∧
      Disjoint U D ∧ Disjoint U A := by
  have hdp := (positiveNodalPiece_superlevels f isClosed_frontier hD).2.1
  have hap := (positiveNodalPiece_superlevels f isClosed_frontier hA).2.1
  obtain ⟨x,hx⟩ := hDn
  have hxS : x∈frontier (openRepresentative E) := by
    rw [hD.1.choose_spec.2] at hx
    exact hx.1.1
  obtain ⟨y,hy,hyneg⟩ := isMinimizerAt_trace_has_negative hV hE hmin hμ f hm ⟨x,hxS,hdp x hx⟩
  refine ⟨{a | f.val (representative a)<0},
    isOpen_lt (continuous_periodic_descent f.property.1.continuous f.property.2) continuous_const,
    ⟨y,hyneg,hy⟩,?_,?_⟩
  · exact Set.disjoint_left.mpr (fun z hz hd ↦ (hdp z hd).not_gt hz)
  · exact Set.disjoint_left.mpr (fun z hz ha ↦ (hap z ha).not_gt hz)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

end Periodic
end CubicTorus
end
end
end

end OAI
