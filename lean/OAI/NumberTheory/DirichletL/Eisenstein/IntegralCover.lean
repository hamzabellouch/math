import OAI.NumberTheory.DirichletL.Eisenstein.AffineCuspFourier

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedOmegaUnit : Eisˣ := (omega_primitive.isUnit (by decide)).unit
lemma ramifiedOmegaUnit_val : (ramifiedOmegaUnit:Eis)=omega :=
  (omega_primitive.isUnit (by decide)).unit_spec

lemma onceCusp_q_as_scale (t:Eisˣ) (l:Fin 3) :
    onceCuspScale (t*ramifiedOmegaUnit^l.val)=onceCuspScale t*omega^l.val := by
  simp only [onceCuspScale,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
  ring

lemma onceCusp_q_congr_scale (t:Eisˣ) (l:Fin 3) :
    (3:Eis)∣onceCuspScale t*omega^l.val-onceCuspScale t := by
  obtain ⟨b,hb⟩:=halfPrimary_omega_pow l.val
  have he:onceCuspScale t*omega^l.val-onceCuspScale t=
      (onceCuspScale t*(omega-1))*b:=by
    linear_combination onceCuspScale t*hb
  rw [he]
  exact (onceCusp_scale_lambda t).mul_right b

lemma onceCusp_q_dvd_three (t:Eisˣ) (l:Fin 3) :
    onceCuspScale t*omega^l.val∣(3:Eis) := by
  rw [←onceCusp_q_as_scale]
  exact ⟨onceCuspComplement _,(onceCusp_scale_complement _).symm⟩

lemma onceCusp_q_trace_dvd (t:Eisˣ) (l:Fin 3) :
    (3:Eis)∣ramifiedTraceLambda*(onceCuspScale t*omega^l.val) := by
  refine ⟨-(t:Eis)*omega^l.val,?_⟩
  unfold onceCuspScale
  linear_combination (t:Eis)*omega^l.val*ramifiedTraceLambda_square

lemma onceCusp_q_dvd_frequency (t:Eisˣ) (l:Fin 3) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) : onceCuspScale t*omega^l.val∣h := by
  have hd:(3:Eis)∣h-onceCuspScale t*omega^l.val:=by
    convert dvd_sub hfreq (onceCusp_q_congr_scale t l) using 1 ;ring
  have hh:onceCuspScale t*omega^l.val∣h-onceCuspScale t*omega^l.val:=
    (onceCusp_q_dvd_three t l).trans hd
  simpa only [sub_add_cancel] using dvd_add hh (dvd_refl (onceCuspScale t*omega^l.val))

lemma onceCusp_period_congruence (t:Eisˣ) (l:Fin 3) (h:Eis) (j:ℕ)
    (hfreq:(3:Eis)∣h-onceCuspScale t) :
    (3:Eis)∣h+ramifiedAffineParameter j 1*(onceCuspScale t*omega^l.val) := by
  have hd:(3:Eis)∣h-onceCuspScale t*omega^l.val:=by
    convert dvd_sub hfreq (onceCusp_q_congr_scale t l) using 1 ;ring
  have ht:=(onceCusp_q_trace_dvd t l).mul_left (j:Eis)
  convert dvd_add hd ht using 1 ; simp only [ramifiedAffineParameter,Nat.cast_one] ;ring

def onceCuspFrequencyQuotient (t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (l:Fin 3) : Eis :=
  Classical.choose (onceCusp_q_dvd_frequency t l h hfreq)

lemma onceCuspFrequencyQuotient_spec (t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (l:Fin 3) :
    h=(onceCuspScale t*omega^l.val)*onceCuspFrequencyQuotient t h hfreq l :=
  Classical.choose_spec (onceCusp_q_dvd_frequency t l h hfreq)

def onceCuspRayUnit (u t:Eisˣ) (l:Fin 3) : Eisˣ := u⁻¹^2*t*ramifiedOmegaUnit^l.val

def onceCuspRayIndex (u t:Eisˣ) (l:Fin 3) : Fin 3 :=
  Classical.choose (unit_eq_sign_omega (onceCuspRayUnit u t l))

lemma onceCuspRayIndex_spec (u t:Eisˣ) (l:Fin 3) :
    (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=omega^(onceCuspRayIndex u t l).val*ramifiedTraceLambda ∨
      (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=-(omega^(onceCuspRayIndex u t l).val*ramifiedTraceLambda) := by
  have he:(↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=
      (onceCuspRayUnit u t l:Eis)*ramifiedTraceLambda:=by
    simp only [onceCuspRayUnit,onceCuspScale,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    ring
  have hh:=Classical.choose_spec (unit_eq_sign_omega (onceCuspRayUnit u t l))
  change (onceCuspRayUnit u t l:Eis)=omega^(onceCuspRayIndex u t l).val ∨
    (onceCuspRayUnit u t l:Eis)=-(omega^(onceCuspRayIndex u t l).val) at hh
  rw [he]
  rcases hh with hh|hh
  · exact Or.inl (by rw [hh])
  · exact Or.inr (by rw [hh];ring)

def onceCuspGaussSeries (u t:Eisˣ) (h:Eis) (hfreq:(3:Eis)∣h-onceCuspScale t) (s:ℂ) : ℂ :=
  ∑l:Fin 3,if (3:Eis)∣onceCuspFrequencyQuotient t h hfreq l+
    ramifiedAffineParameter (onceCuspRayIndex u t l).val 1 then
      (3:ℂ)*(3:ℂ)^(-s)*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
        unramifiedCubicGaussSeries s
          (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*onceCuspFrequencyQuotient t h hfreq l) else 0

theorem onceCusp_eisenstein_fourier (u t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*onceCuspGaussSeries u t h hfreq s := by
  rw [diagonal_once_eisenstein_fourier u t (fun l=>(onceCuspRayIndex u t l).val) h
    (onceCuspFrequencyQuotient t h hfreq) (onceCuspRayIndex_spec u t)
      (onceCuspFrequencyQuotient_spec t h hfreq)
        (fun l=>onceCusp_period_congruence t l h _ hfreq) v hv s hs,
    onceCuspGaussSeries,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  split_ifs <;>ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Manifold ContDiff
open Finset AddChar MulChar EisensteinEmbedding

lemma hyperbolicAction_contMDiff (g : SL(2,ℂ)) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      (fun w : HyperbolicSpace=>g•w) := by
  intro w
  rw [contMDiffAt_iff]
  refine ⟨(continuous_hyperbolic_action g).continuousAt,?_⟩
  have hp : hyperbolicSpatialCoordinates w∈hyperbolicSpatialChart.target :=
    hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have he : (fun p : SpatialCoordinates=>hyperbolicSpatialCoordinates
      (g•hyperbolicSpatialChart.symm p))=ᶠ[𝓝 (hyperbolicSpatialCoordinates w)]mobiusSpatial g := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hpt
    rw [mobiusSpatial_coordinates_global]
    exact congrArg (mobiusSpatial g) (hyperbolicSpatialChart.right_inv hpt)
  have hd := ((mobiusSpatial_contDiffAt g _ (hyperbolicSpatialCoordinates_positive w)).congr_of_eventuallyEq he).contDiffWithinAt (s:=Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.preimage_id_eq,Set.range_id,
    hyperbolicSpatial_chartAt,hyperbolicSpatialChart_apply,Function.comp_def,id_eq] using hd

lemma kernel_contMDiff_of_lift (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞
      (fun w : HyperbolicSpace=>f (integralOrbitProjection globalKubotaKernel w))) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f := by
  intro q
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hs : ContMDiffOn 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      hyperbolicSpatialChart.symm hyperbolicSpatialChart.target := by
    simpa only [hyperbolicSpatial_chartAt] using
      (contMDiffOn_chart_symm (I:=𝓘(ℝ,SpatialCoordinates)) (n:=∞) (x:=q.out))
  have hd := (hf (hyperbolicSpatialChart.symm (kernelQuotientChart q q))).comp _
    (hs.contMDiffAt (hyperbolicSpatialChart.open_target.mem_nhds hp))
  have he : (fun p=>f ((kernelQuotientChart q).symm p))=
      (fun p=>f (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p))) := by
    funext p
    rw [kernelQuotientChart_symm]
  have hdc : ContDiffAt ℝ ∞ (fun p=>f ((kernelQuotientChart q).symm p))
      (kernelQuotientChart q q) := by
    rw [he]
    exact hd.contDiffAt
  have hc : ContinuousAt f q := by
    have hc := hdc.continuousAt.comp
      ((kernelQuotientChart q).continuousOn.continuousAt
        ((kernelQuotientChart q).open_source.mem_nhds hq))
    apply hc.congr
    filter_upwards [(kernelQuotientChart q).open_source.mem_nhds hq] with r hr
    exact congrArg f ((kernelQuotientChart q).left_inv hr)
  rw [contMDiffAt_iff]
  refine ⟨hc,?_⟩
  have hh := hdc.contDiffWithinAt (s:=Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    kernelSpatial_chartAt,chartAt_self_eq,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh

lemma kernelSource_comp_contMDiff (M : CubicKubota.levelTwo) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (fun q=>f (kernelSourceAction M q)) := by
  apply kernel_contMDiff_of_lift
  exact (hf.comp kernelProjection_contMDiff).comp (hyperbolicAction_contMDiff (sourceComplexMatrix M))

def kernelSourceTest (M : CubicKubota.levelTwo) (f : kernelSmoothTests) : kernelSmoothTests :=
  ⟨fun q=>f.1 (kernelSourceAction M q),kernelSource_comp_contMDiff M f.1 f.2.1,
    f.2.2.comp_homeomorph (kernelSourceHomeomorph M)⟩

def kernelSourceTestLinear (M : CubicKubota.levelTwo) : kernelSmoothTests→ₗ[ℂ]kernelSmoothTests where
  toFun := kernelSourceTest M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma kernelSourceTest_field (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelTestField (kernelSourceTest M f)=kernelTestField f ∘ euclideanAction (sourceComplexMatrix M) := by
  funext p
  change f.1 (integralOrbitProjection globalKubotaKernel
      (sourceComplexMatrix M•euclideanToHyperbolic p))=
    f.1 (integralOrbitProjection globalKubotaKernel
      (euclideanToHyperbolic (euclideanAction (sourceComplexMatrix M) p)))
  rw [euclideanAction,euclideanToHyperbolic_coordinates]

lemma kernelSourceTest_energyDensity (M : CubicKubota.levelTwo) (f : kernelSmoothTests)
    (w : HyperbolicSpace) :
    kernelTestEnergyDensity (kernelSourceTest M f) w=
      kernelTestEnergyDensity f (sourceComplexMatrix M•w) := by
  have hp := hyperbolicHeight_pos w
  have he : hyperbolicEuclideanCoordinates (sourceComplexMatrix M•w)=
      euclideanAction (sourceComplexMatrix M) (hyperbolicEuclideanCoordinates w) := by
    rw [euclideanAction,euclideanToHyperbolic_coordinates]
  have hR := hyperbolic_cotangent_energy_comp (sourceComplexMatrix M)
    (fun p : EuclideanSpatial=>(kernelTestField f p).re) (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_re_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp))
  have hI := hyperbolic_cotangent_energy_comp (sourceComplexMatrix M)
    (fun p : EuclideanSpatial=>(kernelTestField f p).im) (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_im_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp))
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  rw [kernelSourceTest_field,he]
  exact congrArg₂ (fun a b : ℝ=>a+b) hR hI

lemma kernelSourceTest_quotientDensity (M : CubicKubota.levelTwo) (f : kernelSmoothTests)
    (q : KernelQuotient) :
    kernelQuotientEnergyDensity (kernelSourceTest M f) q=
      kernelQuotientEnergyDensity f (kernelSourceAction M q) := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelSourceTest_energyDensity M f w

lemma kernelSourceTest_energy (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelDirichletEnergy (kernelSourceTest M f)=kernelDirichletEnergy f := by
  unfold kernelDirichletEnergy
  simp_rw [kernelSourceTest_quotientDensity]
  exact (kernelSourceAction_measurePreserving M).integral_comp
    (kernelSourceHomeomorph M).measurableEmbedding _

lemma kernelSourceTest_mass (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelSmoothTestsToL2 (kernelSourceTest M f)=kernelSourcePullback M (kernelSmoothTestsToL2 f) := by
  apply Lp.ext
  have hbase := (kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelSmoothTests_memLp f).coeFn_toLp
  filter_upwards [(kernelSmoothTests_memLp (kernelSourceTest M f)).coeFn_toLp,
    kernelSourcePullback_ae_eq M (kernelSmoothTestsToL2 f),hbase] with q hnew hpull hbase
  exact hnew.trans (hpull.trans hbase).symm

lemma kernelSourceTest_graph_norm (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore (kernelSourceTest M f)‖=‖kernelEnergyGraphCore f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [kernelEnergyGraphCore_norm_sq,kernelEnergyGraphCore_norm_sq,
    kernelSourceTest_energy,kernelSourceTest_mass,LinearIsometry.norm_map]

def kernelSourceEnergyPullback (M : CubicKubota.levelTwo) : KernelEnergyGraph→ₗᵢ[ℂ]KernelEnergyGraph :=
  (kernelEnergyGraphCore.comp (kernelSourceTestLinear M)).extendOfIsometry
    kernelEnergyGraphCore_dense (kernelSourceTest_graph_norm M)

lemma kernelSourceEnergyPullback_core (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelSourceEnergyPullback M (kernelEnergyGraphCore f)=kernelEnergyGraphCore (kernelSourceTest M f) :=
  LinearMap.extendOfIsometry_eq (kernelEnergyGraphCore.comp (kernelSourceTestLinear M))
    kernelEnergyGraphCore_dense (kernelSourceTest_graph_norm M) f

lemma kernelSourceEnergyPullback_mass (M : CubicKubota.levelTwo) (u : KernelEnergyGraph) :
    kernelEnergyMass (kernelSourceEnergyPullback M u)=kernelSourcePullback M (kernelEnergyMass u) := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (kernelEnergyMass.continuous.comp (kernelSourceEnergyPullback M).continuous)
    ((kernelSourcePullback M).continuous.comp kernelEnergyMass.continuous) ?_) u
  funext f
  change kernelEnergyMass (kernelSourceEnergyPullback M (kernelEnergyGraphCore f))=
    kernelSourcePullback M (kernelEnergyMass (kernelEnergyGraphCore f))
  rw [kernelSourceEnergyPullback_core,kernelEnergyMass_core,kernelEnergyMass_core,kernelSourceTest_mass]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

lemma kernelSourceEnergyPullback_inverse (M : CubicKubota.levelTwo) (u : KernelEnergyGraph) :
    kernelSourceEnergyPullback M (kernelSourceEnergyPullback M⁻¹ u)=u := by
  apply kernelEnergyMass_injective
  rw [kernelSourceEnergyPullback_mass,kernelSourceEnergyPullback_mass,
    kernelSourcePullback_comp,inv_mul_cancel,kernelSourcePullback_one]

lemma kernelSourceEnergyPullback_surjective (M : CubicKubota.levelTwo) :
    Function.Surjective (kernelSourceEnergyPullback M) :=
  fun u=>⟨kernelSourceEnergyPullback M⁻¹ u,kernelSourceEnergyPullback_inverse M u⟩

theorem kernelSource_variationalSolution (M : CubicKubota.levelTwo) (F : KernelQuotientL2) :
    kernelSourceEnergyPullback M (kernelVariationalSolution F)=
      kernelVariationalSolution (kernelSourcePullback M F) := by
  apply kernelVariationalSolution_unique
  intro v
  obtain ⟨w,rfl⟩ := kernelSourceEnergyPullback_surjective M v
  rw [←kernelEnergyGraph_inner,LinearIsometry.inner_map_map,
    kernelSourceEnergyPullback_mass,LinearIsometry.inner_map_map,kernelEnergyGraph_inner]
  exact kernelVariationalSolution_equation F w

theorem kernelSource_variationalResolvent (M : CubicKubota.levelTwo) (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelSourcePullback M F)=
      kernelSourcePullback M (kernelVariationalResolvent F) := by
  change kernelEnergyMass (kernelVariationalSolution (kernelSourcePullback M F))=
    kernelSourcePullback M (kernelEnergyMass (kernelVariationalSolution F))
  rw [←kernelSource_variationalSolution,kernelSourceEnergyPullback_mass]

theorem kernelSource_operatorGraph (M : CubicKubota.levelTwo)
    (F G : KernelQuotientL2) (hFG : (F,G)∈kernelEnergyLaplacian.graph) :
    (kernelSourcePullback M F,kernelSourcePullback M G)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hFG ⊢
  rw [←map_add,kernelSource_variationalResolvent,hFG]

theorem kernelSource_eigenvector (M : CubicKubota.levelTwo) (F : KernelQuotientL2)
    (eigenvalue : ℂ) (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph) :
    (kernelSourcePullback M F,eigenvalue • kernelSourcePullback M F)∈kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelSource_operatorGraph M F (eigenvalue • F) hF

end CubicEisenstein

section

open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def cubeCuspHeightWeight (p:Eis) (j:Fin 4) : ℂ :=
  (((Ideal.absNorm (Ideal.span {p}):ℝ)^((2*(j.val:ℝ)-3)/3)):ℝ)

lemma cubeCuspHeightWeight_zero (p:Eis) :
    cubeCuspHeightWeight p 0=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ := by
  unfold cubeCuspHeightWeight
  generalize Ideal.absNorm (Ideal.span {p}) = n
  norm_num [Real.rpow_neg_one]

lemma cubeCuspHeightWeight_three (p:Eis) :
    cubeCuspHeightWeight p 3=(Ideal.absNorm (Ideal.span {p}):ℂ) := by
  unfold cubeCuspHeightWeight
  generalize Ideal.absNorm (Ideal.span {p}) = n
  norm_num

theorem actualCubeCuspPhaseSum_height (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1) :
    actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2 := by
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp.ne_zero)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=by exact_mod_cast hqN
  by_cases hc:p∣((A:SL(2,Eis)) 1 0)
  · rw [actualCubeCuspPhaseSum_dvd A p hp hprimary hA hc,
      cubeCuspHeightWeight_zero]
    field_simp
  · have hcop:IsCoprime ((A:SL(2,Eis)) 1 0) p:=(hp.coprime_iff_not_dvd.mpr hc).symm
    rw [actualCubeCuspPhaseSum_coprime A p hp hprimary hA hcop,
      cubeCuspHeightWeight_zero,cubeCuspHeightWeight_three]
    field_simp
    ; ring

theorem actualCubeCuspPhaseSum_normalized (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1) :
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ := by
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp.ne_zero)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=by exact_mod_cast hqN
  rw [actualCubeCuspPhaseSum_height A p hp hprimary hA]
  field_simp

end CubicKubota

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def cubeDilationRoot (p:Eis) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2))

lemma cubeDilationRoot_sq (p:Eis) : cubeDilationRoot p^2=eisEmbedding p^3 :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2))

lemma cubeDilationRoot_ne_zero (p:Eis) (hp:p≠0) : cubeDilationRoot p≠0 := by
  intro h
  have hs:=cubeDilationRoot_sq p
  rw [h,zero_pow (by decide)] at hs
  exact pow_ne_zero 3 (eisEmbedding_ne_zero hp) hs.symm

def cubeAverageMatrix (p:Eis) (hp:p≠0) (q:Eis) : SL(2,ℂ) :=
  complexDiagonal (cubeDilationRoot p)⁻¹ (inv_ne_zero (cubeDilationRoot_ne_zero p hp)) *
    complexTranslation (3*eisEmbedding q)

lemma cubeAverageMatrix_entries (p:Eis) (hp:p≠0) (q:Eis) :
    (cubeAverageMatrix p hp q : Matrix (Fin 2) (Fin 2) ℂ)=
      !![(cubeDilationRoot p)⁻¹,(cubeDilationRoot p)⁻¹*(3*eisEmbedding q);0,cubeDilationRoot p] := by
  unfold cubeAverageMatrix
  rw [Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiagonal, complexTranslation, Matrix.mul_apply, Fin.sum_univ_two]

lemma cubeAverageMatrix_add_multiple (p:Eis) (hp:p≠0) (q n:Eis) :
    cubeAverageMatrix p hp (q+p^3*n)=
      complexTranslation (3*eisEmbedding n)*cubeAverageMatrix p hp q := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, cubeAverageMatrix_entries]
  apply Matrix.ext
  intro i j
  have hz := cubeDilationRoot_ne_zero p hp
  have he := cubeDilationRoot_sq p
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, complexTranslation,
      map_add, map_mul, map_pow]
  rw [← he]
  field_simp

lemma cubeAverageMatrix_translate_one (p:Eis) (hp:p≠0) (q t:Eis)
    (ht:3*t=1-p^3) :
    cubeAverageMatrix p hp q*complexTranslation 1=
      complexTranslation 1*cubeAverageMatrix p hp (q+t) := by
  have ht':3*eisEmbedding t=1-eisEmbedding p^3:=by
    simpa only [map_mul,map_sub,map_one,map_ofNat,map_pow] using congrArg eisEmbedding ht
  have hz:=cubeDilationRoot_ne_zero p hp
  have he:=cubeDilationRoot_sq p
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, cubeAverageMatrix_entries]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, complexTranslation, map_add]
  field_simp
  linear_combination -ht'-he

def cubeAverage (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (w:HyperbolicSpace) : ℂ :=
  (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
    ∑' r:Eis⧸Ideal.span {p^3},
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)

lemma cubeAverage_summand_congr (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ)
    (hF:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (a b:Eis) (hab:p^3∣a-b) (w:HyperbolicSpace) :
    F (cubeAverageMatrix p hp a • w)=F (cubeAverageMatrix p hp b • w) := by
  obtain ⟨n,hn⟩:=hab
  have ha:a=b+p^3*n:=by linear_combination hn
  rw [ha,cubeAverageMatrix_add_multiple,mul_smul,hF]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeAverageMatrix_action (p:Eis) (hp:p≠0) (q:Eis)
    (z:ℂ) (v:ℝ) (hv:0<v) :
    cubeAverageMatrix p hp q • upperPoint z v hv =
      upperPoint ((z+3*eisEmbedding q)/eisEmbedding p^3)
        (v/‖eisEmbedding p‖^3) (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)) := by
  rw [cubeAverageMatrix,mul_smul,complexTranslation_action,complexDiagonal_action]
  apply upperPoint_congr
  · rw [inv_pow,cubeDilationRoot_sq]
    ring
  · have hn:‖cubeDilationRoot p‖^2=‖eisEmbedding p‖^3:=by
      rw [←norm_pow,cubeDilationRoot_sq,norm_pow]
    rw [Complex.normSq_eq_norm_sq,norm_inv,inv_pow,hn]
    ring

theorem cubeAverage_period_one (p:Eis) (hp:p≠0) (hprimary:lambda^2∣p-1)
    (F:HyperbolicSpace→ℂ)
    (hF:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (hF1:∀w:HyperbolicSpace,F (complexTranslation 1 • w)=F w)
    (w:HyperbolicSpace) :
    cubeAverage p hp F (complexTranslation 1 • w)=cubeAverage p hp F w := by
  have hd:(3:Eis)∣1-p^3:=by
    have hh:=(three_dvd_primary_sub_one p hprimary).trans (sub_one_dvd_pow_sub_one p 3)
    simpa only [neg_sub] using dvd_neg.mpr hh
  obtain ⟨t,ht⟩:=hd
  let a:(Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}):=
    { toFun:=fun r=>r+Ideal.Quotient.mk _ t
      invFun:=fun r=>r-Ideal.Quotient.mk _ t
      left_inv:=fun r=>add_sub_cancel_right r _
      right_inv:=fun r=>sub_add_cancel r _ }
  let f (r:Eis⧸Ideal.span {p^3}):=
    F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
        (complexTranslation 1 • w))=f (a r) := by
    rw [←mul_smul,cubeAverageMatrix_translate_one p hp _ t ht.symm,mul_smul,hF1]
    apply cubeAverage_summand_congr p hp F hF
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    rw [map_add,GaussianShiftedPartition.representative_spec,
      GaussianShiftedPartition.representative_spec]
    rfl
  unfold cubeAverage
  congr 1
  calc
    _ = ∑' r,f (a r):=tsum_congr hpoint
    _ = ∑' r,f r:=a.tsum_eq f

end CubicEisenstein
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def integralCoverMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    IntegralOrbitQuotient H→IntegralOrbitQuotient K :=
  Quotient.map' id (by
    rintro w u ⟨M,hM⟩
    exact ⟨Subgroup.inclusion hHK M,hM⟩)

lemma integralCoverMap_projection {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) (w : HyperbolicSpace) :
    integralCoverMap hHK (integralOrbitProjection H w)=integralOrbitProjection K w := rfl

lemma integralCoverMap_measurable {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    Measurable (integralCoverMap hHK) := by
  apply measurable_from_quotient.mpr
  exact measurable_integralOrbitProjection K

lemma integralCoverMap_continuous {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    Continuous (integralCoverMap hHK) := continuous_id.quotient_map' _

lemma integralCoverMap_surjective {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    Function.Surjective (integralCoverMap hHK) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact ⟨integralOrbitProjection H w,rfl⟩

abbrev IntegralCoverCosets (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) := K ⧸ H.subgroupOf K

def integralCoverRep (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) : K := q.out

def integralCoverSheet (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) : Set HyperbolicSpace :=
  (fun w=>integralCoverRep H K q • w) ⁻¹' hyperbolicFundamentalSet K

def integralCoverDomain (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) : Set HyperbolicSpace :=
  ⋃q : IntegralCoverCosets H K,integralCoverSheet H K q

lemma integralCoverSheet_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) :
    MeasurableSet (integralCoverSheet H K q) :=
  (measurable_const_smul (integralCoverRep H K q)) (hyperbolicFundamentalSet_measurable K)

lemma integralCoverDomain_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K] :
    MeasurableSet (integralCoverDomain H K) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  exact MeasurableSet.iUnion (integralCoverSheet_measurable H K)

lemma fundamental_reduction_unique (K : Subgroup (SL(2,ActualEisensteinCubic.O))) (hK : K≤CubicKubota.levelThree)
    (r s : K) (w : HyperbolicSpace) (hr : r•w∈hyperbolicFundamentalSet K)
    (hs : s•w∈hyperbolicFundamentalSet K) : r=s := by
  have he : s•w=r•w := by
    have hh := hyperbolicFundamentalSet_orbit_unique K (r•w) hr (s*r⁻¹)
      (by simpa only [mul_smul,inv_smul_smul] using hs)
    simpa only [mul_smul,inv_smul_smul] using hh
  have hfix : (r⁻¹*s)•w=w := by rw [mul_smul,he,inv_smul_smul]
  exact inv_mul_eq_one.mp (subgroup_action_free K hK _ w hfix)

lemma integralCoverSheet_pairwiseDisjoint (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hK : K≤CubicKubota.levelThree) : Pairwise (fun q r=>Disjoint (integralCoverSheet H K q) (integralCoverSheet H K r)) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro w hwq hwr
  have he := fundamental_reduction_unique K hK (integralCoverRep H K q)
    (integralCoverRep H K r) w hwq hwr
  apply hqr
  exact Quotient.out_injective he

lemma integralCoverRep_mul_projection {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (q : IntegralCoverCosets H K) (h : H) :
    ((integralCoverRep H K q*Subgroup.inclusion hHK h : K) : IntegralCoverCosets H K)=q := by
  rw [QuotientGroup.mk_mul_of_mem _ (show Subgroup.inclusion hHK h∈H.subgroupOf K from h.property)]
  exact QuotientGroup.out_eq' q

lemma integralCover_inclusion_smul {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (h : H) (w : HyperbolicSpace) :
    (Subgroup.inclusion hHK h)•w=h•w := rfl

private lemma mul_smul_mem_set_iff {G X : Type*} [Monoid G] [MulAction G X]
    (a b : G) (w v : X) (hv : v = b • w) (S : Set X) :
    a • v ∈ S ↔ (a * b) • w ∈ S := by
  rw [hv, mul_smul]

private lemma mem_integralCoverSheet (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    w ∈ integralCoverSheet H K q ↔
      integralCoverRep H K q • w ∈ hyperbolicFundamentalSet K := Iff.rfl

lemma integralCoverSheet_membership {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (q : IntegralCoverCosets H K) (h : H) (w : HyperbolicSpace) :
    h•w∈integralCoverSheet H K q ↔
      (integralCoverRep H K q*Subgroup.inclusion hHK h)•w∈hyperbolicFundamentalSet K := by
  exact (mem_integralCoverSheet H K q (h • w)).trans
    (mul_smul_mem_set_iff (integralCoverRep H K q) (Subgroup.inclusion hHK h)
      w (h • w) (integralCover_inclusion_smul hHK h w).symm (hyperbolicFundamentalSet K))

lemma integralCoverDomain_covers {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (w : HyperbolicSpace) :
    ∃h : H,h•w∈integralCoverDomain H K := by
  obtain ⟨k,hk⟩ := hyperbolicFundamentalSet_covers K w
  let q : IntegralCoverCosets H K := k
  let r := integralCoverRep H K q
  have hr : r⁻¹*k∈H.subgroupOf K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  let h : H := ⟨((r⁻¹*k:K):SL(2,ActualEisensteinCubic.O)),hr⟩
  have hin : Subgroup.inclusion hHK h=r⁻¹*k := rfl
  refine ⟨h,Set.mem_iUnion.mpr ⟨q,?_⟩⟩
  apply (integralCoverSheet_membership hHK q h w).mpr
  change (r*Subgroup.inclusion hHK h)•w∈hyperbolicFundamentalSet K
  rw [hin,mul_inv_cancel_left]
  exact hk

lemma integralCoverDomain_unique {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) (w : HyperbolicSpace)
    (h1 h2 : H) (hh1 : h1•w∈integralCoverDomain H K)
    (hh2 : h2•w∈integralCoverDomain H K) : h1=h2 := by
  obtain ⟨q1,hq1⟩ := Set.mem_iUnion.mp hh1
  obtain ⟨q2,hq2⟩ := Set.mem_iUnion.mp hh2
  have he : integralCoverRep H K q1*Subgroup.inclusion hHK h1=
      integralCoverRep H K q2*Subgroup.inclusion hHK h2 := by
    apply fundamental_reduction_unique K hK _ _ w
    · exact (integralCoverSheet_membership hHK q1 h1 w).mp hq1
    · exact (integralCoverSheet_membership hHK q2 h2 w).mp hq2
  have hqeq : q1=q2 := by
    have hproj := congrArg (fun k : K=>(k : IntegralCoverCosets H K)) he
    rw [integralCoverRep_mul_projection hHK q1 h1,
      integralCoverRep_mul_projection hHK q2 h2] at hproj
    exact hproj
  subst q2
  exact (Subgroup.inclusion_injective hHK) (mul_left_cancel he)

theorem integralCoverDomain_isFundamentalDomain {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IsFundamentalDomain H (integralCoverDomain H K) hyperbolicVolume := by
  apply IsFundamentalDomain.mk' (integralCoverDomain_measurable H K).nullMeasurableSet
  intro w
  obtain ⟨h,hh⟩ := integralCoverDomain_covers hHK w
  exact ⟨h,hh,fun g hg=>integralCoverDomain_unique hHK hK w g h hg hh⟩

end CubicEisenstein

end

end OAI
