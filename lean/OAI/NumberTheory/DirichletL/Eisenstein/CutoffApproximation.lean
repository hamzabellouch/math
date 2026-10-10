import OAI.NumberTheory.DirichletL.RowCompletion.ThetaNonvanishing

namespace OAI

noncomputable section

namespace CubicEisenstein

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

section BoundedConvergence
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] («μ» : Measure α)

omit [CompleteSpace E] in
lemma l2_norm_sq_integral (f : Lp E 2 «μ») : ‖f‖^2=∫a,‖f a‖^2∂«μ» := by
  calc
    ‖f‖^2=inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫a,inner ℝ (f a) (f a)∂«μ» := L2.inner_def _ _
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

omit [CompleteSpace E] in
lemma l2_toLp_sub_norm_sq (f g : α→E) (hf : MemLp f 2 «μ») (hg : MemLp g 2 «μ») :
    ‖hf.toLp f-hg.toLp g‖^2=∫a,‖f a-g a‖^2∂«μ» := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp] with a ha hf hg
  rw [ha]
  simp only [Pi.sub_apply,hf,hg]

omit [CompleteSpace E] in
theorem l2_tendsto_of_bounded_eventuallyEq [IsFiniteMeasure «μ»]
    (f : ℕ→α→E) (g : α→E) (hf : ∀n,MemLp (f n) 2 «μ») (hg : MemLp g 2 «μ»)
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hfB : ∀n a,‖f n a‖≤B) (hgC : ∀a,‖g a‖≤C)
    (hlim : ∀a,∀ᶠn : ℕ in atTop,f n a=g a) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hsq : Tendsto (fun n => ∫a,‖f n a-g a‖^2∂«μ») atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence («μ» := «μ»)
      (F := fun n a => ‖f n a-g a‖^2) (f := fun _ => (0:ℝ)) (fun _ => (B+C)^2)
      (fun n => ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2)
      (integrable_const _) ?_ ?_
    · simpa only [integral_zero] using h
    · intro n
      exact Eventually.of_forall (fun a => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hB hC)).mpr
        exact (norm_sub_le _ _).trans (add_le_add (hfB n a) (hgC a)))
    · exact Eventually.of_forall (fun a => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hlim a] with n hn
        simp only [hn,sub_self,norm_zero,zero_pow (by decide : 2≠0)])
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖^2) atTop (𝓝 0) := by
    simpa only [l2_toLp_sub_norm_sq] using hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hsqrt

end BoundedConvergence

instance kernelFundamentalVolume_finite : IsFiniteMeasure KernelFundamentalVolume := by
  refine ⟨?_⟩
  change (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)) Set.univ<⊤
  rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact hyperbolicFundamentalSet_volume_lt_top globalKubotaKernel globalKubotaKernel_le_levelThree

def kernelFunctionField (f : KernelQuotient→ℂ) (p : EuclideanSpatial) : ℂ :=
  f (kernelEuclideanProjection p)

lemma kernelFunctionField_smooth (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelFunctionField f) p :=
  (((hf.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

def kernelFunctionGradient (f : KernelQuotient→ℂ) (w : HyperbolicSpace) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j => (hyperbolicHeight w:ℂ)*
    fderiv ℝ (kernelFunctionField f) (hyperbolicEuclideanCoordinates w) (euclideanCoordinateVector j))

lemma kernelFunctionGradient_continuous (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    Continuous (kernelFunctionGradient f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  apply (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
  rw [continuous_iff_continuousAt]
  intro w
  exact (((kernelFunctionField_smooth f hf _ (hyperbolicHeight_pos w)).continuousAt_fderiv
    (by simp)).clm_apply continuousAt_const).comp hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma norm_three_vector_bound (v : EuclideanSpace ℂ (Fin 3)) (B : ℝ) (hB : 0≤B)
    (hv : ∀j,‖v j‖≤B) : ‖v‖≤3*B := by
  have hsq : ‖v‖^2≤3*B^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑j : Fin 3,B^2 := Finset.sum_le_sum (fun j hj =>
        (sq_le_sq₀ (norm_nonneg _) hB).mpr (hv j))
      _ = _ := by simp
  nlinarith [norm_nonneg v,sq_nonneg B]

lemma kernelFunctionGradient_bound (f : KernelQuotient→ℂ) (B : ℝ) (hB : 0≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤B)
    (w : HyperbolicSpace) : ‖kernelFunctionGradient f w‖≤3*B := by
  apply norm_three_vector_bound _ B hB
  intro j
  exact hgrad (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) j

lemma kernelFunctionGradient_memLp (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B : ℝ) (hB : 0≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤B) :
    MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume :=
  MemLp.of_bound (kernelFunctionGradient_continuous f hf).aestronglyMeasurable (3*B)
    (Eventually.of_forall (kernelFunctionGradient_bound f B hB hgrad))

def kernelFunctionCutoff (n : ℕ) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) : kernelSmoothTests := by
  refine ⟨fun q => (kernelExhaustionCutoff n q:ℂ)*f q,?_,?_⟩
  · have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1*z.2) := contDiff_fst.mul contDiff_snd
    exact hm.contMDiff.comp
      ((Complex.ofRealCLM.contDiff.contMDiff.comp (kernelExhaustionCutoff_smooth n)).prodMk_space hf)
  · apply HasCompactSupport.of_support_subset_isCompact (kernelExhaustionCutoff_hasCompactSupport n)
    intro q hq
    by_contra hn
    have hz : kernelExhaustionCutoff n q=0 := image_eq_zero_of_notMem_tsupport hn
    exact hq (by simp [hz])

lemma kernelFunctionCutoff_apply (n : ℕ) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) (q : KernelQuotient) :
    (kernelFunctionCutoff n f hf).1 q=(kernelExhaustionCutoff n q:ℂ)*f q := rfl

lemma kernelFunctionCutoff_field (n : ℕ) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    kernelTestField (kernelFunctionCutoff n f hf)=
      fun p => (kernelExhaustionCutoff n (kernelEuclideanProjection p):ℂ)*kernelFunctionField f p := rfl

lemma kernelFunctionGradient_of_test (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelFunctionGradient f.1 w=kernelGradientAt w f := by
  unfold kernelFunctionGradient
  simp only [euclideanCoordinateVector_eq_basis]
  rfl

lemma kernelFunctionCutoff_field_eventually (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ∀ᶠn : ℕ in atTop,kernelTestField (kernelFunctionCutoff n f hf)=ᶠ[𝓝 p]kernelFunctionField f := by
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [kernelExhaustionCutoff_eventually_one_near (kernelEuclideanProjection p)] with n hn
  filter_upwards [hn.comp_tendsto hc] with q hq
  change kernelExhaustionCutoff n (kernelEuclideanProjection q)=1 at hq
  change (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)*kernelFunctionField f q=kernelFunctionField f q
  rw [hq]
  simp

lemma kernelFunctionCutoff_gradient_eventually (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) (w : HyperbolicSpace) :
    ∀ᶠn : ℕ in atTop,kernelGradientAt w (kernelFunctionCutoff n f hf)=kernelFunctionGradient f w := by
  filter_upwards [kernelFunctionCutoff_field_eventually f hf
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)] with n hn
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  change (hyperbolicHeight w:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf)) _ _=
    (hyperbolicHeight w:ℂ)*fderiv ℝ (kernelFunctionField f) _ _
  rw [hn.fderiv_eq,euclideanCoordinateVector_eq_basis]

lemma kernelFunctionCutoff_mass_bound (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B : ℝ) (_hB : 0≤B) (hbound : ∀q,‖f q‖≤B) (n : ℕ) (q : KernelQuotient) :
    ‖(kernelFunctionCutoff n f hf).1 q‖≤B := by
  rw [kernelFunctionCutoff_apply,norm_mul,Complex.norm_of_nonneg (kernelExhaustionCutoff_bounds n q).1]
  exact (mul_le_mul (kernelExhaustionCutoff_bounds n q).2 (hbound q) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)

lemma kernelFunctionCutoff_scaled_deriv_bound (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B G D : ℝ) (hB : 0≤B) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (hcut : ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤D)
    (n : ℕ) (p : EuclideanSpatial) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf)) p (euclideanCoordinateVector j)‖≤G+B*D := by
  let c : EuclideanSpatial→ℂ:=fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)
  have hc : DifferentiableAt ℝ c p :=
    (kernelFunctionField_smooth (fun q => (kernelExhaustionCutoff n q:ℂ))
      (Complex.ofRealCLM.contDiff.contMDiff.comp (kernelExhaustionCutoff_smooth n)) p hp).differentiableAt (by simp)
  have hd := (kernelFunctionField_smooth f hf p hp).differentiableAt (by simp)
  rw [kernelFunctionCutoff_field,fderiv_fun_mul hc hd]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  have he : (p 2:ℂ)*(c p*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)+
      kernelFunctionField f p*fderiv ℝ c p (euclideanCoordinateVector j))=
      c p*((p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j))+
        kernelFunctionField f p*((p 2:ℂ)*fderiv ℝ c p (euclideanCoordinateVector j)) := by ring
  change ‖(p 2:ℂ)*(c p*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)+
      kernelFunctionField f p*fderiv ℝ c p (euclideanCoordinateVector j))‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  have hc1 : ‖c p‖≤1 := by
    rw [Complex.norm_of_nonneg (kernelExhaustionCutoff_bounds n _).1]
    exact (kernelExhaustionCutoff_bounds n _).2
  have hleft : ‖c p‖*‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G :=
    (mul_le_mul hc1 (hgrad p hp j) (norm_nonneg _) zero_le_one).trans_eq (one_mul G)
  have hright : ‖kernelFunctionField f p‖*‖(p 2:ℂ)*fderiv ℝ c p (euclideanCoordinateVector j)‖≤B*D :=
    mul_le_mul (hfB (kernelEuclideanProjection p)) (hcut n p hp j) (norm_nonneg _) hB
  simpa only [norm_mul] using add_le_add hleft hright

lemma kernelFunctionCutoff_gradient_bound (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    ∃D : ℝ,0≤D ∧ ∀n : ℕ,∀w : HyperbolicSpace,‖kernelGradientAt w (kernelFunctionCutoff n f hf)‖≤D := by
  obtain ⟨D,hD,hcut⟩ := kernelExhaustionCutoff_scaled_fderiv_bound
  refine ⟨3*(G+B*D),by positivity,?_⟩
  intro n w
  apply norm_three_vector_bound _ (G+B*D) (by positivity)
  intro j
  change ‖(hyperbolicHeight w:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf))
    (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)‖≤_
  rw [←euclideanCoordinateVector_eq_basis]
  exact kernelFunctionCutoff_scaled_deriv_bound f hf B G D hB hfB hgrad hcut n
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) j

theorem kernelFunctionCutoff_mass_tendsto (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (B : ℝ) (hB : 0≤B) (hbound : ∀q,‖f q‖≤B) :
    Tendsto (fun n => kernelSmoothTestsToL2 (kernelFunctionCutoff n f hf)) atTop (𝓝 (hfL.toLp f)) := by
  apply l2_tendsto_of_bounded_eventuallyEq (integralQuotientVolume globalKubotaKernel)
    (fun n => (kernelFunctionCutoff n f hf).1) f
    (fun n => kernelSmoothTests_memLp (kernelFunctionCutoff n f hf)) hfL B B hB hB
    (kernelFunctionCutoff_mass_bound f hf B hB hbound) hbound
  intro q
  filter_upwards [kernelExhaustionCutoff_eventually_one q] with n hn
  rw [kernelFunctionCutoff_apply,hn]
  simp

theorem kernelFunctionCutoff_gradient_tendsto (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    Tendsto (fun n => kernelGradientToL2 (kernelFunctionCutoff n f hf)) atTop
      (𝓝 (hgL.toLp (kernelFunctionGradient f))) := by
  obtain ⟨D,hD,hbound⟩ := kernelFunctionCutoff_gradient_bound f hf B G hB hG hfB hgrad
  apply l2_tendsto_of_bounded_eventuallyEq KernelFundamentalVolume
    (fun n w => kernelGradientAt w (kernelFunctionCutoff n f hf)) (kernelFunctionGradient f)
    (fun n => kernelGradientAt_memLp (kernelFunctionCutoff n f hf)) hgL D (3*G) hD (by positivity)
    hbound (kernelFunctionGradient_bound f G hG hgrad)
  exact kernelFunctionCutoff_gradient_eventually f hf

theorem kernel_bounded_smooth_energy_exists (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    ∃u : KernelEnergyGraph,kernelEnergyMass u=hfL.toLp f ∧
      kernelEnergyGradient u=hgL.toLp (kernelFunctionGradient f) := by
  let x : KernelEnergyAmbient:=WithLp.toLp 2 (hfL.toLp f,hgL.toLp (kernelFunctionGradient f))
  have hm := kernelFunctionCutoff_mass_tendsto f hf hfL B hB hfB
  have hg := kernelFunctionCutoff_gradient_tendsto f hf hgL B G hB hG hfB hgrad
  have hp := hm.prodMk_nhds hg
  have ht : Tendsto (fun n => kernelEnergyCore (kernelFunctionCutoff n f hf)) atTop (𝓝 x) := by
    have h := (WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).symm.continuous.continuousAt.tendsto.comp hp
    exact h
  have hx : x∈kernelEnergyGraphSubmodule := by
    change x∈closure (Set.range kernelEnergyCore)
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun n => ⟨kernelFunctionCutoff n f hf,rfl⟩))
  exact ⟨⟨x,hx⟩,rfl,rfl⟩

def kernelEisensteinRemainderL2 (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) : KernelQuotientL2 :=
  (kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs).toLp
    (kernelEisensteinRemainder a b s (by linarith))

lemma kernelEisensteinRemainderL2_ae (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    kernelEisensteinRemainderL2 a b ha hab s hs=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelEisensteinRemainder a b s (by linarith) :=
  (kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs).coeFn_toLp

theorem kernelEisensteinRemainder_energy (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃u : KernelEnergyGraph,kernelEnergyMass u=kernelEisensteinRemainderL2 a b ha hab s hs := by
  let f := kernelEisensteinRemainder a b s (by linarith)
  have hf := kernelEisensteinRemainder_smooth a b ha hab s (by linarith)
  have hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel) :=
    kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs
  have hfB : ∀q,‖f q‖≤eisensteinRemainderBound b s := by
    intro q
    induction q using Quotient.inductionOn with
    | _ w => exact eisenstein_sub_seed_bounded a b ha.le hab s hs w
  obtain ⟨G,hG,hgrad⟩ := kernelEisensteinRemainder_scaled_fderiv_bound a b ha hab s hs
  have hgrad' : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G := hgrad
  have hgL := kernelFunctionGradient_memLp f hf G hG hgrad'
  obtain ⟨u,hu,hgu⟩ := kernel_bounded_smooth_energy_exists f hf hfL hgL
    (eisensteinRemainderBound b s) G (eisensteinRemainderBound_nonneg b s) hG hfB hgrad'
  exact ⟨u,hu⟩

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold Matrix

lemma axis_update_contDiff (p : SpatialCoordinates) (j : Fin 3) :
    ContDiff ℝ ∞ (fun t => Function.update p j t) := by
  apply contDiff_pi.mpr
  intro k
  by_cases h : k=j
  · subst k
    simpa only [Function.update_self,id_eq] using! (contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => t))
  · simpa only [Function.update_of_ne h] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => p k))

lemma smooth_positive_axis_regular (f : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice f p j) (p j) ∧
      DifferentiableAt ℝ (deriv (axisSlice f p j)) (p j) := by
  have hh : ContDiffAt ℝ ∞ (axisSlice f p j) (p j) := by
    have hfp : ContDiffAt ℝ ∞ f (Function.update p j (p j)) := by
      simpa only [Function.update_eq_self] using hf p hp
    have h := hfp.comp (p j) (axis_update_contDiff p j).contDiffAt
    simpa only [axisSlice,Function.comp_def,Function.update_eq_self] using! h
  exact ⟨hh.differentiableAt (by simp),(hh.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma axisLaplacian_sub_smooth (f g : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (hg : ∀p,0<p 2→ContDiffAt ℝ ∞ g p)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => f q-g q) p=axisLaplacian f p-axisLaplacian g p := by
  let F : Fin 2→SpatialCoordinates→ℂ:=![f,fun q => (-1:ℂ)*g q]
  have hF : ∀i : Fin 2,∀q,0<q 2→ContDiffAt ℝ ∞ (F i) q := by
    intro i q hq
    fin_cases i
    · exact hf q hq
    · exact contDiffAt_const.mul (hg q hq)
  have hh := axisLaplacian_finset_sum Finset.univ F
    (fun i hi q hq j => smooth_positive_axis_regular (F i) (hF i) q hq j) p hp
  have he : (fun q => ∑i : Fin 2,F i q)=(fun q => f q-g q) := by
    funext q
    simp [F,Fin.sum_univ_two,sub_eq_add_neg]
  rw [he] at hh
  simp only [Fin.sum_univ_two,F,Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  rw [axisLaplacian_const_mul] at hh
  simpa only [neg_one_mul,sub_eq_add_neg] using hh

lemma eisensteinRemainder_coordinate_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (eisensteinRemainderField a b s) p=
      smoothCuspSeedDefectField a b s p+s*(2-s)*eisensteinRemainderField a b s p := by
  have hD := actual_smoothCuspSeed_laplace_defect a b s ha hab p hp
  unfold eisensteinRemainderField
  rw [axisLaplacian_sub_smooth _ _ (smoothEisenstein_contDiffAt s hs)
    (actual_smoothCuspSeed_contDiffAt a b s ha hab) p hp,smoothEisenstein_eigenfunction s hs p hp]
  linear_combination hD

lemma kernelQuotientDefect_euclidean_eq (a b : ℝ) (s : ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelQuotientDefect a b s (kernelEuclideanProjection p)=smoothCuspSeedDefectField a b s p.ofLp := by
  unfold kernelEuclideanProjection
  simp only [Function.comp_apply]
  rw [euclideanToHyperbolic_positive p hp]
  change smoothCuspSeedDefect a b s _=smoothCuspSeedDefectField a b s p.ofLp
  rw [smoothCuspSeedDefectField,dite_eq_left hp]
  simp only [mul_comm Complex.I]

theorem kernelEisensteinRemainder_operator_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian (kernelFunctionField (kernelEisensteinRemainder a b s hs)) p=
      kernelQuotientDefect a b s (kernelEuclideanProjection p)+
        kernelEisensteinSpectralParameter s*kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p) := by
  let f := kernelFunctionField (kernelEisensteinRemainder a b s hs)
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s hs
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s hs (WithLp.toLp 2 q) hq
  rw [positiveEuclideanLaplacian_eq_axis f hf p hp,
    axisLaplacian_congr_positive _ _ he p.ofLp hp,
    eisensteinRemainder_coordinate_equation a b ha hab s hs p.ofLp hp,
    kernelQuotientDefect_euclidean_eq a b s p hp,kernelEisensteinRemainder_euclidean_eq a b s hs p hp]
  rfl

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernelFunctionCutoff_uniform_near (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃N : ℕ,∀n≥N,∀p : EuclideanSpatial,0<p 2→kernelEuclideanProjection p∈K→
      kernelTestField (kernelFunctionCutoff n f hf)=ᶠ[𝓝 p]kernelFunctionField f := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image
    (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousOn
  obtain ⟨N,hN⟩ := exists_nat_gt C
  refine ⟨N,?_⟩
  intro n hn p hp hpK
  have hheight : kernelQuotientBarrier 2 3 (kernelEuclideanProjection p)<(n:ℝ)+1 := by
    have hh := hC ⟨kernelEuclideanProjection p,hpK,rfl⟩
    have hcast : (N:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hnear := (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousAt.eventually_lt_const hheight
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [hc hnear] with q hq
  change (kernelExhaustionProfile n (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)):ℂ)*
    kernelFunctionField f q=kernelFunctionField f q
  rw [kernelExhaustionProfile_one n _ hq.le]
  simp

lemma kernelBoundedFunction_form_equation (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p))
    (g : kernelSmoothTests) :
    inner ℂ (hgL.toLp (kernelFunctionGradient f)) (kernelGradientToL2 g)=
      inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g) := by
  obtain ⟨N,hN⟩ := kernelFunctionCutoff_uniform_near f hf (tsupport g.1) g.2.2
  have hconstant : ∀ᶠn : ℕ in atTop,
      inner ℂ (kernelGradientToL2 (kernelFunctionCutoff n f hf)) (kernelGradientToL2 g)=
        inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [kernelGradientToL2_inner,kernelL2_inner_toLp_smooth]
    apply kernelDirichletForm_supported_equation (kernelFunctionCutoff n f hf) g A hA
    intro p hp hpg
    change positiveEuclideanLaplacian (kernelTestField (kernelFunctionCutoff n f hf)) p=A (kernelEuclideanProjection p)
    rw [positiveEuclideanLaplacian_congr _ _ p (hN n hn p hp hpg)]
    exact hEq p hp
  have hlim : Tendsto (fun n => inner ℂ (kernelGradientToL2 (kernelFunctionCutoff n f hf))
      (kernelGradientToL2 g)) atTop (𝓝 (inner ℂ (hgL.toLp (kernelFunctionGradient f)) (kernelGradientToL2 g))) :=
    (kernelFunctionCutoff_gradient_tendsto f hf hgL B G hB hG hfB hgrad).inner
      (tendsto_const_nhds (x := kernelGradientToL2 g))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconstant.mono (fun n hn => hn.symm)))

theorem kernel_bounded_smooth_operator_graph (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p)) :
    (hfL.toLp f,hA.toLp A)∈kernelEnergyLaplacian.graph := by
  have hgL := kernelFunctionGradient_memLp f hf G hG hgrad
  obtain ⟨u,hum,hug⟩ := kernel_bounded_smooth_energy_exists f hf hfL hgL B G hB hG hfB hgrad
  have hform (v : KernelEnergyGraph) :
      inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ (hA.toLp A) (kernelEnergyMass v) := by
    exact kernelEnergyGraphCore_dense.induction_on v
      (isClosed_eq (by fun_prop : Continuous (fun v : KernelEnergyGraph =>
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)))
        (by fun_prop : Continuous (fun v : KernelEnergyGraph => inner ℂ (hA.toLp A) (kernelEnergyMass v))))
      (fun g => by
        rw [hug,kernelEnergyGradient_core,kernelEnergyMass_core]
        exact kernelBoundedFunction_form_equation f hf hgL B G hB hG hfB hgrad A hA hEq g)
  have hu : u=kernelVariationalSolution (hfL.toLp f+hA.toLp A) := by
    apply kernelVariationalSolution_unique
    intro v
    rw [hum,hform v,inner_add_left]
  have hm := congrArg kernelEnergyMass hu
  rw [hum] at hm
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  exact hm.symm

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

theorem kernelEisensteinRemainderL2_graph (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    (kernelEisensteinRemainderL2 a b ha hab s hs,
      kernelL2Defect a b (by linarith) hab s+kernelEisensteinSpectralParameter s •
        kernelEisensteinRemainderL2 a b ha hab s hs)∈kernelEnergyLaplacian.graph := by
  let f := kernelEisensteinRemainder a b s (by linarith)
  have hf := kernelEisensteinRemainder_smooth a b ha hab s (by linarith)
  have hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel) :=
    kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs
  have hfB : ∀q,‖f q‖≤eisensteinRemainderBound b s := by
    intro q
    induction q using Quotient.inductionOn with
    | _ w => exact eisenstein_sub_seed_bounded a b ha.le hab s hs w
  obtain ⟨G,hG,hgrad⟩ := kernelEisensteinRemainder_scaled_fderiv_bound a b ha hab s hs
  let A : KernelQuotient→ℂ := fun q => kernelQuotientDefect a b s q+
    kernelEisensteinSpectralParameter s*f q
  have hD := kernelQuotientDefect_memLp a b s (by linarith) hab
  have hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel) :=
    hD.add (hfL.const_smul (kernelEisensteinSpectralParameter s))
  have hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p) := by
    intro p hp
    exact kernelEisensteinRemainder_operator_equation a b ha hab s (by linarith) p hp
  have hgraph := kernel_bounded_smooth_operator_graph f hf hfL
    (eisensteinRemainderBound b s) G (eisensteinRemainderBound_nonneg b s) hG hfB hgrad A hA hEq
  have hAL : hA.toLp A=kernelL2Defect a b (by linarith) hab s+
      kernelEisensteinSpectralParameter s • kernelEisensteinRemainderL2 a b ha hab s hs := by
    exact (hD.toLp_add (hfL.const_smul (kernelEisensteinSpectralParameter s))).trans
      (congrArg (fun x => hD.toLp (kernelQuotientDefect a b s)+x)
        (hfL.toLp_const_smul (kernelEisensteinSpectralParameter s)))
  rw [hAL] at hgraph
  exact hgraph

theorem kernelEisensteinL2Correction_eq_remainder (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelEisensteinL2Correction a b (by linarith) hab s=
      kernelEisensteinRemainderL2 a b ha hab s hs := by
  exact kernelEisensteinL2Correction_unique a b (by linarith) hab s
    (kernelSpectralFormOperator_isUnit_nonreal _
      (kernelEisensteinSpectralParameter_nonreal s (by linarith) (by linarith)))
    _ (kernelEisensteinRemainderL2_graph a b ha hab s hs)

theorem kernelEisensteinL2Correction_initial_overlap (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelEisensteinL2Correction a b (by linarith) hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q := by
  rw [kernelEisensteinL2Correction_eq_remainder a b ha hab s hs hi]
  exact kernelEisensteinRemainderL2_ae a b ha hab s hs

end CubicEisenstein

end

end OAI
