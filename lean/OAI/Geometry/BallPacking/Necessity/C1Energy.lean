import Mathlib
import OAI.Geometry.BallPacking.Necessity.AffineEnergy

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory ContinuousLinearMap
namespace TwoPointContinuation

variable {G E : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 def approxBump (j : ℕ) : ContDiffBump (0:G) :=
  ⟨(1/((j:ℝ)+1))/2,1/((j:ℝ)+1),by positivity,by apply half_lt_self; positivity⟩

 omit [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] in
 theorem approxBump_shrinks : Tendsto (fun j : ℕ => (approxBump (G:=G) j).rOut) atTop (𝓝 0) := by
  simp only [approxBump,one_div]
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

 def mollify (μ : Measure G) (j : ℕ) (f : G → E) : G → E :=
  (approxBump j).normed μ ⋆[lsmul ℝ ℝ,μ] f

 theorem mollify_tendsto (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : Continuous f) (x : G) : Tendsto (fun j => mollify μ j f x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous approxBump_shrinks hf x

 omit [CompleteSpace E] in
 theorem mollify_smooth (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : Continuous f) (j : ℕ) : ContDiff ℝ ∞ (mollify μ j f) := by
  exact (approxBump (G:=G) j).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (approxBump j).contDiff_normed hf.locallyIntegrable

 omit [CompleteSpace E] in
 theorem mollify_fderiv (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (j : ℕ) (x : G) :
    fderiv ℝ (mollify μ j f) x=mollify μ j (fderiv ℝ f) x := by
  have h := hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
    (μ:=μ) ((approxBump (G:=G) j).continuous_normed (μ:=μ)).locallyIntegrable hf x
  unfold mollify
  rw [h.fderiv]
  rfl

 theorem mollify_fderiv_tendsto (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (x : G) :
    Tendsto (fun j => fderiv ℝ (mollify μ j f) x) atTop (𝓝 (fderiv ℝ f x)) := by
  simp_rw [mollify_fderiv μ hf hc]
  exact mollify_tendsto μ (hf.continuous_fderiv one_ne_zero) x

 theorem mollify_norm_le (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖≤M) (j : ℕ) (x : G) :
    ‖mollify μ j f x‖≤3*M := by
  have h := (approxBump (G:=G) j).dist_normed_convolution_le
    (μ:=μ) hf.aestronglyMeasurable (x₀:=x) (ε:=2*M) (fun y _ => by
      exact (dist_le_norm_add_norm _ _).trans (by linarith [hM y,hM x]))
  change dist (mollify μ j f x) (f x)≤2*M at h
  calc
    ‖mollify μ j f x‖ ≤ ‖mollify μ j f x-f x‖+‖f x‖ := by
      simpa using norm_add_le (mollify μ j f x-f x) (f x)
    _ ≤ 3*M := by rw [dist_eq_norm] at h; linarith [hM x]

end TwoPointContinuation

 

 

open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory ContinuousLinearMap
namespace TwoPointContinuation
variable {G E : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

 theorem mollify_jet_integral_tendsto (μ : Measure G) [μ.IsAddHaarMeasure]
    {f : G → E} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (A : G × (E × (G →L[ℝ] E)) → ℝ) (hA : Continuous A)
    (K : Set G) (hK : IsCompact K) (hzero : ∀ z, z ∉ K → ∀ v, A (z,v)=0) :
    Tendsto (fun j => ∫ z, A (z,(mollify μ j f z,fderiv ℝ (mollify μ j f) z)) ∂μ)
      atTop (𝓝 (∫ z, A (z,(f z,fderiv ℝ f z)) ∂μ)) := by
  classical
  obtain ⟨M,hM⟩ := (hc.isCompact_range hf.continuous).isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := ((hc.fderiv ℝ).isCompact_range
    (hf.continuous_fderiv one_ne_zero)).isBounded.exists_norm_le
  have hmb (z : G) : ‖f z‖ ≤ M := hM _ (mem_range_self z)
  have hnb (z : G) : ‖fderiv ℝ f z‖ ≤ N := hN _ (mem_range_self z)
  let L := K ×ˢ (Metric.closedBall (0:E) (3*M) ×ˢ Metric.closedBall (0:G →L[ℝ] E) (3*N))
  have hL : IsCompact L := hK.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  obtain ⟨B,hB⟩ := (hL.image hA).isBounded.exists_norm_le
  have hb (j : ℕ) (z : G) (hz : z ∈ K) :
      ‖A (z,(mollify μ j f z,fderiv ℝ (mollify μ j f) z))‖≤B := by
    apply hB _ (mem_image_of_mem A ?_)
    refine ⟨hz,?_,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using mollify_norm_le μ hf.continuous hmb j z
    · rw [mollify_fderiv μ hf hc]
      simpa only [Metric.mem_closedBall,dist_zero_right] using
        mollify_norm_le μ (hf.continuous_fderiv one_ne_zero) hnb j z
  apply tendsto_integral_of_dominated_convergence (K.indicator (fun _ => B))
  · intro j
    exact (hA.comp (continuous_id.prodMk ((mollify_smooth μ hf.continuous j).continuous.prodMk
      ((mollify_smooth μ hf.continuous j).continuous_fderiv (by simp))))).aestronglyMeasurable
  · rw [integrable_indicator_iff hK.measurableSet]
    exact (integrableOn_const (C:=B) hK.measure_lt_top.ne)
  · intro j
    apply Eventually.of_forall
    intro z
    by_cases hz : z ∈ K
    · simpa only [indicator_of_mem hz] using hb j z hz
    · simp only [hzero z hz,indicator_of_notMem hz,norm_zero,le_refl]
  · apply Eventually.of_forall
    intro z
    exact (hA.tendsto _).comp (tendsto_const_nhds.prodMk_nhds
      ((mollify_tendsto μ hf.continuous z).prodMk_nhds (mollify_fderiv_tendsto μ hf hc z)))

end TwoPointContinuation

 

 

 

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open TwoPointContinuation

 def c1Area {n : ℕ} (u : Plane → Phase n) (z : Plane) : ℝ :=
  standardForm (fderiv ℝ u z (1,0)) (fderiv ℝ u z (0,1))

 theorem c1Area_continuous {n : ℕ} {u : Plane → Phase n} (hu : ContDiff ℝ 1 u) :
    Continuous (c1Area u) := by
  unfold c1Area
  simp only [← stdOmega_apply]
  exact ((stdOmega n).continuous.comp ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const)).clm_apply
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const)

 theorem c1_standard_stokes_compact {n : ℕ} {u : Plane → Phase n}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    (∫ z,cutoffWedge χ (planarPullback u stdPrimitive) z)= -(∫ z,χ z*c1Area u z) := by
  let A : Plane × (Phase n × (Plane →L[ℝ] Phase n)) → ℝ :=
    fun y => χ y.1*standardForm (y.2.2 (1,0)) (y.2.2 (0,1))
  let B : Plane × (Phase n × (Plane →L[ℝ] Phase n)) → ℝ :=
    fun y => fderiv ℝ χ y.1 (1,0)*stdPrimitive y.2.1 (y.2.2 (0,1))-
      fderiv ℝ χ y.1 (0,1)*stdPrimitive y.2.1 (y.2.2 (1,0))
  have hA : Continuous A := by
    simp only [A,← stdOmega_apply]
    fun_prop
  have hP : Continuous (fun y : Plane × (Phase n × (Plane →L[ℝ] Phase n)) =>
      stdPrimitive y.2.1) := (stdPrimitive_smooth n).continuous.comp continuous_snd.fst
  have hB : Continuous B := by
    have hd := hχ.continuous_fderiv (show (∞ : WithTop ℕ∞)≠0 by simp)
    exact (((hd.comp continuous_fst).clm_apply continuous_const).mul
      (hP.clm_apply (continuous_snd.snd.clm_apply continuous_const))).sub
      (((hd.comp continuous_fst).clm_apply continuous_const).mul
      (hP.clm_apply (continuous_snd.snd.clm_apply continuous_const)))
  let K := tsupport χ ∪ tsupport (fderiv ℝ χ)
  have hK : IsCompact K := hχc.union (hχc.fderiv ℝ)
  have hAz : ∀ z, z ∉ K → ∀ v, A (z,v)=0 := by
    intro z hz v
    have hz' : z ∉ tsupport χ := fun h => hz (Or.inl h)
    simp only [A,image_eq_zero_of_notMem_tsupport hz',zero_mul]
  have hBz : ∀ z, z ∉ K → ∀ v, B (z,v)=0 := by
    intro z hz v
    have hz' : z ∉ tsupport (fderiv ℝ χ) := fun h => hz (Or.inr h)
    simp only [B,image_eq_zero_of_notMem_tsupport hz',zero_apply,zero_mul,sub_self]
  have ha := mollify_jet_integral_tendsto volume hu hc A hA K hK hAz
  have hb := mollify_jet_integral_tendsto volume hu hc B hB K hK hBz
  have he (j : ℕ) :
      (∫ z,A (z,(mollify volume j u z,fderiv ℝ (mollify volume j u) z)))=
      -(∫ z,B (z,(mollify volume j u z,fderiv ℝ (mollify volume j u) z))) := by
    have h := integral_cutoffWedge hχ hχc
      (planarPullback_smooth (mollify_smooth volume hu.continuous j) (stdPrimitive_smooth n))
    have he (z : Plane) : planarCurl (planarPullback (mollify volume j u) stdPrimitive) z=
        standardForm (fderiv ℝ (mollify volume j u) z (1,0)) (fderiv ℝ (mollify volume j u) z (0,1)) := by
      rw [planarPullback_curl (mollify_smooth volume hu.continuous j) (stdPrimitive_smooth n)]
      exact stdPrimitive_extDeriv _ _ _
    simp_rw [he] at h
    change (∫ z,B (z,(mollify volume j u z,fderiv ℝ (mollify volume j u) z)))=
      -(∫ z,A (z,(mollify volume j u z,fderiv ℝ (mollify volume j u) z))) at h
    linarith
  have ht := tendsto_nhds_unique ha (hb.neg.congr (fun j => (he j).symm))
  change (∫ z,χ z*c1Area u z)= -(∫ z,cutoffWedge χ (planarPullback u stdPrimitive) z) at ht
  linarith

 theorem c1_local_compact {n : ℕ} {u : Plane → Phase n}
    (hu : ContDiff ℝ 1 u) {K : Set Plane} (hK : IsCompact K) :
    ∃ v : Plane → Phase n, ContDiff ℝ 1 v ∧ HasCompactSupport v ∧
      ∀ z ∈ K, v =ᶠ[𝓝 z] u := by
  obtain ⟨R,hR,hRb⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0:Plane) := ⟨R+1,R+2,by linarith,by linarith⟩
  refine ⟨fun z => b z • u z,b.contDiff.smul hu,b.hasCompactSupport.smul_right,?_⟩
  intro z hz
  have hm : z ∈ Metric.ball (0:Plane) b.rIn := by
    simp only [Metric.mem_ball,dist_zero_right]
    change ‖z‖<R+1
    linarith [hRb z hz]
  filter_upwards [b.eventuallyEq_one_of_mem_ball hm] with y hy
  simp only [hy,Pi.one_apply,one_smul]

 theorem c1_standard_stokes {n : ℕ} {u : Plane → Phase n}
    (hu : ContDiff ℝ 1 u) {χ : Plane → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    (∫ z,cutoffWedge χ (planarPullback u stdPrimitive) z)= -(∫ z,χ z*c1Area u z) := by
  let K := tsupport χ ∪ tsupport (fderiv ℝ χ)
  have hK : IsCompact K := hχc.union (hχc.fderiv ℝ)
  obtain ⟨v,hv,hvc,hvu⟩ := c1_local_compact hu hK
  have heA : (fun z => χ z*c1Area v z)=fun z => χ z*c1Area u z := by
    funext z
    by_cases hz : z ∈ K
    · simp only [c1Area,(hvu z hz).fderiv_eq]
    · have hz' : z ∉ tsupport χ := fun h => hz (Or.inl h)
      simp only [image_eq_zero_of_notMem_tsupport hz',zero_mul]
  have heB : cutoffWedge χ (planarPullback v stdPrimitive)=cutoffWedge χ (planarPullback u stdPrimitive) := by
    funext z
    by_cases hz : z ∈ K
    · simp only [cutoffWedge,planarPullback,(hvu z hz).self_of_nhds,(hvu z hz).fderiv_eq]
    · have hz' : z ∉ tsupport (fderiv ℝ χ) := fun h => hz (Or.inr h)
      simp only [cutoffWedge,image_eq_zero_of_notMem_tsupport hz',zero_apply,
        zero_mul,sub_self]
  have h := c1_standard_stokes_compact hv hvc hχ hχc
  rwa [heA,heB] at h

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem continuous_boundary_bounds {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : Continuous β) {A k ε : ℝ} (hA : 0 < A)
    (he : ∀ z : Plane, A ≤ radiusSq z → |β z (planeRotation z) - k| ≤ ε) :
    2 * Real.pi * (k-ε) ≤ (- ∫ z : Plane, 2 * deriv (outerProfile A) (radiusSq z) * β z (planeRotation z)) ∧
      (- ∫ z : Plane, 2 * deriv (outerProfile A) (radiusSq z) * β z (planeRotation z)) ≤ 2 * Real.pi * (k+ε) := by
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hgc : HasCompactSupport g := outerProfile_compact hA
  have hdi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z)) :=
    (((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv)).const_mul 2
  have hwi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z) * β z (planeRotation z)) := by
    exact ((((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).const_mul 2).mul
      (hβ.clm_apply (continuous_snd.neg.prodMk continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv).mul_left.mul_right
  have hp (z : Plane) :
      2 * deriv g (radiusSq z) * (k+ε) ≤ 2 * deriv g (radiusSq z) * β z (planeRotation z) ∧
      2 * deriv g (radiusSq z) * β z (planeRotation z) ≤ 2 * deriv g (radiusSq z) * (k-ε) := by
    by_cases hd : deriv g (radiusSq z) = 0
    · simp only [hd, mul_zero, zero_mul, le_refl, and_self]
    have hz : A ≤ radiusSq z := by
      by_contra! hn
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) hn)
    have hb := abs_le.mp (he z hz)
    have hdn : 2 * deriv g (radiusSq z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num)
        (outerProfile_deriv_nonpos hA (radiusSq_nonneg z))
    exact ⟨mul_le_mul_of_nonpos_left (by linarith [hb.2]) hdn,
      mul_le_mul_of_nonpos_left (by linarith [hb.1]) hdn⟩
  have hlo := integral_mono (hdi.mul_const (k+ε)) hwi (fun z => (hp z).1)
  have hhi := integral_mono hwi (hdi.mul_const (k-ε)) (fun z => (hp z).2)
  have hg0 : g 0 = 1 := outerProfile_zero_value hA
  rw [integral_mul_const, integral_radial_derivative hg hgc, hg0] at hlo hhi
  change _ ≤ - ∫ z : Plane, 2 * deriv g (radiusSq z) * β z (planeRotation z) ∧ _
  constructor <;> nlinarith

theorem continuous_boundary_limit {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : Continuous β) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    Tendsto (fun A : ℝ => - ∫ z : Plane, 2 * deriv (outerProfile A) (radiusSq z) * β z (planeRotation z)) atTop (𝓝 (2 * Real.pi * k)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (4 * Real.pi)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : 2 * Real.pi * δ = ε / 2 := by
    dsimp [δ]
    field_simp
    ring
  have he : ∀ᶠ z in cocompact Plane, |β z (planeRotation z) - k| ≤ δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hlim) δ hδ] with z hz
    exact (Real.dist_eq _ _ ▸ hz).le
  obtain ⟨K,hK,hKs⟩ := mem_cocompact.mp he
  obtain ⟨B,hB,hbound⟩ := (hK.image radiusSq_smooth.continuous).isBounded.exists_pos_norm_le
  filter_upwards [eventually_ge_atTop (B+1)] with A hA
  have hApos : 0 < A := by linarith
  have hb := continuous_boundary_bounds hβ hApos (k := k) (ε := δ) (by
    intro z hz
    apply hKs
    intro hzK
    have hx := hbound (radiusSq z) ⟨z,hzK,rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (radiusSq_nonneg z)] at hx
    linarith)
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith [hb.1, hb.2]

 theorem c1_pullback_continuous {n : ℕ} {u : Plane → Phase n} (hu : ContDiff ℝ 1 u) :
    Continuous (planarPullback u stdPrimitive) :=
  ((stdPrimitive_smooth n).continuous.comp hu.continuous).clm_comp
    (hu.continuous_fderiv one_ne_zero)

 theorem c1_area_of_nonneg_of_angular_limit {n : ℕ} {u : Plane → Phase n}
    (hu : ContDiff ℝ 1 u) (hp : ∀ z, 0≤c1Area u z)
    (hl : Tendsto (fun z => planarPullback u stdPrimitive z (planeRotation z))
      (cocompact Plane) (𝓝 0)) :
    Integrable (c1Area u) ∧ (∫ z,c1Area u z)=0 := by
  apply integrable_of_nonneg_of_outerCutoff_limit (c1Area_continuous hu) hp
  have hlim := (continuous_boundary_limit (c1_pullback_continuous hu) hl).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  simp only [mul_zero] at hlim
  apply hlim.congr
  intro j
  have hA : 0<(j:ℝ)+1 := by positivity
  have h := c1_standard_stokes hu
    ((outerProfile_smooth ((j:ℝ)+1)).comp radiusSq_smooth)
    (HasCompactSupport.comp_radiusSq (outerProfile_compact hA))
  dsimp only [Function.comp_def] at h
  simp_rw [cutoffWedge_radial_rotation (outerProfile_smooth ((j:ℝ)+1))] at h
  dsimp only [Function.comp_def]
  linarith

end HigherDimensionalBallPacking.Rigidity

end

end OAI
