import Mathlib
import OAI.Geometry.BallPacking.Moser.AnnularFinalPacking

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold MeasureTheory Filter

theorem equalNormalCoefficient_pos {m : ℕ} {b d : ℝ} (hb : 0≤b) (hbd : b*d<1)
    {p : Fin m → ℝ} (hp : (∑ j,p j)≤d) : 0<equalNormalCoefficient m b p := by
  unfold equalNormalCoefficient
  have hle := mul_le_mul_of_nonneg_left hp hb
  linarith

theorem equalNormalCoefficient_le_one {m : ℕ} {b : ℝ} (hb : 0≤b)
    {p : Fin m → ℝ} (hp : ∀ j,0≤p j) : equalNormalCoefficient m b p≤1 := by
  unfold equalNormalCoefficient
  exact sub_le_self _ (mul_nonneg hb (Finset.sum_nonneg (fun j _ => hp j)))

theorem equalNormalCoefficient_uniform_limit {m : ℕ} {b d a : ℝ}
    (hb : 0≤b) (hbd : b*d<1) {P : Set (Fin m → ℝ)}
    (hP : ∀ p∈P,(∀ j,0≤p j) ∧ (∑ j,p j)≤d)
    {mass : ℕ → ℝ} (hmass : Tendsto mass atTop (𝓝 a)) :
    TendstoUniformlyOn (fun ℓ p => equalNormalCoefficient m b p * mass ℓ)
      (fun p => a * equalNormalCoefficient m b p) atTop P := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hm : ∀ᶠ ℓ in atTop,dist (mass ℓ) a<ε :=
    hmass.eventually (Metric.ball_mem_nhds a hε)
  filter_upwards [hm] with ℓ hℓ p hp
  have hc0 := equalNormalCoefficient_pos hb hbd (hP p hp).2
  have hc1 := equalNormalCoefficient_le_one hb (hP p hp).1
  rw [Real.dist_eq,show a*equalNormalCoefficient m b p-
    equalNormalCoefficient m b p*mass ℓ = equalNormalCoefficient m b p*(a-mass ℓ) by ring,
    abs_mul,abs_of_pos hc0]
  calc
    equalNormalCoefficient m b p * |a-mass ℓ| ≤ |a-mass ℓ| :=
      mul_le_of_le_one_left (abs_nonneg _) hc1
    _ < ε := by simpa only [Real.dist_eq,abs_sub_comm] using hℓ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormalSpace M] [SigmaCompactSpace M]

theorem exists_equalNormalPrimitive_sequence {m : ℕ}
    (D : ℕ → Set M) (hD : ∀ ℓ,IsCompact (D ℓ))
    (hproper : ∀ ℓ,(D ℓ)ᶜ.Nonempty) (hor : PositivePlaneTransitions M)
    {σ : ManifoldTwoForm Plane M} (hσ : SmoothTwoForm σ)
    (hskew : ∀ x u v,σ x u v= -σ x v u)
    (b : ℝ) (A : ℕ → Fin m → ManifoldOneForm Plane M)
    (hA : ∀ ℓ j,SmoothOneFormFamily (fun _ : ℝ => A ℓ j))
    (hdA : ∀ ℓ,∀ᶠ x in 𝓝ˢ (D ℓ),∀ j,manifoldExteriorOneForm (A ℓ j) x=(-b) • σ x) :
    ∃ γ : ℕ → ManifoldOneForm Plane M,
      (∀ ℓ,SmoothOneFormFamily (fun _ : ℝ => γ ℓ)) ∧
      (∀ ℓ,∃ L : Set M,IsCompact L ∧ ∀ x,x∉L → γ ℓ x=0) ∧
      (∀ ℓ,SmoothOneFormFamily (equalNormalPrimitive (γ ℓ) (A ℓ))) ∧
      ∀ ℓ,∀ᶠ x in 𝓝ˢ (D ℓ),∀ p,
        manifoldExteriorOneForm (equalNormalPrimitive (γ ℓ) (A ℓ) p) x =
          equalNormalCoefficient m b p • σ x := by
  classical
  have hex ℓ := exists_base_primitive_near_compact (hD ℓ) (hproper ℓ) hor hσ hskew
  choose γ L hL hγ hγz hdγ using hex
  refine ⟨γ,hγ,fun ℓ => ⟨L ℓ,hL ℓ,hγz ℓ⟩,
    fun ℓ => equalNormalPrimitive_smooth (hγ ℓ) (hA ℓ),?_⟩
  intro ℓ
  filter_upwards [hdγ ℓ,hdA ℓ] with x hxγ hxA
  exact equalNormalPrimitive_exterior (hγ ℓ) (hA ℓ) b σ hxγ hxA

variable [MeasurableSpace M] [BorelSpace M]

omit [PreconnectedSpace M] [NormalSpace M] in
theorem equalNormalPrimitive_mass {m : ℕ} {D : Set M} (hD : IsCompact D)
    (Γ : (Fin m → ℝ) → ManifoldOneForm Plane M)
    (σ : ManifoldTwoForm Plane M) (b : ℝ)
    (hd : ∀ x∈D,∀ p,manifoldExteriorOneForm (Γ p) x=equalNormalCoefficient m b p • σ x)
    (p : Fin m → ℝ) :
    compactSurfaceFormIntegral hD (manifoldExteriorOneForm (Γ p)) =
      equalNormalCoefficient m b p * compactSurfaceFormIntegral hD σ := by
  rw [compactSurfaceFormIntegral_congr hD (fun x hx => hd x hx p)]
  exact compactSurfaceFormIntegral_smul hD _ σ

omit [PreconnectedSpace M] [NormalSpace M] in
theorem equalNormalPrimitive_area_limit {m : ℕ}
    (D : ℕ → Set M) (hD : ∀ ℓ,IsCompact (D ℓ))
    (Γ : ℕ → (Fin m → ℝ) → ManifoldOneForm Plane M)
    (σ : ManifoldTwoForm Plane M) {b d a : ℝ} (hb : 0≤b) (hbd : b*d<1)
    {P : Set (Fin m → ℝ)} (hP : ∀ p∈P,(∀ j,0≤p j) ∧ (∑ j,p j)≤d)
    (hd : ∀ ℓ,∀ x∈D ℓ,∀ p,
      manifoldExteriorOneForm (Γ ℓ p) x=equalNormalCoefficient m b p • σ x)
    (hmass : Tendsto (fun ℓ => compactSurfaceFormIntegral (hD ℓ) σ) atTop (𝓝 a)) :
    TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (hD ℓ)
      (manifoldExteriorOneForm (Γ ℓ p)))
      (fun p => a * equalNormalCoefficient m b p) atTop P := by
  have he ℓ p := equalNormalPrimitive_mass (hD ℓ) (Γ ℓ) σ b (hd ℓ) p
  simp_rw [he]
  exact equalNormalCoefficient_uniform_limit hb hbd hP hmass

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m q : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance : SigmaCompactSpace (locus a) := curveSigmaCompact a

 def normalHorizontalPrimitive (b : ℝ) (p : Fin q → ℝ) : ManifoldOneForm Plane (locus a) :=
  equalNormalCoefficient q b p • curveFSPrimitive a (1/Real.pi)

 theorem normalHorizontalPrimitive_smooth (b : ℝ) :
    SmoothOneFormFamily (normalHorizontalPrimitive (q := q) a b) :=
  ((curveFSPrimitive_smooth a (1/Real.pi)).comp
    (f := fun _ : Fin q → ℝ => (0:ℝ)) contDiff_const).smul (equalNormalCoefficient_smooth q b)

 theorem normalHorizontalPrimitive_exterior (b : ℝ) (p : Fin q → ℝ) (x : locus a) :
    manifoldExteriorOneForm (normalHorizontalPrimitive a b p) x=
      equalNormalCoefficient q b p • curveFSForm a (1/Real.pi) x := by
  have hx := (extChartAt 𝓘(ℝ,Plane) x).map_source (mem_extChartAt_source x)
  rw [normalHorizontalPrimitive,manifoldExteriorOneForm_smul_at _
    ((curveFSPrimitive_smooth a (1/Real.pi)).spatial_smooth 0 x hx),curveFSPrimitive_exterior]

 theorem normalHorizontalPrimitive_area_limit {b d : ℝ} (hb : 0≤b) (hbd : b*d<1)
    {P : Set (Fin q → ℝ)} (hP : ∀ p∈P,(∀ j,0≤p j) ∧ (∑ j,p j)≤d) :
    TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ))
      (fun x => equalNormalCoefficient q b p • curveFSForm a (1/Real.pi) x))
      (fun p => (2:ℝ)^m*equalNormalCoefficient q b p) atTop P := by
  have he p : (fun x => equalNormalCoefficient q b p • curveFSForm a (1/Real.pi) x)=
      equalNormalCoefficient q b p • curveFSForm a (1/Real.pi) := rfl
  simp_rw [he,compactSurfaceFormIntegral_smul]
  exact equalNormalCoefficient_uniform_limit hb hbd hP (tendsto_normalized_exhaustion_area a)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable (m : ℕ)

theorem transverse_transition_differentiable (c : Surface m) {z : ℂ}
    (hz : z∈transverseAnnulusDomain m) :
    DifferentiableAt ℂ (((normalChartAt (parameters m) c).sliceChart c) ∘
      (transverseAnnulusChart m).symm) z := by
  let n := normalChartAt (parameters m) c
  have hs := (curveCoordinate n.coordinate).contDiff.contDiffAt.comp z
    (transverseAnnulusPoint_contDiffAt m hz)
  apply (hs.differentiableAt (by simp)).congr_of_eventuallyEq
  filter_upwards [(transverseAnnulusDomain_isOpen m).mem_nhds hz] with t ht
  change curveCoordinate n.coordinate ((transverseAnnulusInverse m t).val)=_
  rw [transverseAnnulusInverse_val m ht.1]
  rfl

theorem transverse_transition_inverse_differentiable (c : Surface m) {z : ℂ}
    (hz : z∈((normalChartAt (parameters m) c).sliceChart c).target) :
    DifferentiableAt ℂ ((transverseAnnulusChart m) ∘
      ((normalChartAt (parameters m) c).sliceChart c).symm) z := by
  have hs := ((normalChartAt (parameters m) c).sliceChart_inverse_smooth c).contDiffAt
    (((normalChartAt (parameters m) c).sliceChart c).open_target.mem_nhds hz)
  exact ((transverseCoordinate m).contDiff.contDiffAt.comp z hs).differentiableAt (by simp)

theorem transverseDiffeomorph_positive : PositivePartialChart (transverseDiffeomorph m) := by
  intro c y hy hc
  let n := normalChartAt (parameters m) c
  let e := (transverseAnnulusChart m).symm.trans (n.sliceChart c)
  have hchart : chartAt Plane c=realChart (parameters m) c := rfl
  have hc' : transverseDiffeomorph m y∈(n.sliceChart c).source := by
    simpa only [mfld_simps,hchart,realChart_source] using hc
  have hy' : Complex.equivRealProdCLM.symm y∈transverseAnnulusDomain m := by
    simpa only [transverseDiffeomorph_source,mem_preimage] using hy
  have hye : Complex.equivRealProdCLM.symm y∈e.source := ⟨hy',hc'⟩
  have h := holomorphic_partialHomeomorph_orientation e hye
    (transverse_transition_differentiable m c hy')
    (transverse_transition_inverse_differentiable m c (n.sliceChart c |>.map_source hc'))
  simpa only [e,mfld_simps,hchart,realChart,realTransverseChart,
    transverseDiffeomorph,Function.comp_def,OpenPartialHomeomorph.trans_apply,
    ContinuousLinearEquiv.coe_toHomeomorph] using h

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

def rectanglePolar (y : Plane) : Plane :=
  Complex.equivRealProdCLM (cylinderComplexMap (cylinderCover y))

theorem rectanglePolar_smooth : ContDiff ℝ ∞ rectanglePolar := by
  apply contMDiff_iff_contDiff.mp
  exact Complex.equivRealProdCLM.contDiff.contMDiff.comp
    (cylinderComplexMap_smooth.comp cylinderCover_smooth)

theorem rectanglePolar_det (y : Plane) :
    (fderiv ℝ rectanglePolar y).det=2*Real.pi*(Real.exp y.1)^2 := by
  let u : ℂ := circleTurn y.2
  have h1 := (Complex.ofRealCLM.hasFDerivAt.comp y.1 (Real.hasDerivAt_exp y.1).hasFDerivAt).comp y
    (hasFDerivAt_fst : HasFDerivAt (@Prod.fst ℝ ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) y)
  have h2 := (circleTurn_deriv y.2).hasFDerivAt.comp y
    (hasFDerivAt_snd : HasFDerivAt (@Prod.snd ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) y)
  have hh := Complex.equivRealProdCLM.hasFDerivAt.comp y (h1.mul h2)
  change HasFDerivAt rectanglePolar _ y at hh
  rw [hh.fderiv,planar_det,planarArea_apply]
  have hu : u.re^2+u.im^2=1 := by
    have h := Complex.sq_norm (u)
    rw [show ‖u‖=1 from Circle.norm_coe _,one_pow] at h
    simpa only [Complex.normSq_apply,pow_two] using h.symm
  simp [Function.comp_def,Complex.mul_re,Complex.mul_im,Complex.exp_ofReal_re]
  calc
    _=2*Real.pi*(Real.exp y.1)^2*(u.re^2+u.im^2) := by ring
    _=_ := by rw [hu,mul_one]

theorem rectanglePolar_det_pos (y : Plane) : 0<(fderiv ℝ rectanglePolar y).det := by
  rw [rectanglePolar_det]
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_pos (Real.exp_pos _))

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

theorem fixed_handle_densityChart_positive (H : AnnularHandleData Plane (Surface m))
    (hH : H.chart=restrictedTransverseCylinder m (transverseCylinderWidth m/2)) :
    PositivePartialChart H.densityChart := by
  have heq : (H.densityChart : Plane → Surface m)=transverseDiffeomorph m ∘ rectanglePolar := by
    funext y
    rw [AnnularHandleData.densityChart_apply,hH]
    rfl
  intro c y hy hc
  have hys : cylinderCover y∈H.chart.source := hy.2
  rw [hH] at hys
  have hyc : cylinderCover y∈(transverseCylinder m).source := hys.1
  rw [transverseCylinder_source] at hyc
  have hyd : rectanglePolar y∈(transverseDiffeomorph m).source := by
    rw [transverseDiffeomorph_source]
    change Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM
      (cylinderComplexMap (cylinderCover y)))∈transverseAnnulusDomain m
    simpa only [ContinuousLinearEquiv.symm_apply_apply,mem_preimage] using hyc
  have hc' : transverseDiffeomorph m (rectanglePolar y)∈(extChartAt 𝓘(ℝ,Plane) c).source := by
    simpa only [heq,Function.comp_apply] using hc
  have hpos := transverseDiffeomorph_positive m c (rectanglePolar y) hyd hc'
  have hf : DifferentiableAt ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ transverseDiffeomorph m) (rectanglePolar y) := by
    have hi := (transverseDiffeomorph m).contMDiffOn.contMDiffAt
      ((transverseDiffeomorph m).open_source.mem_nhds hyd)
    have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,Plane)) (n := ∞) (x := c)
      (by simpa only [extChartAt_source] using hc')
    exact (ho.comp _ hi).contDiffAt.differentiableAt (by simp)
  rw [heq,← Function.comp_assoc,fderiv_comp y hf (rectanglePolar_smooth.differentiable (by simp) y)]
  change 0<LinearMap.det ((fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ transverseDiffeomorph m)
    (rectanglePolar y)).toLinearMap.comp (fderiv ℝ rectanglePolar y).toLinearMap)
  rw [LinearMap.det_comp]
  exact mul_pos hpos (rectanglePolar_det_pos y)

theorem exists_positive_fixed_annularHandleData :
    ∃ H : AnnularHandleData Plane (Surface m),
      H.width=transverseCylinderWidth m/2 ∧
      H.clock=positiveCircleClock (1/4) ∧ PositivePartialChart H.densityChart := by
  obtain ⟨H,hw,hH,hf⟩ := exists_fixed_annularHandleData m
  exact ⟨H,hw,hf,fixed_handle_densityChart_positive m H hH⟩

theorem exists_positive_annularHandleData :
    ∃ H : AnnularHandleData Plane (Surface m),PositivePartialChart H.densityChart := by
  obtain ⟨H,_,hH,_⟩ := exists_fixed_annularHandleData m
  exact ⟨H,fixed_handle_densityChart_positive m H hH⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport
open scoped BigOperators
open Set MeasureTheory

def momentSimplex (m : ℕ) (h : ℝ) : Set (Fin m → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i ≤ h}

theorem momentSimplex_isClosed (m : ℕ) (h : ℝ) : IsClosed (momentSimplex m h) := by
  have h₁ : IsClosed {p : Fin m → ℝ | ∀ i, 0 ≤ p i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact h₁.inter (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

theorem momentSimplex_isCompact (m : ℕ) (h : ℝ) : IsCompact (momentSimplex m h) := by
  refine (isCompact_Icc (a := (fun _ : Fin m => (0:ℝ))) (b := fun _ => h)).of_isClosed_subset (momentSimplex_isClosed m h) ?_
  intro p hp
  refine ⟨hp.1,fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)).trans hp.2

theorem momentSimplex_cons {m : ℕ} (h t : ℝ) (p : Fin m → ℝ) :
    Fin.cons t p ∈ momentSimplex (m+1) h ↔ 0 ≤ t ∧ p ∈ momentSimplex m (h-t) := by
  simp only [momentSimplex,mem_ofPred_eq,Fin.forall_fin_succ,Fin.cons_zero,
    Fin.cons_succ,Fin.sum_univ_succ]
  constructor
  · rintro ⟨⟨ht,hp⟩,hs⟩
    exact ⟨ht,hp,by linarith⟩
  · rintro ⟨ht,hp,hs⟩
    exact ⟨⟨ht,hp⟩,by linarith⟩

theorem integrable_simplex_power (m k : ℕ) (h : ℝ) :
    Integrable ((momentSimplex m h).indicator (fun p => (h-∑ i,p i)^k)) := by
  apply (integrable_indicator_iff (momentSimplex_isClosed m h).measurableSet).2
  exact (((continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_apply i)).pow k).continuousOn).integrableOn_compact (momentSimplex_isCompact m h)

theorem simplex_power_cons {m k : ℕ} (h t : ℝ) (p : Fin m → ℝ) :
    (momentSimplex (m+1) h).indicator (fun q => (h-∑ i,q i)^k) (Fin.cons t p) =
      (Icc 0 h).indicator (fun s => (momentSimplex m (h-s)).indicator
        (fun q => (h-s-∑ i,q i)^k) p) t := by
  by_cases ht : t ∈ Icc 0 h
  · rw [indicator_of_mem ht]
    by_cases hp : p ∈ momentSimplex m (h-t)
    · rw [indicator_of_mem hp,indicator_of_mem ((momentSimplex_cons h t p).2 ⟨ht.1,hp⟩)]
      congr 1
      simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
      ring
    · rw [indicator_of_notMem hp,indicator_of_notMem (by
        intro hh; exact hp ((momentSimplex_cons h t p).1 hh).2)]
  · rw [indicator_of_notMem ht,indicator_of_notMem (by
      intro hh
      obtain ⟨ht0,hp⟩ := (momentSimplex_cons h t p).1 hh
      have hs : 0 ≤ ∑ i,p i := Finset.sum_nonneg fun i _ => hp.1 i
      exact ht ⟨ht0,by linarith [hp.2]⟩)]

theorem integral_simplex_power_step (m k : ℕ) (h : ℝ) :
    (∫ p in momentSimplex (m+1) h, (h-∑ i,p i)^k) =
      ∫ t in Icc 0 h, ∫ p in momentSimplex m (h-t), (h-t-∑ i,p i)^k := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
  let f := (momentSimplex (m+1) h).indicator (fun p => (h-∑ i,p i)^k)
  have hi : Integrable (f ∘ e) := (he.integrable_comp_emb e.measurableEmbedding).2
    (integrable_simplex_power (m+1) k h)
  rw [←integral_indicator (momentSimplex_isClosed (m+1) h).measurableSet]
  change (∫ p, f p) = _
  rw [←he.integral_comp e.measurableEmbedding]
  change (∫ x, (f ∘ e) x ∂(volume.prod volume)) = _
  rw [integral_prod _ hi]
  have hes (x : ℝ × (Fin m → ℝ)) : e x = Fin.cons x.1 x.2 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  simp only [Function.comp_apply,hes,f,simplex_power_cons]
  rw [←integral_indicator measurableSet_Icc]
  congr 1
  funext t
  by_cases ht : t ∈ Icc 0 h
  · simp only [indicator_of_mem ht]
    exact integral_indicator (momentSimplex_isClosed m (h-t)).measurableSet
  · simp [ht]

theorem integral_simplex_power (m k : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ p in momentSimplex m h, (h-∑ i,p i)^k) =
      (k.factorial : ℝ) / ((m+k).factorial : ℝ) * h^(m+k) := by
  induction m generalizing h with
  | zero =>
    have hv : (volume : Measure (Fin 0 → ℝ)) univ = 1 := Measure.pi_empty_univ _
    have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
    simp [momentSimplex,hh,hv,measureReal_def,hfac]
  | succ m ih =>
    rw [integral_simplex_power_step]
    have hc : (∫ t in Icc 0 h, ∫ p in momentSimplex m (h-t), (h-t-∑ i,p i)^k) =
        ∫ t in Icc 0 h, (k.factorial : ℝ) / ((m+k).factorial : ℝ) * (h-t)^(m+k) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact ih (by linarith [ht.2])
    rw [hc,integral_const_mul,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le hh,
      intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^(m+k)) h]
    rw [sub_self,sub_zero,integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero _),sub_zero]
    rw [show m+1+k=m+k+1 by omega,Nat.factorial_succ,Nat.cast_mul]
    simp only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_inv_rev]
    ring

theorem volumeReal_momentSimplex (m : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (momentSimplex m h) = h^m / (m.factorial : ℝ) := by
  simpa [div_eq_mul_inv,mul_comm] using integral_simplex_power m 0 hh

theorem integral_simplex_tent (m : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ p in momentSimplex m h, (h-∑ i,p i)) = h^(m+1) / ((m+1).factorial : ℝ) := by
  simpa [div_eq_mul_inv,mul_comm] using integral_simplex_power m 1 hh

theorem tent_indicator_eq {m : ℕ} {r : ℝ} {D : Set (Fin m → ℝ)}
    (hD : ∀ p ∈ D, ∀ i, 0 ≤ p i) (hcap : momentSimplex m r ⊆ D) :
    D.indicator (fun p => max (r-∑ i,p i) 0) =
      (momentSimplex m r).indicator (fun p => r-∑ i,p i) := by
  funext p
  by_cases hp : p ∈ momentSimplex m r
  · rw [indicator_of_mem hp,indicator_of_mem (hcap hp),max_eq_left (sub_nonneg.mpr hp.2)]
  · rw [indicator_of_notMem hp]
    by_cases hd : p ∈ D
    · rw [indicator_of_mem hd,max_eq_right]
      exact le_of_lt (sub_neg.mpr (lt_of_not_ge (fun hs => hp ⟨hD p hd,hs⟩)))
    · exact indicator_of_notMem hd _

theorem integrableOn_tent {m : ℕ} {r : ℝ} {D : Set (Fin m → ℝ)}
    (hDmeas : MeasurableSet D) (hD : ∀ p ∈ D, ∀ i, 0 ≤ p i)
    (hcap : momentSimplex m r ⊆ D) :
    IntegrableOn (fun p => max (r-∑ i,p i) 0) D := by
  rw [←integrable_indicator_iff hDmeas,tent_indicator_eq hD hcap]
  simpa using integrable_simplex_power m 1 r

theorem integral_tent {m : ℕ} {r : ℝ} (hr : 0 ≤ r) {D : Set (Fin m → ℝ)}
    (hDmeas : MeasurableSet D) (hD : ∀ p ∈ D, ∀ i, 0 ≤ p i)
    (hcap : momentSimplex m r ⊆ D) :
    (∫ p in D, max (r-∑ i,p i) 0) = r^(m+1) / ((m+1).factorial : ℝ) := by
  rw [←integral_indicator hDmeas,tent_indicator_eq hD hcap,
    integral_indicator (momentSimplex_isClosed m r).measurableSet]
  exact integral_simplex_tent m hr

theorem integral_sum_tents {m : ℕ} {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) {D : Set (Fin m → ℝ)}
    (hDmeas : MeasurableSet D) (hD : ∀ p ∈ D, ∀ j, 0 ≤ p j)
    (hcap : ∀ i, momentSimplex m (r i) ⊆ D) :
    (∫ p in D, ∑ i, max (r i-∑ j,p j) 0) =
      (∑ i,r i^(m+1)) / ((m+1).factorial : ℝ) := by
  rw [integral_finsetSum _ (fun i _ => integrableOn_tent hDmeas hD (hcap i))]
  simp_rw [integral_tent (hr _) hDmeas hD (hcap _)]
  exact (Finset.sum_div _ _ _).symm

def smallModelMean (m : ℕ) (h : ℝ) : ℝ :=
  (2:ℝ)^m*h^m/(m.factorial : ℝ)*(1-2*m*h/(m+1))

theorem integral_small_model (m : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ p in momentSimplex m h, (2:ℝ)^m*(1-2*∑ i,p i)) = smallModelMean m h := by
  have ht : IntegrableOn (fun p : Fin m → ℝ => h-∑ i,p i) (momentSimplex m h) := by
    exact ((continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_apply i)).continuousOn).integrableOn_compact (momentSimplex_isCompact m h)
  have hc : IntegrableOn (fun _ : Fin m → ℝ => 1-2*h) (momentSimplex m h) :=
    continuousOn_const.integrableOn_compact (momentSimplex_isCompact m h)
  have heq (p : Fin m → ℝ) : 1-2*∑ i,p i = (1-2*h)+2*(h-∑ i,p i) := by ring
  simp_rw [heq]
  rw [integral_const_mul,integral_add hc (ht.const_mul 2),integral_const_mul,
    setIntegral_const,integral_simplex_tent m hh]
  simp only [smul_eq_mul,volumeReal_momentSimplex m hh]
  dsimp [smallModelMean]
  rw [Nat.factorial_succ,Nat.cast_mul]
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm : (m:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem continuous_smallModelMean (m : ℕ) : Continuous (smallModelMean m) := by
  unfold smallModelMean
  fun_prop

theorem smallModelMean_half (m : ℕ) : smallModelMean m (1/2) =
    1 / ((m+1).factorial : ℝ) := by
  have hp : (2:ℝ)^m*(1/2)^m=1 := by rw [←mul_pow]; norm_num
  dsimp [smallModelMean]
  rw [hp,Nat.factorial_succ,Nat.cast_mul]
  simp only [Nat.cast_add,Nat.cast_one]
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm : (m:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

def cappedAffine {m : ℕ} {ι : Type*} [Fintype ι]
    (A : ℝ) (B : Fin m → ℝ) (r w : ι → ℝ) (p : Fin m → ℝ) : ℝ :=
  A-(∑ j, B j*p j)-∑ i,w i*max (r i-∑ j,p j) 0

theorem continuous_cappedAffine {m : ℕ} {ι : Type*} [Fintype ι]
    (A : ℝ) (B : Fin m → ℝ) (r w : ι → ℝ) : Continuous (cappedAffine A B r w) := by
  unfold cappedAffine
  fun_prop

theorem concaveOn_cappedAffine {m : ℕ} {ι : Type*} [Fintype ι]
    (A : ℝ) (B : Fin m → ℝ) (r w : ι → ℝ) (hw : ∀ i,0 ≤ w i)
    {D : Set (Fin m → ℝ)} (hD : Convex ℝ D) : ConcaveOn ℝ D (cappedAffine A B r w) := by
  refine ⟨hD,?_⟩
  intro x hx y hy a b ha hb hab
  have hsum : (∑ j,(a • x+b • y) j)=a*(∑ j,x j)+b*(∑ j,y j) := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,Finset.mul_sum]
  have hB : (∑ j,B j*(a • x+b • y) j)=a*(∑ j,B j*x j)+b*(∑ j,B j*y j) := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  have hcap (i : ι) : max (r i-∑ j,(a • x+b • y) j) 0 ≤
      a*max (r i-∑ j,x j) 0+b*max (r i-∑ j,y j) 0 := by
    apply max_le
    · rw [hsum]
      have hx := mul_le_mul_of_nonneg_left (le_max_left (r i-∑ j,x j) 0) ha
      have hy := mul_le_mul_of_nonneg_left (le_max_left (r i-∑ j,y j) 0) hb
      have he := congrArg (fun t : ℝ => t*r i) hab
      nlinarith only [hx,hy,he]
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hcap i) (hw i))
  have he : (∑ i,w i*(a*max (r i-∑ j,x j) 0+b*max (r i-∑ j,y j) 0)) =
      a*(∑ i,w i*max (r i-∑ j,x j) 0)+b*(∑ i,w i*max (r i-∑ j,y j) 0) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [he] at hc
  have hA : a*A+b*A=A := by rw [←add_mul,hab,one_mul]
  dsimp [cappedAffine]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hB hc
  rw [hB]
  nlinarith only [hA,hc]

end PackingSufficiencySupport
end

end OAI
