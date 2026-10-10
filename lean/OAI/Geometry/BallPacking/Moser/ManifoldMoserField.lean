import Mathlib
import OAI.Geometry.BallPacking.Moser.PlanarCovectorPrimitive

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped NNReal
open MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

abbrev ManifoldOneForm (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  M → E →L[ℝ] ℝ

def chartOneForm (α : ManifoldOneForm E M) (c : M) (y : E) : E →L[ℝ] ℝ :=
  let z := (extChartAt 𝓘(ℝ,E) c).symm y
  (α z).comp (chartDifferential c z).inverse

def manifoldMoserField (Ω : ℝ → ManifoldTwoForm E M)
    (α : ℝ → ManifoldOneForm E M) (p : ℝ × M) : TangentSpace 𝓘(ℝ,E) p.2 :=
  -(Ω p.1 p.2).inverse (α p.1 p.2)

theorem chartTwoForm_isInvertible {Ω : ManifoldTwoForm E M} {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : (Ω ((extChartAt 𝓘(ℝ,E) c).symm y)).IsInvertible) :
    (chartTwoForm Ω c y).IsInvertible := by
  apply bilinearComp_isInvertible hΩ
  apply ContinuousLinearMap.IsInvertible.inverse
  convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
    ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1

theorem chart_moser_contraction
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : (Ω p.1 ((extChartAt 𝓘(ℝ,E) c).symm p.2)).IsInvertible) :
    chartTwoForm (Ω p.1) c p.2 (timeChartField (manifoldMoserField Ω α) c p) =
      -chartOneForm (α p.1) c p.2 := by
  let z := (extChartAt 𝓘(ℝ,E) c).symm p.2
  have hC : (chartDifferential (E := E) c z).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
      ((extChartAt 𝓘(ℝ,E) c).map_target hp) using 1
  ext w
  change Ω p.1 z ((chartDifferential c z).inverse
      (chartDifferential c z (manifoldMoserField Ω α (p.1,z))))
      ((chartDifferential c z).inverse w) =
    -(α p.1 z ((chartDifferential c z).inverse w))
  erw [hC.inverse_apply_self]
  change Ω p.1 z (-((Ω p.1 z).inverse (α p.1 z))) _ = _
  rw [map_neg,hΩ.self_apply_inverse]
  rfl

theorem timeChartField_moser_eq
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : (Ω p.1 ((extChartAt 𝓘(ℝ,E) c).symm p.2)).IsInvertible) :
    timeChartField (manifoldMoserField Ω α) c p =
      -(chartTwoForm (Ω p.1) c p.2).inverse (chartOneForm (α p.1) c p.2) := by
  have hi := chartTwoForm_isInvertible hp hΩ
  apply hi.injective
  rw [chart_moser_contraction hp hΩ,map_neg,hi.self_apply_inverse]

variable [CompleteSpace E]

theorem timeChartField_moser_contDiffAt
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) p)
    (hα : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) p)
    (hinv : ∀ᶠ q : ℝ × E in 𝓝 p,
      (Ω q.1 ((extChartAt 𝓘(ℝ,E) c).symm q.2)).IsInvertible) :
    ContDiffAt ℝ ∞ (timeChartField (manifoldMoserField Ω α) c) p := by
  have hi := chartTwoForm_isInvertible hp hinv.self_of_nhds
  have hs := ((hi.contDiffAt_map_inverse.comp p hΩ).clm_apply hα).neg
  apply hs.congr_of_eventuallyEq
  have ht : ∀ᶠ q : ℝ × E in 𝓝 p, q.2 ∈ (extChartAt 𝓘(ℝ,E) c).target :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp)
  filter_upwards [hinv,ht] with q hq hqt
  exact timeChartField_moser_eq hqt hq

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem periodic_parameter_arg_smooth {h : P × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hp : ∀ y, Periodic (fun t => h (y,t)) (2*Real.pi)) {p : P × ℂ} (hz : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : P × ℂ => h (q.1,q.2.arg)) p := by
  by_cases hs : p.2 ∈ Complex.slitPlane
  · exact hh.contDiffAt.comp p (contDiffAt_fst.prodMk
      ((contDiffAt_arg_slit hs).comp p contDiffAt_snd))
  · have hsneg : -p.2 ∈ Complex.slitPlane :=
      (Complex.mem_slitPlane_or_neg_mem_slitPlane hz).resolve_left hs
    have hd : ContDiffAt ℝ ∞ (fun q : P × ℂ => h (q.1,(-q.2).arg+Real.pi)) p :=
      hh.contDiffAt.comp p (contDiffAt_fst.prodMk
        (((contDiffAt_arg_slit hsneg).comp p contDiffAt_snd.neg).add contDiffAt_const))
    apply hd.congr_of_eventuallyEq
    filter_upwards [(isOpen_ne.preimage continuous_snd).mem_nhds hz] with q hq
    exact periodic_arg_neg (hp q.1) hq

theorem angularExtension_parameter_smooth {R delta : ℝ} (hd : 0 < delta)
    (hdR : delta < R^2) {h : P × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hp : ∀ y, Periodic (fun t => h (y,t)) (2*Real.pi)) :
    ContDiff ℝ ∞ (fun p : P × Plane => angularExtension R delta hd (fun t => h (p.1,t)) p.2) := by
  let b : ContDiffBump (R^2) := ⟨delta/2,delta,by positivity,by linarith⟩
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases h0 : p.2 = 0
  · have hn : ∀ᶠ q : P × Plane in 𝓝 p, delta < |radiusSq q.2-R^2| := by
      apply (isOpen_lt continuous_const (((radiusSq_smooth.continuous.comp continuous_snd).sub
        continuous_const).abs)).mem_nhds
      simpa [h0,radiusSq,abs_of_nonneg (sq_nonneg R)] using hdR
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    exact angularExtension_zero hd _ q.2 hq.le
  · have hz : Complex.equivRealProdCLM.symm p.2 ≠ 0 := by
      intro he
      apply h0
      apply Complex.equivRealProdCLM.symm.injective
      simpa only [map_zero] using he
    exact (b.contDiff.comp (radiusSq_smooth.comp contDiff_snd)).contDiffAt.mul
      ((periodic_parameter_arg_smooth hh hp hz).comp p
        (contDiff_fst.prodMk (Complex.equivRealProdCLM.symm.contDiff.comp contDiff_snd)).contDiffAt)

omit [NormedSpace ℝ P] in
theorem angularExtension_parameter_compact {R delta : ℝ} (hd : 0 < delta)
    {h : P × ℝ → ℝ} {K : Set P} (hK : IsCompact K)
    (hzero : ∀ y, y ∉ K → ∀ t, h (y,t) = 0) :
    HasCompactSupport (fun p : P × Plane => angularExtension R delta hd (fun t => h (p.1,t)) p.2) := by
  apply HasCompactSupport.intro (hK.prod (isCompact_closedBall (0 : Plane) (R^2+delta+1)))
  intro p hp
  by_cases hy : p.1 ∈ K
  · have hx : p.2 ∉ Metric.closedBall 0 (R^2+delta+1) := fun hx => hp ⟨hy,hx⟩
    apply angularExtension_zero hd _ p.2
    by_contra! ht
    have hq : radiusSq p.2 < R^2+delta := by linarith [(abs_lt.mp ht).2]
    apply hx
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,Real.norm_eq_abs,Real.norm_eq_abs]
    have h1 : p.2.1^2 ≤ radiusSq p.2 := by dsimp [radiusSq]; nlinarith [sq_nonneg p.2.2]
    have h2 : p.2.2^2 ≤ radiusSq p.2 := by dsimp [radiusSq]; nlinarith [sq_nonneg p.2.1]
    have hb : 0 < R^2+delta := by positivity
    constructor
    · nlinarith [sq_abs p.2.1,abs_nonneg p.2.1,sq_nonneg (|p.2.1|-1)]
    · nlinarith [sq_abs p.2.2,abs_nonneg p.2.2,sq_nonneg (|p.2.2|-1)]
  · simp only [angularExtension,hzero p.1 hy,mul_zero]

theorem circlePullback_parameter_smooth {alpha : P × Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (R : ℝ) :
    ContDiff ℝ ∞ (fun p : P × ℝ => circlePullback (fun x => alpha (p.1,x)) R p.2) := by
  apply (ha.comp (contDiff_fst.prodMk (polar_smooth.comp (contDiff_const.prodMk contDiff_snd)))).clm_apply
  fun_prop

variable [FiniteDimensional ℝ P]

theorem exists_parametric_circle_primitive {alpha : P × Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (hac : HasCompactSupport alpha) {R delta : ℝ}
    (hR : 0 < R) (hd : 0 < delta) (hdR : delta < R^2)
    (hz : ∀ y, (∫ p in roundDisk R, planarCurl (fun x => alpha (y,x)) p) = 0) :
    ∃ H : P × Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∀ y p, delta ≤ |radiusSq p-R^2| → H (y,p) = 0) ∧
      (∀ y t, fderiv ℝ (fun x => H (y,x)) (polarCoord.symm (R,t))
        (-R*Real.sin t,R*Real.cos t) = circlePullback (fun x => alpha (y,x)) R t) ∧
      ∀ y, (∀ x, alpha (y,x) = 0) → ∀ x, H (y,x) = 0 := by
  let a : P × ℝ → ℝ := fun p => circlePullback (fun x => alpha (p.1,x)) R p.2
  have has : ContDiff ℝ ∞ a := circlePullback_parameter_smooth ha R
  have hay (y : P) : ContDiff ℝ ∞ (fun t => a (y,t)) :=
    has.comp (contDiff_const.prodMk contDiff_id)
  have haz (y : P) : (∫ t in -Real.pi..Real.pi, a (y,t)) = 0 := by
    have hai : ContDiff ℝ ∞ (fun x : Plane => alpha (y,x)) :=
      ha.comp (contDiff_const.prodMk contDiff_id)
    exact (integral_curl_roundDisk hai hR).symm.trans (hz y)
  have hp (y : P) := periodicPrimitive_periodic (hay y).continuous
    (circlePullback_periodic (fun x => alpha (y,x)) R) (haz y)
  let H : P × Plane → ℝ := fun p =>
    angularExtension R delta hd (periodicPrimitive (fun t => a (p.1,t))) p.2
  have hH : ContDiff ℝ ∞ H := angularExtension_parameter_smooth hd hdR
    (contDiff_parameter_segment_integral has (-Real.pi)) hp
  have hHc : HasCompactSupport H := by
    have hK : IsCompact (Prod.fst '' tsupport alpha) := hac.image continuous_fst
    apply angularExtension_parameter_compact (h := fun p =>
      periodicPrimitive (fun t => a (p.1,t)) p.2) (K := Prod.fst '' tsupport alpha) hd hK
    intro y hy t
    have he : (fun t => a (y,t)) = fun _ => (0:ℝ) := by
      funext θ
      have hzero : alpha (y,polarCoord.symm (R,θ)) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hy ⟨(y,polarCoord.symm (R,θ)),h,rfl⟩)
      simp only [a,circlePullback,hzero,zero_apply]
    change periodicPrimitive (fun t => a (y,t)) t = 0
    rw [he]
    simp only [periodicPrimitive,intervalIntegral.integral_zero]
  refine ⟨H,hH,hHc,fun _ p hp => angularExtension_zero hd _ p hp,?_,?_⟩
  · intro y t
    have hc : HasDerivAt (fun t => polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) t := by
      change HasDerivAt (fun t => (R*Real.cos t,R*Real.sin t)) _ t
      exact (((Real.hasDerivAt_cos t).const_mul R).prodMk
        ((Real.hasDerivAt_sin t).const_mul R)).congr_deriv (by ext <;> simp [neg_mul])
    have hHy : ContDiff ℝ ∞ (fun x => H (y,x)) := hH.comp (contDiff_const.prodMk contDiff_id)
    have hdH := ((hHy.differentiable (by simp)) (polarCoord.symm (R,t))).hasFDerivAt.comp_hasDerivAt t hc
    have he : (fun t => H (y,polarCoord.symm (R,t))) = periodicPrimitive (fun t => a (y,t)) :=
      funext fun t => angularExtension_polar hR hd (hp y) t
    change HasDerivAt (fun t => H (y,polarCoord.symm (R,t))) _ t at hdH
    rw [he] at hdH
    exact hdH.unique (periodicPrimitive_hasDerivAt (hay y).continuous t)

  · intro y hy x
    have he : (fun t => a (y,t)) = fun _ => (0:ℝ) := by
      funext t
      simp only [a,circlePullback,hy,zero_apply]
    change angularExtension R delta hd (periodicPrimitive (fun t => a (y,t))) x = 0
    rw [he]
    simp only [angularExtension,periodicPrimitive,intervalIntegral.integral_zero,mul_zero]

omit [FiniteDimensional ℝ P] in
theorem fiber_fderiv {F : P × Plane → ℝ} (hF : ContDiff ℝ ∞ F) (y : P) (x : Plane) :
    fderiv ℝ (fun x => F (y,x)) x =
      (fderiv ℝ F (y,x)).comp (ContinuousLinearMap.inr ℝ P Plane) := by
  have hi : HasFDerivAt (fun x : Plane => (y,x)) (ContinuousLinearMap.inr ℝ P Plane) x := by
    simpa only [Prod.mk_add_mk,zero_add,add_zero,ContinuousLinearMap.inr_apply] using
      ((ContinuousLinearMap.inr ℝ P Plane).hasFDerivAt (x := x)).const_add (y,0)
  exact (((hF.differentiable (by simp)) (y,x)).hasFDerivAt.comp x hi).fderiv

omit [FiniteDimensional ℝ P] in
theorem fiber_fderiv_smooth {F : P × Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  have he : (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) =
      fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ P Plane) := by
    funext p
    exact fiber_fderiv hF p.1 p.2
  rw [he]
  exact (hF.fderiv_right (by simp)).clm_comp contDiff_const

omit [FiniteDimensional ℝ P] in
theorem fiber_fderiv_compact {F : P × Plane → ℝ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    HasCompactSupport (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  have he : (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) =
      (fun A : (P × Plane) →L[ℝ] ℝ => A.comp (ContinuousLinearMap.inr ℝ P Plane)) ∘ fderiv ℝ F := by
    funext p
    exact fiber_fderiv hF p.1 p.2
  rw [he]
  exact (hc.fderiv (𝕜 := ℝ)).comp_left (by simp only [ContinuousLinearMap.zero_comp])

omit [FiniteDimensional ℝ P] in

theorem parametric_finite_potential_correction {ι : Type*} [Fintype ι]
    {alpha : P × Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (hac : HasCompactSupport alpha) (R : ι → ℝ)
    (H : ι → P × Plane → ℝ) (hHs : ∀ i, ContDiff ℝ ∞ (H i))
    (hHc : ∀ i, HasCompactSupport (H i))
    (hself : ∀ i y p, radiusSq p = (R i)^2 →
      fderiv ℝ (fun x => H i (y,x)) p (-p.2,p.1) = alpha (y,p) (-p.2,p.1))
    (hother : ∀ i j, j ≠ i → ∀ y p, radiusSq p = (R i)^2 →
      fderiv ℝ (fun x => H j (y,x)) p = 0)
    (hHzero : ∀ i y, (∀ x, alpha (y,x) = 0) → ∀ x, H i (y,x) = 0) :
    ∃ beta : P × Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      (∀ y p, planarCurl (fun x => beta (y,x)) p = planarCurl (fun x => alpha (y,x)) p) ∧
      (∀ i y p, radiusSq p = (R i)^2 → beta (y,p) (-p.2,p.1) = 0) ∧
      ∀ y, (∀ x, alpha (y,x) = 0) → ∀ x, beta (y,x) = 0 := by
  classical
  let F : P × Plane → ℝ := fun p => ∑ i, H i p
  have hFs : ContDiff ℝ ∞ F := ContDiff.sum (fun i _ => hHs i)
  have hFc : HasCompactSupport F := by
    have he : (∑ i, H i) = F := by funext p; simp [F]
    rw [← he]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (f := H) (fun i _ => hHc i)
  have hFd (y : P) (p v : Plane) :
      fderiv ℝ (fun x => F (y,x)) p v = ∑ i, fderiv ℝ (fun x => H i (y,x)) p v := by
    change fderiv ℝ (fun x => ∑ i, H i (y,x)) p v = _
    have hHyi (i : ι) : DifferentiableAt ℝ (fun x : Plane => H i (y,x)) p :=
      (((hHs i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) p
    rw [fderiv_fun_sum (fun i _ => hHyi i)]
    simp only [sum_apply]
  let beta : P × Plane → Plane →L[ℝ] ℝ := fun p => alpha p - fderiv ℝ (fun x => F (p.1,x)) p.2
  refine ⟨beta,ha.sub (fiber_fderiv_smooth hFs),hac.sub (fiber_fderiv_compact hFs hFc),?_,?_,?_⟩
  · intro y p
    exact planarCurl_sub_differential (ha.comp (contDiff_const.prodMk contDiff_id))
      (hFs.comp (contDiff_const.prodMk contDiff_id)) p
  · intro i y p hp
    change alpha (y,p) (-p.2,p.1) - fderiv ℝ (fun x => F (y,x)) p (-p.2,p.1) = 0
    rw [hFd,Finset.sum_eq_single i,hself i y p hp,sub_self]
    · intro j _ hj
      rw [hother i j hj y p hp]
      rfl
    · simp

  · intro y hy x
    have he : (fun x => F (y,x)) = fun _ => (0:ℝ) := by
      funext q
      exact Finset.sum_eq_zero (fun i _ => hHzero i y hy q)
    change alpha (y,x) - fderiv ℝ (fun x => F (y,x)) x = 0
    rw [hy x,he,fderiv_const_apply,sub_self]

theorem exists_parametric_finite_circle_correction {ι : Type*} [Fintype ι]
    {alpha : P × Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (hac : HasCompactSupport alpha) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hRi : Injective R)
    (hz : ∀ i y, (∫ p in roundDisk (R i), planarCurl (fun x => alpha (y,x)) p) = 0) :
    ∃ beta : P × Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      (∀ y p, planarCurl (fun x => beta (y,x)) p = planarCurl (fun x => alpha (y,x)) p) ∧
      (∀ i y p, radiusSq p = (R i)^2 → beta (y,p) (-p.2,p.1) = 0) ∧
      ∀ y, (∀ x, alpha (y,x) = 0) → ∀ x, beta (y,x) = 0 := by
  classical
  choose d hd hdR hdsep using exists_disjoint_radial_collars R hR hRi
  choose H hHs hHc hHspt hHt hHzero using fun i =>
    exists_parametric_circle_primitive ha hac (hR i) (hd i) (hdR i) (hz i)
  apply parametric_finite_potential_correction ha hac R H hHs hHc
      (hHzero := hHzero)
  · intro i y p hp
    obtain ⟨t,rfl⟩ := polar_surjective_circle (hR i) hp
    simpa only [circlePullback,polarCoord_symm_apply,neg_mul] using hHt i y t
  · intro i j hj y p hp
    apply fderiv_zero_outside_collar (hHspt j y)
    rw [hp]
    exact hdsep j i hj.symm

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem fixedStep_affine {L M : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (Y : C(F,F)) (hY : LipschitzWith M Y) (A : E →L[ℝ] F) (b : F)
    (hXY : ∀ x, Y (b+A x) = A (X x))
    {h : ℝ} (hhX : ‖h‖*L < 1) (hhY : ‖h‖*M < 1) (x : E) :
    fixedStep Y hY h (b+A x) =
      ⟨fun s => b+A (fixedStep X hX h x s),
        continuous_const.add (A.continuous.comp (fixedStep X hX h x).continuous)⟩ := by
  let u := fixedStep X hX h x
  let q : C(Time,F) := ⟨fun s => b+A (u s),continuous_const.add (A.continuous.comp u.continuous)⟩
  change fixedStep Y hY h (b+A x) = q
  apply (picard_contracts Y hY (p := (b+A x,h)) hhY).fixedPoint_unique'
    (localPath_fixed Y hY (p := (b+A x,h)) hhY)
  apply ContinuousMap.ext
  intro s
  have hu := congrArg (fun v : C(Time,E) => v s) (fixedStep_equation X hX hhX x)
  have hq : (fun t : ℝ => extendPath (Y.comp q) t) =
      fun t => A (extendPath (X.comp u) t) := by
    funext t
    exact hXY _
  have hi := A.intervalIntegral_comp_comm (μ := volume)
    ((extendPath (X.comp u)).continuous.intervalIntegrable 0 (s:ℝ))
  change b+A x + h • (∫ t in 0..(s:ℝ), extendPath (Y.comp q) t) = b+A (u s)
  rw [hq,hi]
  change u s = x + h • (∫ t in 0..(s:ℝ), extendPath (X.comp u) t) at hu
  rw [hu,map_add,map_smul]
  simp only [add_assoc]

theorem stepEndpoint_affine {L M : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (Y : C(F,F)) (hY : LipschitzWith M Y) (A : E →L[ℝ] F) (b : F)
    (hXY : ∀ x, Y (b+A x) = A (X x))
    {h : ℝ} (hhX : ‖h‖*L < 1) (hhY : ‖h‖*M < 1) (x : E) :
    stepEndpoint Y hY h (b+A x) = b+A (stepEndpoint X hX h x) := by
  exact congrArg (fun u : C(Time,F) => u ⟨1,by simp⟩)
    (fixedStep_affine X hX Y hY A b hXY hhX hhY x)

end

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def parameterField (X : C(ℝ × (P × E),E)) : C(ℝ × (P × E),P × E) :=
  ⟨fun p => (0,X p),continuous_const.prodMk X.continuous⟩

def fiberField (X : C(ℝ × (P × E),E)) (y : P) : C(ℝ × E,E) :=
  ⟨fun p => X (p.1,(y,p.2)),X.continuous.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))⟩

omit [NormedSpace ℝ P] [CompleteSpace P] [NormedSpace ℝ E] [CompleteSpace E] in
theorem parameterField_lipschitz {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) : LipschitzWith L (parameterField X) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [parameterField,ContinuousMap.coe_mk,Prod.dist_eq,dist_self,
    max_eq_right dist_nonneg] using hX.dist_le_mul p q

omit [NormedSpace ℝ P] [CompleteSpace P] [NormedSpace ℝ E] [CompleteSpace E] in
theorem fiberField_lipschitz {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) (y : P) : LipschitzWith L (fiberField X y) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [fiberField,ContinuousMap.coe_mk,Prod.dist_eq,dist_self,
    max_eq_right dist_nonneg] using hX.dist_le_mul (p.1,(y,p.2)) (q.1,(y,q.2))

omit [CompleteSpace P] [CompleteSpace E] in
theorem parameterField_smooth (X : C(ℝ × (P × E),E)) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (parameterField X) := contDiff_const.prodMk hX

omit [CompleteSpace P] [CompleteSpace E] in
theorem fiberField_smooth (X : C(ℝ × (P × E),E)) (hX : ContDiff ℝ ∞ X) (y : P) :
    ContDiff ℝ ∞ (fiberField X y) :=
  hX.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))

theorem timeStep_fiber {L : ℝ≥0} (X : C(ℝ × (P × E),E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖*L < 1) (t : ℝ) (y : P) (x : E) :
    timeStep (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX) h t (y,x) =
      (y,timeStep (fiberField X y) (fiberField_lipschitz X hX y) h t x) := by
  let A : (ℝ × E) →L[ℝ] (ℝ × (P × E)) :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod
      ((0 : (ℝ × E) →L[ℝ] P).prod (ContinuousLinearMap.snd ℝ ℝ E))
  let b : ℝ × (P × E) := (0,(y,0))
  have hXY : ∀ p, clockField (E := P × E) (parameterField X) (b+A p) =
      A (clockField (E := E) (fiberField X y) p) := by
    intro p
    simp only [b,A,ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd',zero_apply,Prod.mk_add_mk,
      zero_add,add_zero,clockField_apply,parameterField,fiberField,ContinuousMap.coe_mk]
  have he := stepEndpoint_affine (clockField (E := E) (fiberField X y))
    (clockField_lipschitz (E := E) (fiberField X y) (fiberField_lipschitz X hX y)) (clockField (E := P × E) (parameterField X))
    (clockField_lipschitz (E := P × E) (parameterField X) (parameterField_lipschitz X hX)) A b hXY hh hh (t,x)
  have he' := congrArg Prod.snd he
  simpa only [b,A,ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd',zero_apply,Prod.mk_add_mk,
    zero_add,add_zero,timeStep] using he'

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

theorem timeSteps_fiber {L : ℝ≥0} (X : C(ℝ × (P × E),E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖*L < 1) (t : ℝ) (N : ℕ) (y : P) (x : E) :
    timeSteps (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
        (parameterField_smooth X hXs) hh t N (y,x) =
      (y,timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
        (fiberField_smooth X hXs y) hh t N x) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change timeStep (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX) h (t+N*h)
      (timeSteps (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
        (parameterField_smooth X hXs) hh t N (y,x)) = _
    rw [ih,timeStep_fiber X hX hh]
    rfl

theorem timeSteps_fiber_smooth {L : ℝ≥0} (X : C(ℝ × (P × E),E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖*L < 1) (t : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (fun p : P × E => timeSteps (fiberField X p.1)
      (fiberField_lipschitz X hX p.1) (fiberField_smooth X hXs p.1) hh t N p.2) ∧
    ContDiff ℝ ∞ (fun p : P × E => (timeSteps (fiberField X p.1)
      (fiberField_lipschitz X hX p.1) (fiberField_smooth X hXs p.1) hh t N).symm p.2) := by
  let Φ := timeSteps (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
    (parameterField_smooth X hXs) hh t N
  let φ (y : P) := timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
    (fiberField_smooth X hXs y) hh t N
  have he (p : P × E) : Φ p = (p.1,φ p.1 p.2) := timeSteps_fiber X hX hXs hh t N p.1 p.2
  have hei (p : P × E) : Φ.symm p = (p.1,(φ p.1).symm p.2) := by
    apply Φ.injective
    rw [Φ.apply_symm_apply,he,(φ p.1).apply_symm_apply]
  have hs := timeSteps_smooth (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
    (parameterField_smooth X hXs) hh t N
  constructor
  · have hfun : (fun p : P × E => φ p.1 p.2) = fun p => (Φ p).2 :=
      funext fun p => (congrArg Prod.snd (he p)).symm
    change ContDiff ℝ ∞ (fun p : P × E => φ p.1 p.2)
    rw [hfun]
    exact hs.1.snd
  · have hfun : (fun p : P × E => (φ p.1).symm p.2) = fun p => (Φ.symm p).2 :=
      funext fun p => (congrArg Prod.snd (hei p)).symm
    change ContDiff ℝ ∞ (fun p : P × E => (φ p.1).symm p.2)
    rw [hfun]
    exact hs.2.snd

omit [NormedSpace ℝ P] [CompleteSpace P] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
theorem fiberField_compact (X : C(ℝ × (P × E),E)) (hc : HasCompactSupport X) (y : P) :
    HasCompactSupport (fiberField X y) := by
  apply HasCompactSupport.intro
    (hc.image (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  intro p hp
  change X (p.1,(y,p.2)) = 0
  exact image_eq_zero_of_notMem_tsupport (fun h => hp ⟨(p.1,(y,p.2)),h,rfl⟩)

theorem exists_parametric_density_transport {ι : Type*} {L : ℝ≥0}
    (X : C(ℝ × (P × Plane),Plane)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    (ρ : P → ℝ × Plane → ℝ) (hρ : ∀ y, ContDiff ℝ ∞ (ρ y))
    (B : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hPDE : ∀ y p v w, fderiv ℝ (ρ y) p (1,fiberField X y p) * B v w +
      ρ y p * (B (fderiv ℝ (fiberField X y) p (0,v)) w +
        B v (fderiv ℝ (fiberField X y) p (0,w))) = 0)
    (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (htan : ∀ i y t x, radiusSq x = (R i)^2 → radialDrift (fiberField X y) (t,x) = 0)
    (t T : ℝ) : ∃ Φ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (Φ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => Φ p.1 p.2 - p.2) ∧
      (∀ y x v w, ρ y (t+T,Φ y x) * B (fderiv ℝ (Φ y) x v) (fderiv ℝ (Φ y) x w) =
        ρ y (t,x) * B v w) ∧
      (∀ i y, Φ y '' closedRoundDisk (R i) = closedRoundDisk (R i)) ∧
      ∀ y, (∀ t x, X (t,(y,x)) = 0) → ∀ x, Φ y x = x := by
  obtain ⟨N,hN⟩ := exists_nat_gt (‖T‖ * L)
  have hN0 : (0:ℝ) < N := (mul_nonneg (norm_nonneg _) L.coe_nonneg).trans_lt hN
  let h := T / N
  have hh : ‖h‖ * L < 1 := by
    change ‖T/(N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le,div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr hN
  have he : (N:ℝ) * h = T := by dsimp [h]; field_simp
  let Φ (y : P) := timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
    (fiberField_smooth X hXs y) hh t N
  have hK : IsCompact (Prod.snd '' tsupport X) := hXc.image continuous_snd
  have hfix (p : P × Plane) (hp : p ∉ Prod.snd '' tsupport X) : Φ p.1 p.2 = p.2 := by
    apply timeSteps_of_stationary
    intro s
    change X (s,p) = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hp ⟨(s,p),h,rfl⟩)
  refine ⟨Φ,(timeSteps_fiber_smooth X hX hXs hh t N).1,
    (timeSteps_fiber_smooth X hX hXs hh t N).2,
    HasCompactSupport.intro hK (fun p hp => sub_eq_zero.mpr (hfix p hp)),?_,?_,?_⟩
  · intro y x v w
    simpa only [he] using timeSteps_preserves_density (fiberField X y)
      (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y)
      (ρ y) (hρ y) B (hPDE y) hh t N x v w
  · intro i y
    apply homeomorph_image_closedRoundDisk
    intro x
    exact timeSteps_preserves_circle_iff (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) (fiberField_compact X hXc y) (hR i) (htan i y) hh t N x

  · intro y hy x
    apply timeSteps_of_stationary
    intro s
    exact hy s x

end PackingSufficiencySupport.Hamiltonian
end

end OAI
