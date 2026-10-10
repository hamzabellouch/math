import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevSmoothTests
import OAI.Analysis.Conductivity.Variational.L2TranslationAverage

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
open scoped Convolution

abbrev SpatialBump := ContDiffBump (0:R3)

def bumpProbability (φ : SpatialBump) : Measure R3 :=
  volume.withDensity (fun x => ENNReal.ofReal (φ.normed volume x))

instance bumpProbability_isProbability (φ : SpatialBump) : IsProbabilityMeasure (bumpProbability φ) where
  measure_univ := by
    rw [bumpProbability,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal φ.integrable_normed (ae_of_all _ φ.nonneg_normed),φ.integral_normed]
    simp

lemma bumpProbability_integral (φ : SpatialBump) (f : R3 → ℝ) :
    (∫ y, f y ∂bumpProbability φ)=∫ y, φ.normed volume y*f y := by
  rw [bumpProbability,integral_withDensity_eq_integral_toReal_smul
    φ.continuous_normed.measurable.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _),smul_eq_mul]

lemma bumpProbability_ball (φ : SpatialBump) :
    ∀ᵐ y ∂bumpProbability φ, ‖y‖<φ.rOut := by
  rw [bumpProbability,ae_withDensity_iff φ.continuous_normed.measurable.ennreal_ofReal]
  filter_upwards with y hy
  have hne : φ.normed volume y≠0 := fun h => hy (by rw [h]; simp)
  have hs : y∈Function.support (φ.normed volume) := hne
  rw [φ.support_normed_eq] at hs
  simpa using hs

def mollifyReal (φ : SpatialBump) (f : R3 → ℝ) : R3 → ℝ :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f

lemma mollifyReal_smooth (φ : SpatialBump) {f : R3 → ℝ} (hf : LocallyIntegrable f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (mollifyReal φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed hf

lemma mollifyReal_eq_average (φ : SpatialBump) (f : R3 → ℝ) (x : R3) :
    mollifyReal φ f x=∫ y, f (x-y) ∂bumpProbability φ := by
  rw [bumpProbability_integral]
  rfl

lemma mollifyReal_sub (φ : SpatialBump) (f : WholeL2) (x : R3) :
    mollifyReal φ f x-f x=∫ y, (f (x-y)-f x) ∂bumpProbability φ := by
  rw [bumpProbability_integral]
  simp_rw [mul_sub]
  have hi : Integrable (fun y => φ.normed volume y*f (x-y)) :=
    φ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      φ.continuous_normed ((Lp.memLp f).locallyIntegrable (by norm_num)) x
  rw [integral_sub hi (φ.integrable_normed.mul_const _),integral_mul_const,φ.integral_normed,one_mul]
  rfl

lemma mollifyReal_memLp (φ : SpatialBump) (f : WholeL2) : MemLp (mollifyReal φ f) 2 volume := by
  obtain ⟨hm,_⟩ := memLp_probability_average (whole_translation_memLp (μ := bumpProbability φ) f)
  exact MemLp.ae_eq (ae_of_all _ (fun x => (mollifyReal_eq_average φ f x).symm)) hm

theorem mollifyReal_approx (f : WholeL2) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ φ : SpatialBump, φ.rOut≤δ →
      (∫ x, (mollifyReal φ f x-f x)^2) ≤ ε := by
  obtain ⟨δ,hδ,hd⟩ := small_translation_radius f hε
  refine ⟨δ,hδ,fun φ hφ => ?_⟩
  obtain ⟨_,he⟩ := translation_average_sq_le (μ := bumpProbability φ) f
    (show ∀ᵐ y ∂bumpProbability φ, ‖translateL2 y f-f‖^2≤ε from by
      filter_upwards [bumpProbability_ball φ] with y hy
      exact (hd y (hy.trans_le hφ)).le)
  simpa only [mollifyReal_sub] using he

def WeakL2Direction (f g : R3 → ℝ) (v : R3) : Prop :=
  ∀ ψ : R3 → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
    (∫ x, f x*fderiv ℝ ψ x v) = -(∫ x, g x*ψ x)

lemma mollifyReal_fderiv_eq {f : R3 → ℝ} (hf : LocallyIntegrable f)
    (φ : SpatialBump) (x v : R3) :
    fderiv ℝ (mollifyReal φ f) x v=
      ∫ y, fderiv ℝ (φ.normed volume) (x-y) v*f y := by
  let L : (R3 →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ] (R3 →L[ℝ] ℝ) := ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)
  have hc : HasCompactSupport (fderiv ℝ (φ.normed volume)) :=
    φ.hasCompactSupport_normed.fderiv ℝ
  have hκ : ContDiff ℝ (↑(⊤ : ℕ∞)) (φ.normed volume) := φ.contDiff_normed
  have hd : Continuous (fderiv ℝ (φ.normed volume)) :=
    hκ.continuous_fderiv (by simp)
  have hi : Integrable (fun y => L (fderiv ℝ (φ.normed volume) (x-y)) (f y)) :=
    (hc.convolutionExists_left L hd hf x).integrable_swap
  have hder := φ.hasCompactSupport_normed.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (hκ.of_le (by simp)) hf x
  change fderiv ℝ ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f) x v=_
  rw [hder.fderiv,convolution_eq_swap,ContinuousLinearMap.integral_apply hi]
  rfl

lemma mollifyReal_direction {f g : R3 → ℝ} (hf : MemLp f 2 volume)
    (_ : MemLp g 2 volume) (v : R3) (hw : WeakL2Direction f g v)
    (φ : SpatialBump) (x : R3) :
    fderiv ℝ (mollifyReal φ f) x v=mollifyReal φ g x := by
  let κ := φ.normed volume
  have hκ : ContDiff ℝ (↑(⊤ : ℕ∞)) κ := φ.contDiff_normed
  have hκc : HasCompactSupport κ := φ.hasCompactSupport_normed
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : R3 => κ (x-y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y : R3 => κ (x-y)) :=
    hκc.comp_homeomorph (Homeomorph.subLeft x)
  have hdψ (y : R3) : fderiv ℝ (fun z : R3 => κ (x-z)) y v=
      -(fderiv ℝ κ (x-y) v) := by
    have hh := ((hκ.differentiable (by simp)) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change fderiv ℝ (κ ∘ (fun z : R3 => x-z)) y v=_
    rw [hh.fderiv]
    simp
  have he := hw _ hψ hψc
  simp_rw [hdψ,mul_neg,integral_neg] at he
  have he' : (∫ y, fderiv ℝ κ (x-y) v*f y)=∫ y, g y*κ (x-y) := by
    simpa only [mul_comm,neg_inj] using he
  rw [mollifyReal_fderiv_eq (hf.locallyIntegrable (by norm_num)),he']
  unfold mollifyReal
  rw [convolution_eq_swap]
  congr 1
  ext y
  simp [κ,mul_comm]

lemma mollifyReal_zero_outside {f : R3 → ℝ} {R : ℝ}
    (hf : ∀ᵐ y, R<‖y‖ → f y=0) (φ : SpatialBump) {x : R3}
    (hx : R+φ.rOut<‖x‖) : mollifyReal φ f x=0 := by
  unfold mollifyReal
  rw [convolution_eq_swap]
  apply integral_eq_zero_of_ae
  filter_upwards [hf] with y hy
  change φ.normed volume (x-y)*f y=0
  by_cases hf' : f y=0
  · rw [hf',mul_zero]
  · have hR : ‖y‖≤R := le_of_not_gt (fun h => hf' (hy h))
    have hn : φ.rOut<‖x-y‖ := by
      have ht : ‖x‖≤‖x-y‖+‖y‖ := by simpa using norm_add_le (x-y) y
      linarith
    have hκ : φ.normed volume (x-y)=0 := by
      apply Function.notMem_support.mp
      rw [φ.support_normed_eq,Metric.mem_ball,dist_zero_right]
      exact not_lt.mpr hn.le
    rw [hκ,zero_mul]

lemma mollifyReal_support {f : R3 → ℝ} {R : ℝ}
    (hf : ∀ᵐ y, R<‖y‖ → f y=0) (φ : SpatialBump) :
    tsupport (mollifyReal φ f)⊆Metric.closedBall 0 (R+φ.rOut) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (mollifyReal_zero_outside hf φ hn))

lemma mollifyReal_compact {f : R3 → ℝ} {R : ℝ}
    (hf : ∀ᵐ y, R<‖y‖ → f y=0) (φ : SpatialBump) :
    HasCompactSupport (mollifyReal φ f) :=
  (isCompact_closedBall (0:R3) (R+φ.rOut)).of_isClosed_subset (isClosed_tsupport _)
    (mollifyReal_support hf φ)

end

open Set MeasureTheory Filter Topology

def dyadicBump (n : ℕ) : SpatialBump where
  rIn := (1/2:ℝ)^(n+1)
  rOut := (1/2:ℝ)^n
  rIn_pos := by positivity
  rIn_lt_rOut := by
    rw [pow_succ]
    have h : 0<(1/2:ℝ)^n := by positivity
    linarith

lemma dyadicBump_radius : Tendsto (fun n => (dyadicBump n).rOut) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

def mollifyL2 (φ : SpatialBump) (f : WholeL2) : WholeL2 :=
  (mollifyReal_memLp φ f).toLp _

lemma mollifyL2_ae (φ : SpatialBump) (f : WholeL2) :
    (mollifyL2 φ f : R3 → ℝ) =ᵐ[volume] mollifyReal φ f :=
  (mollifyReal_memLp φ f).coeFn_toLp

lemma mollifyL2_norm_sq (φ : SpatialBump) (f : WholeL2) :
    ‖mollifyL2 φ f-f‖^2=∫ x, (mollifyReal φ f x-f x)^2 := by
  rw [wholeL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (mollifyL2 φ f) f,mollifyL2_ae φ f] with x hx hy
  simp only [hx,Pi.sub_apply,hy]

lemma mollifyL2_tendsto (f : WholeL2) :
    Tendsto (fun n => mollifyL2 (dyadicBump n) f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := mollifyReal_approx f (show 0<ε^2/2 by positivity)
  have he : ∀ᶠ n in atTop, (dyadicBump n).rOut<δ :=
    dyadicBump_radius.eventually (gt_mem_nhds hδ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hh : ‖mollifyL2 (dyadicBump n) f-f‖^2≤ε^2/2 := by
    rw [mollifyL2_norm_sq]
    exact hd _ (hN n hn).le
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (mollifyL2 (dyadicBump n) f-f)]

abbrev WholeJetSpace := Lp JetFiber 2 (volume : Measure R3)

def jetCoordinateL (i : Fin 4) : ℝ →L[ℝ] JetFiber :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)

lemma jetCoordinateL_apply (i : Fin 4) (r : ℝ) (j : Fin 4) :
    jetCoordinateL i r j=if j=i then r else 0 := by
  simp [jetCoordinateL,eq_comm]

def wholeJet (F : Fin 4 → WholeL2) : WholeJetSpace :=
  ∑ i, (jetCoordinateL i).compLpL 2 volume (F i)

lemma wholeJet_ae (F : Fin 4 → WholeL2) :
    ∀ᵐ x, ∀ i, wholeJet F x i=F i x := by
  have hc : ∀ᵐ x, ∀ i, ((jetCoordinateL i).compLpL 2 volume (F i)) x=jetCoordinateL i (F i x) :=
    ae_all_iff.mpr (fun i => (jetCoordinateL i).coeFn_compLp (F i))
  filter_upwards [hc,Lp.coeFn_finsetSum Finset.univ
    (fun i => (jetCoordinateL i).compLpL 2 volume (F i))] with x hx hy
  intro j
  change (∑ i, (jetCoordinateL i).compLpL 2 volume (F i)) x j=F j x
  rw [hy]
  simp only [Finset.sum_apply,hx]
  change (∑ i, jetCoordinateL i (F i x) j)=F j x
  simp only [jetCoordinateL_apply]
  simp

lemma wholeJet_continuous : Continuous wholeJet := by
  unfold wholeJet
  apply continuous_finsetSum
  intro i _
  exact ((jetCoordinateL i).compLpL 2 volume).continuous.comp (continuous_apply i)

def ballJet (F : Fin 4 → WholeL2) : JetSpace :=
  LpToLpRestrictCLM R3 JetFiber ℝ volume 2 ball (wholeJet F)

lemma ballJet_ae (F : Fin 4 → WholeL2) :
    ∀ᵐ x ∂ballMeasure, ∀ i, ballJet F x i=F i x := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ ball (wholeJet F),
    (wholeJet_ae F).filter_mono (ae_mono Measure.restrict_le_self)] with x hx hy
  intro i
  exact congrArg (fun z : JetFiber => z i) hx |>.trans (hy i)

lemma ballJet_continuous : Continuous ballJet :=
  (LpToLpRestrictCLM R3 JetFiber ℝ volume 2 ball).continuous.comp wholeJet_continuous

lemma ballJet_mollify_tendsto (F : Fin 4 → WholeL2) :
    Tendsto (fun n => ballJet (fun i => mollifyL2 (dyadicBump n) (F i))) atTop (𝓝 (ballJet F)) :=
  ballJet_continuous.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun i => mollifyL2_tendsto (F i)))

lemma mollifiedJet_eq (F : Fin 4 → WholeL2)
    (hw : ∀ i : Fin 3, WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1))
    (φ : SpatialBump) :
    ballJet (fun i => mollifyL2 φ (F i))=
      (smoothH1 (mollifyReal φ (F 0))
        (mollifyReal_smooth φ ((Lp.memLp (F 0)).locallyIntegrable (by norm_num)))).val := by
  apply Lp.ext
  have hma : ∀ᵐ x ∂ballMeasure, ∀ i : Fin 4,
      mollifyL2 φ (F i) x=mollifyReal φ (F i) x :=
    (ae_all_iff.mpr (fun i => mollifyL2_ae φ (F i))).filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [ballJet_ae (fun i => mollifyL2 φ (F i)),hma,
    (smoothJet_memLp (mollifyReal_smooth φ
      ((Lp.memLp (F 0)).locallyIntegrable (by norm_num)))).coeFn_toLp] with x hx hy hz
  change _ = (smoothJet_memLp (mollifyReal_smooth φ
    ((Lp.memLp (F 0)).locallyIntegrable (by norm_num)))).toLp _ x
  rw [hz]
  ext i
  rw [hx i,hy i]
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change mollifyReal φ (F j.succ) x=gradient (mollifyReal φ (F 0)) x j
    have hd := mollifyReal_direction (Lp.memLp (F 0)) (Lp.memLp (F j.succ))
      (EuclideanSpace.single j 1) (hw j) φ x
    have he : inner ℝ (EuclideanSpace.single j 1) (gradient (mollifyReal φ (F 0)) x)=
        fderiv ℝ (mollifyReal φ (F 0)) x (EuclideanSpace.single j 1) := by
      simp only [inner_gradient_right,RCLike.conj_to_real]
    simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul]
      using (he.trans hd).symm

theorem compact_weakJet_mem_zeroTrace (F : Fin 4 → WholeL2)
    (hw : ∀ i : Fin 3, WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1))
    {R : ℝ} (hR : R<3) (hs : ∀ᵐ x, R<‖x‖ → F 0 x=0) :
    ballJet F∈zeroTraceAmbient := by
  apply (Submodule.isClosed_topologicalClosure (Submodule.span ℝ compactSmoothJets)).mem_of_tendsto
    (ballJet_mollify_tendsto F)
  have he : ∀ᶠ n in atTop, (dyadicBump n).rOut<3-R :=
    dyadicBump_radius.eventually (gt_mem_nhds (by linarith))
  filter_upwards [he] with n hn
  rw [mollifiedJet_eq F hw]
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨mollifyReal (dyadicBump n) (F 0),
    mollifyReal_smooth _ ((Lp.memLp (F 0)).locallyIntegrable (by norm_num)),
    mollifyReal_compact hs _,?_,smoothJet_memLp (mollifyReal_smooth _
      ((Lp.memLp (F 0)).locallyIntegrable (by norm_num))),rfl⟩
  intro x hx
  have hb := mollifyReal_support hs (dyadicBump n) hx
  change ‖x-0‖<3
  rw [sub_zero]
  have hh : ‖x‖≤R+(dyadicBump n).rOut := by simpa using hb
  linarith

lemma zeroTraceAmbient_le_H1Space : zeroTraceAmbient≤H1Space := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro z ⟨f,hf,hc,hs,hm,hz⟩
  exact ⟨f,hf,hm,hz⟩

theorem compact_weak_H1 (F : Fin 4 → WholeL2)
    (hw : ∀ i : Fin 3, WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1))
    {R : ℝ} (hR : R<3) (hs : ∀ᵐ x, R<‖x‖ → F 0 x=0) :
    ∃ u : H1, u∈H10 ∧
      (∀ᵐ x ∂ballMeasure, weakValue u x=F 0 x ∧ ∀ i : Fin 3, weakGradient u x i=F i.succ x) := by
  have hz := compact_weakJet_mem_zeroTrace F hw hR hs
  let u : H1 := ⟨ballJet F,zeroTraceAmbient_le_H1Space hz⟩
  refine ⟨u,hz,?_⟩
  filter_upwards [ballJet_ae F] with x hx
  exact ⟨hx 0,fun i => hx i.succ⟩

end ScalarConductivity

end

end OAI
