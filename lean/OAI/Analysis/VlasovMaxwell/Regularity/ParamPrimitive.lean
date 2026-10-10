import Mathlib
import OAI.Analysis.VlasovMaxwell.Maxwell.WaveK

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma hasFDerivAt_intervalIntegral
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ 1 F) (a b : ℝ) (p : H) :
    HasFDerivAt (fun x => ∫ s in a..b, F (x,s))
      (∫ s in a..b, (fderiv ℝ F (p,s)).comp (ContinuousLinearMap.inl ℝ H ℝ)) p := by
  let D : H × ℝ → H →L[ℝ] W := fun z =>
    (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H ℝ)
  have hD : Continuous D := (hF.continuous_fderiv (by simp)).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod isCompact_uIcc).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s:=closedBall p 1) (bound:=fun _ => C) (F':=fun x s => D (x,s))
    (closedBall_mem_nhds p (by norm_num))
  · exact Eventually.of_forall (fun x => (hF.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    intro x hx
    exact hC _ ⟨(x,s),⟨hx,uIoc_subset_uIcc hs⟩,rfl⟩
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun s x _ => (hF.differentiable (by simp) (x,s)).hasFDerivAt.comp x
      (by convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const s x) using 1 <;> rfl))

lemma contDiff_intervalIntegral_nat
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    (k : ℕ) : ∀ {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W}, ContDiff ℝ ∞ F → ∀ a b,
      ContDiff ℝ k (fun x => ∫ s in a..b, F (x,s)) := by
  induction k with
  | zero =>
    intro W _ _ _ F hF a b
    have hd : Differentiable ℝ (fun x => ∫ s in a..b, F (x,s)) :=
      fun x => (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) a b x).differentiableAt
    exact contDiff_zero.mpr hd.continuous
  | succ k ih =>
    intro W _ _ _ F hF a b
    let D : H × ℝ → H →L[ℝ] W := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H ℝ)
    have hD : ContDiff ℝ ∞ D :=
      (contDiff_infty_iff_fderiv.mp hF).2.clm_comp contDiff_const
    have he : fderiv ℝ (fun x => ∫ s in a..b, F (x,s)) =
        (fun x => ∫ s in a..b, D (x,s)) := by
      funext x
      exact (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) a b x).fderiv
    rw [show (↑(k+1) : ℕ∞ω) = ↑k+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) a b x).differentiableAt,?_,?_⟩
    · simp
    · rw [he]
      exact ih hD a b

lemma contDiff_intervalIntegral
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ s in a..b, F (x,s)) := by
  rw [contDiff_infty]
  intro k
  exact contDiff_intervalIntegral_nat k hF a b

def paramPrimitive {H W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : H × ℝ → W) (p : ℝ × H) : W := ∫ s in 0..p.1, F (p.2,s)

lemma paramPrimitive_scale {H W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : H × ℝ → W) (p : ℝ × H) :
    paramPrimitive F p = p.1 • ∫ u in (0:ℝ)..1, F (p.2,p.1*u) := by
  simpa [paramPrimitive] using (intervalIntegral.smul_integral_comp_mul_left (fun s => F (p.2,s)) p.1
    (a:=0) (b:=1)).symm

lemma contDiff_paramPrimitive
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (paramPrimitive F) := by
  have he : paramPrimitive F = fun p => p.1 • ∫ u in (0:ℝ)..1, F (p.2,p.1*u) :=
    funext (paramPrimitive_scale F)
  rw [he]
  apply contDiff_fst.smul
  apply contDiff_intervalIntegral (F:=fun z : (ℝ × H) × ℝ => F (z.1.2,z.1.1*z.2))
  exact hF.comp ((contDiff_snd.comp contDiff_fst).prodMk
    ((contDiff_fst.comp contDiff_fst).mul contDiff_snd))

lemma paramPrimitive_fderiv_apply
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ ∞ F) (t : ℝ) (p : H) (dt : ℝ) (dp : H) :
    fderiv ℝ (paramPrimitive F) (t,p) (dt,dp) =
      dt • F (p,t) + (∫ s in 0..t, (fderiv ℝ F (p,s)).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) dp := by
  have hJ : Differentiable ℝ (paramPrimitive F) := (contDiff_paramPrimitive hF).differentiable (by simp)
  have htime := (hJ (t,p)).hasFDerivAt.comp t
    ((hasFDerivAt_id (𝕜:=ℝ) t).prodMk (hasFDerivAt_const (𝕜:=ℝ) p t))
  have hc : Continuous (fun s => F (p,s)) := hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hFTC := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have ht : fderiv ℝ (paramPrimitive F) (t,p) (1,0) = F (p,t) := by
    exact htime.hasDerivAt.unique hFTC
  have hparam := (hJ (t,p)).hasFDerivAt.comp p
    ((hasFDerivAt_const (𝕜:=ℝ) t p).prodMk (hasFDerivAt_id (𝕜:=ℝ) p))
  have hp := hparam.unique (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) 0 t p)
  have hp' := congrArg (fun L : H →L[ℝ] W => L dp) hp
  change fderiv ℝ (paramPrimitive F) (t,p) (0,dp) = _ at hp'
  rw [show (dt,dp) = dt • (1,0) + (0,dp) by simp,map_add,map_smul,ht,hp']

def dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (F : H → W) (e x : H) : W :=
  fderiv ℝ F x e

lemma contDiff_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e : H) : ContDiff ℝ ∞ (dirD F e) :=
  (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

lemma dirD_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e v x : H) :
    dirD (dirD F e) v x = fderiv ℝ (fderiv ℝ F) x v e := by
  unfold dirD
  rw [fderiv_clm_apply ((contDiff_infty_iff_fderiv.mp hF).2.differentiable (by simp) x)
    (differentiableAt_const e)]
  simp

lemma dirD_comm {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e v x : H) :
    dirD (dirD F e) v x = dirD (dirD F v) e x := by
  rw [dirD_dirD hF,dirD_dirD hF]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq v e

lemma dirD_clm_comp {G H W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : H → W} (hF : Differentiable ℝ F) (L : G →L[ℝ] H) (e x : G) :
    dirD (fun y => F (L y)) e x = dirD F (L e) (L x) := by
  unfold dirD
  have h := (hF (L x)).hasFDerivAt.comp x L.hasFDerivAt
  change HasFDerivAt (fun y => F (L y)) _ x at h
  rw [h.fderiv]
  rfl

lemma deriv_slice_eq_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × H → W}
    (hF : Differentiable ℝ F) (t : ℝ) (x : H) :
    deriv (fun r => F (r,x)) t = dirD F (1,0) (t,x) := by
  exact ((hF (t,x)).hasFDerivAt.comp t
    ((hasFDerivAt_id (𝕜:=ℝ) t).prodMk (hasFDerivAt_const (𝕜:=ℝ) x t))).hasDerivAt.deriv

lemma deriv_deriv_slice_eq_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × H → W}
    (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : H) :
    deriv (deriv (fun r => F (r,x))) t = dirD (dirD F (1,0)) (1,0) (t,x) := by
  have he : deriv (fun r => F (r,x)) = fun r => dirD F (1,0) (r,x) := by
    funext r
    exact deriv_slice_eq_dirD (hF.differentiable (by simp)) r x
  rw [he]
  exact deriv_slice_eq_dirD ((contDiff_dirD hF (1,0)).differentiable (by simp)) t x

lemma dirD_prod_left {H G W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : H × G → W} (hF : Differentiable ℝ F) (e x : H) (y : G) :
    dirD (fun z => F (z,y)) e x = dirD F (e,0) (x,y) := by
  have h := (hF (x,y)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (𝕜:=ℝ) y x))
  change HasFDerivAt (fun z => F (z,y)) _ x at h
  unfold dirD
  rw [h.fderiv]
  simp

def volterra {H : Type*} (F : (ℝ × H) × ℝ → ℝ) (p : ℝ × H) : ℝ :=
  ∫ s in 0..p.1, F (p,s)

lemma contDiff_volterra {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    {F : (ℝ × H) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (volterra F) :=
  (contDiff_paramPrimitive hF).comp (contDiff_fst.prodMk contDiff_id)

lemma dirD_volterra {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    {F : (ℝ × H) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (e p : ℝ × H) :
    dirD (volterra F) e p = e.1*F (p,p.1) + volterra (dirD F (e,0)) p := by
  have h := ((contDiff_paramPrimitive hF).differentiable (by simp) (p.1,p)).hasFDerivAt.comp (f:=fun z : ℝ × H => (z.1,z)) p
    (((hasFDerivAt_id (𝕜:=ℝ) p).fst).prodMk (hasFDerivAt_id (𝕜:=ℝ) p))
  change HasFDerivAt (volterra F) _ p at h
  unfold dirD
  rw [h.fderiv]
  change fderiv ℝ (paramPrimitive F) (p.1,p) (e.1,e) = _
  rw [paramPrimitive_fderiv_apply hF]
  congr 1
  have hc : Continuous (fun s => (fderiv ℝ F (p,s)).comp
      (ContinuousLinearMap.inl ℝ (ℝ × H) ℝ)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 p.1)]
  rfl

lemma spatialPartial_eq_dirD (g : Vec → ℝ) (x : Vec) (i : Fin 3) :
    spatialPartial g x i = dirD g (basis i) x := rfl

lemma laplace_slice_eq_dirD {F : ℝ × Vec → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : Vec) :
    laplace (fun y => F (t,y)) x =
      ∑ i : Fin 3, dirD (dirD F (0,basis i)) (0,basis i) (t,x) := by
  rw [laplace_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => spatialPartial (fun z => F (t,z)) y i) =
      fun y => dirD F (0,basis i) (t,y) := by
    funext y
    exact spatialPartial_time_slice (hF.differentiable (by simp) (t,y)) i
  rw [he]
  exact spatialPartial_time_slice ((contDiff_dirD hF (0,basis i)).differentiable (by simp) (t,x)) i

lemma laplace_volterra {F : (ℝ × Vec) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : Vec) :
    laplace (fun y => volterra F (t,y)) x =
      ∫ s in 0..t, laplace (fun y => F ((t,y),s)) x := by
  rw [laplace_slice_eq_dirD (contDiff_volterra hF)]
  have he (i : Fin 3) : dirD (volterra F) (0,basis i) =
      volterra (dirD F ((0,basis i),0)) := by
    funext p
    simpa only [zero_mul,zero_add] using dirD_volterra hF (0,basis i) p
  simp_rw [he]
  have he' (i : Fin 3) : dirD (volterra (dirD F ((0,basis i),0))) (0,basis i) (t,x) =
      volterra (dirD (dirD F ((0,basis i),0)) ((0,basis i),0)) (t,x) := by
    simpa only [zero_mul,zero_add] using
      dirD_volterra (contDiff_dirD hF ((0,basis i),0)) (0,basis i) (t,x)
  simp_rw [he']
  have hc (i : Fin 3) : Continuous (fun s => dirD (dirD F ((0,basis i),0))
      ((0,basis i),0) ((t,x),s)) :=
    (contDiff_dirD (contDiff_dirD hF _) _).continuous.comp (continuous_const.prodMk continuous_id)
  rw [show (∑ i : Fin 3, volterra (dirD (dirD F ((0,basis i),0)) ((0,basis i),0)) (t,x)) =
      ∫ s in 0..t, ∑ i : Fin 3, dirD (dirD F ((0,basis i),0)) ((0,basis i),0) ((t,x),s) by
        exact (intervalIntegral.integral_finsetSum (fun i _ => (hc i).intervalIntegrable 0 t)).symm]
  apply intervalIntegral.integral_congr
  intro s _
  have hFs : ContDiff ℝ ∞ (fun p => F (p,s)) := hF.comp (contDiff_id.prodMk contDiff_const)
  change _ = laplace (fun y => F ((t,y),s)) x
  rw [laplace_slice_eq_dirD hFs]
  apply Finset.sum_congr rfl
  intro i _
  have hf := hF.differentiable (by simp)
  have hdir : dirD (fun z => F (z,s)) (0,basis i) =
      fun p => dirD F ((0,basis i),0) (p,s) := by
    funext p
    exact dirD_prod_left hf _ p s
  rw [hdir,dirD_prod_left ((contDiff_dirD hF _).differentiable (by simp))]

def sourceWaveKernel (ρ : ℝ × Vec → ℝ) (z : (ℝ × Vec) × ℝ) : ℝ :=
  waveK (fun y => ρ (z.2,y)) (z.1.1-z.2,z.1.2)

def sourceWave (ρ : ℝ × Vec → ℝ) : ℝ × Vec → ℝ := volterra (sourceWaveKernel ρ)

lemma contDiff_sourceWaveKernel {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (sourceWaveKernel ρ) := by
  have hF : ContDiff ℝ ∞ (fun z : ((ℝ × Vec) × ℝ) × Vec =>
      ρ (z.1.2,z.1.1.2+(z.1.1.1-z.1.2) • z.2)) := by
    apply hρ.comp
    apply (contDiff_snd.comp contDiff_fst).prodMk
    apply (contDiff_snd.comp (contDiff_fst.comp contDiff_fst)).add
    exact ((contDiff_fst.comp (contDiff_fst.comp contDiff_fst)).sub
      (contDiff_snd.comp contDiff_fst)).smul contDiff_snd
  exact contDiff_const.mul (((contDiff_fst.comp contDiff_fst).sub contDiff_snd).mul
    (contDiff_integral_sphere hF))

lemma contDiff_sourceWave {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (sourceWave ρ) := contDiff_volterra (contDiff_sourceWaveKernel hρ)

lemma sourceWaveKernel_boundary (ρ : ℝ × Vec → ℝ) (p : ℝ × Vec) :
    sourceWaveKernel ρ (p,p.1) = 0 := by
  simp [sourceWaveKernel,waveK]

lemma sourceWave_timeDerivative {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    dirD (sourceWave ρ) (1,0) = volterra (dirD (sourceWaveKernel ρ) ((1,0),0)) := by
  funext p
  simpa only [sourceWave,one_mul,sourceWaveKernel_boundary,zero_add] using
    dirD_volterra (contDiff_sourceWaveKernel hρ) (1,0) p

lemma sourceWaveKernel_timeDerivative {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (t s : ℝ) (x : Vec) :
    dirD (sourceWaveKernel ρ) ((1,0),0) ((t,x),s) =
      deriv (fun r => waveK (fun y => ρ (s,y)) (r,x)) (t-s) := by
  have hK := contDiff_sourceWaveKernel hρ
  rw [← dirD_prod_left (hK.differentiable (by simp)) (1,0) (t,x) s]
  have hs : ContDiff ℝ ∞ (fun p => sourceWaveKernel ρ (p,s)) :=
    hK.comp (contDiff_id.prodMk contDiff_const)
  rw [← deriv_slice_eq_dirD (hs.differentiable (by simp))]
  change deriv (fun r => waveK (fun y => ρ (s,y)) (r-s,x)) t = _
  exact deriv_comp_sub_const (fun r => waveK (fun y => ρ (s,y)) (r,x)) s t

lemma sourceWaveKernel_secondTime {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (t s : ℝ) (x : Vec) :
    dirD (dirD (sourceWaveKernel ρ) ((1,0),0)) ((1,0),0) ((t,x),s) =
      deriv (deriv (fun r => waveK (fun y => ρ (s,y)) (r,x))) (t-s) := by
  have hK := contDiff_dirD (contDiff_sourceWaveKernel hρ) ((1,0),0)
  rw [← dirD_prod_left (hK.differentiable (by simp)) (1,0) (t,x) s]
  have hs : ContDiff ℝ ∞ (fun p => dirD (sourceWaveKernel ρ) ((1,0),0) (p,s)) :=
    hK.comp (contDiff_id.prodMk contDiff_const)
  rw [← deriv_slice_eq_dirD (hs.differentiable (by simp))]
  have he : (fun r => dirD (sourceWaveKernel ρ) ((1,0),0) ((r,x),s)) =
      fun r => deriv (fun u => waveK (fun y => ρ (s,y)) (u,x)) (r-s) := by
    funext r
    exact sourceWaveKernel_timeDerivative hρ r s x
  rw [he,deriv_comp_sub_const]

lemma sourceWave_initial_value (ρ : ℝ × Vec → ℝ) (x : Vec) :
    sourceWave ρ (0,x) = 0 := by simp [sourceWave,volterra]

lemma sourceWave_initial_velocity {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) (x : Vec) :
    deriv (fun t => sourceWave ρ (t,x)) 0 = 0 := by
  rw [deriv_slice_eq_dirD ((contDiff_sourceWave hρ).differentiable (by simp)),sourceWave_timeDerivative hρ]
  simp [volterra]

lemma sourceWave_equation {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) (x : Vec)
    {t : ℝ} (ht : 0≤t) :
    deriv (deriv (fun r => sourceWave ρ (r,x))) t =
      laplace (fun y => sourceWave ρ (t,y)) x + ρ (t,x) := by
  rw [deriv_deriv_slice_eq_dirD (contDiff_sourceWave hρ),sourceWave_timeDerivative hρ,
    dirD_volterra (contDiff_dirD (contDiff_sourceWaveKernel hρ) ((1,0),0)),one_mul,
    sourceWaveKernel_timeDerivative hρ t t x,sub_self]
  have hρt : ContDiff ℝ ∞ (fun y => ρ (t,y)) := hρ.comp (contDiff_const.prodMk contDiff_id)
  rw [waveK_initial_velocity hρt]
  change _ = laplace (fun y => volterra (sourceWaveKernel ρ) (t,y)) x + _
  rw [laplace_volterra (contDiff_sourceWaveKernel hρ),add_comm]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hst : s≤t := (by simpa only [uIcc_of_le ht] using hs : s ∈ Icc 0 t).2
  dsimp only
  rw [sourceWaveKernel_secondTime hρ]
  have hρs : ContDiff ℝ ∞ (fun y => ρ (s,y)) := hρ.comp (contDiff_const.prodMk contDiff_id)
  exact waveK_equation hρs x (sub_nonneg.mpr hst)

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


lemma contDiff_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : ContDiff ℝ ∞ F) (i : Fin 3) : ContDiff ℝ ∞ (fun x => F x i) :=
  (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF

lemma contDiff_divergence {F : Vec → Vec} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (divergence F) := by
  exact ContDiff.sum (fun i _ => contDiff_spatialPartial (contDiff_component hF i) i)

lemma contDiff_curl {F : Vec → Vec} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (curl F) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> exact (contDiff_spatialPartial (contDiff_component hF _) _).sub
    (contDiff_spatialPartial (contDiff_component hF _) _)

lemma spatialPartial_sum {ι : Type*} (s : Finset ι) {f : ι → Vec → ℝ}
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (x : Vec) (j : Fin 3) :
    spatialPartial (fun y => ∑ i ∈ s, f i y) x j = ∑ i ∈ s, spatialPartial (f i) x j := by
  unfold spatialPartial
  rw [fderiv_fun_sum (fun i hi => hf i hi x)]
  simp

lemma spatialPartial_comm {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) (i j : Fin 3) :
    spatialPartial (fun y => spatialPartial g y i) x j =
      spatialPartial (fun y => spatialPartial g y j) x i :=
  dirD_comm hg (basis i) (basis j) x

lemma divergence_curl {F : Vec → Vec} (hF : ContDiff ℝ ∞ F) (x : Vec) :
    divergence (curl F) x = 0 := by
  have hc (i j : Fin 3) : DifferentiableAt ℝ (fun y => spatialPartial (fun z => F z i) y j) x :=
    (contDiff_spatialPartial (contDiff_component hF i) j).differentiable (by simp) x
  simp only [divergence,Fin.sum_univ_succ]
  change spatialPartial (fun y => spatialPartial (fun z => F z 2) y 1-spatialPartial (fun z => F z 1) y 2) x 0 +
    (spatialPartial (fun y => spatialPartial (fun z => F z 0) y 2-spatialPartial (fun z => F z 2) y 0) x 1 +
    (spatialPartial (fun y => spatialPartial (fun z => F z 1) y 0-spatialPartial (fun z => F z 0) y 1) x 2+0)) = _
  simp only [spatialPartial_sub (hc _ _) (hc _ _)]
  rw [spatialPartial_comm (contDiff_component hF 2) x 1 0,
    spatialPartial_comm (contDiff_component hF 1) x 2 0,
    spatialPartial_comm (contDiff_component hF 0) x 2 1]
  ring

lemma curl_gradient {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) :
    curl (gradient g) x = 0 := by
  ext i
  fin_cases i <;> simp [curl, gradient_apply]
  · exact sub_eq_zero.mpr (spatialPartial_comm hg x 2 1)
  · exact sub_eq_zero.mpr (spatialPartial_comm hg x 0 2)
  · exact sub_eq_zero.mpr (spatialPartial_comm hg x 1 0)

lemma curl_curl_component {F : Vec → Vec} (hF : ContDiff ℝ ∞ F) (x : Vec) (i : Fin 3) :
    curl (curl F) x i = spatialPartial (divergence F) x i-laplace (fun y => F y i) x := by
  have hc (i j : Fin 3) : DifferentiableAt ℝ (fun y => spatialPartial (fun z => F z i) y j) x :=
    (contDiff_spatialPartial (contDiff_component hF i) j).differentiable (by simp) x
  have hsum : spatialPartial (divergence F) x i =
      ∑ j : Fin 3, spatialPartial (fun y => spatialPartial (fun z => F z j) y j) x i := by
    apply spatialPartial_sum
    intro j _
    exact (contDiff_spatialPartial (contDiff_component hF j) j).differentiable (by simp)
  rw [hsum,laplace_eq_sum]
  fin_cases i <;> simp [curl, Fin.sum_univ_succ]
  all_goals simp only [spatialPartial_sub (hc _ _) (hc _ _)]
  · rw [spatialPartial_comm (contDiff_component hF 1) x 0 1,
      spatialPartial_comm (contDiff_component hF 2) x 0 2]
    ring
  · rw [spatialPartial_comm (contDiff_component hF 2) x 1 2,
      spatialPartial_comm (contDiff_component hF 0) x 1 0]
    ring
  · rw [spatialPartial_comm (contDiff_component hF 0) x 2 0,
      spatialPartial_comm (contDiff_component hF 1) x 2 1]
    ring
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace


lemma deriv_moving_local_energy {e : ℝ × Vec → ℝ} {S : ℝ × Vec → Vec}
    {U : Set ℝ} (hU : IsOpen U)
    (he : ContDiffOn ℝ 1 e (U ×ˢ (univ : Set Vec)))
    (hSg : ContDiffOn ℝ 1 S (U ×ˢ (univ : Set Vec)))
    (hcons : ∀ t ∈ U, ∀ x, deriv (fun r => e (r,x)) t + divergence (fun y => S (t,y)) x = 0)
    {g : ℝ × Vec → ℝ} {K : Set Vec} (hK : IsCompact K)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ (univ : Set Vec)))
    (hz : ∀ r ∈ U, ∀ x ∉ K, g (r,x)=0)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun r => ∫ x : Vec, g (r,x) * e (r,x))
      (∫ x : Vec, fderiv ℝ g (t,x) (1,0) * e (t,x) +
        fderiv ℝ g (t,x) (0,S (t,x))) t := by
  have hE := he
  have hF : ContDiffOn ℝ 1 (fun p => g p * e p)
      (U ×ˢ (univ : Set Vec)) := hg.mul hE
  have hzF : ∀ r ∈ U, ∀ x ∉ K, g (r,x)*e (r,x)=0 := by
    intro r hr x hx
    rw [hz r hr x hx,zero_mul]
  have hd := hasFDerivAt_integral_uniform_support hU hK ht hF hzF
  have hi := fderiv_integral_uniform_support_apply hU hK ht hF hzF (1:ℝ)
  have hgg : ContDiff ℝ 1 (fun x => g (t,x)) := by
    apply ContDiffOn.comp_contDiff hg (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hS : ContDiff ℝ 1 (fun x => S (t,x)) := by
    apply ContDiffOn.comp_contDiff hSg
      (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hEc : Continuous (fun x => e (t,x)) := by
    apply hE.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hgD : Continuous (fun x => fderiv ℝ g (t,x)) := by
    apply (hg.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) (by simp)).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hDc : HasCompactSupport (fun x => fderiv ℝ g (t,x)) :=
    compactSupport_param_fderiv hU hK ht hz
  have hgC : HasCompactSupport (fun x => g (t,x)) :=
    compactSupport_of_zero_off hK (hz t ht)
  have hgDapply (v : ℝ × Vec) : HasCompactSupport (fun x => fderiv ℝ g (t,x) v) := by
    apply compactSupport_of_zero_off hDc
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_apply]
  have hIt : Integrable (fun x => fderiv ℝ g (t,x) (1,0) * e (t,x)) :=
    ((hgD.clm_apply continuous_const).mul hEc).integrable_of_hasCompactSupport
      (hgDapply (1,0)).mul_right
  have hIa : Integrable (fun x => g (t,x) * divergence (fun y => S (t,y)) x) :=
    (hgg.continuous.mul (continuous_divergence hS)).integrable_of_hasCompactSupport hgC.mul_right
  have hIs : Integrable (fun x => fderiv ℝ (fun y => g (t,y)) x (S (t,x))) :=
    ((hgg.continuous_fderiv (by simp)).clm_apply hS.continuous).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hgC.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx,zero_apply]))
  have heq : ∀ x : Vec,
      fderiv ℝ (fun p => g p * e p) (t,x) (1,0) =
        fderiv ℝ g (t,x) (1,0) * e (t,x) -
          g (t,x) * divergence (fun y => S (t,y)) x := by
    intro x
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hg' := (hg.contDiffAt hn).differentiableAt (by simp)
    have hE' := (hE.contDiffAt hn).differentiableAt (by simp)
    change fderiv ℝ (g * e) (t,x) (1,0) = _
    rw [fderiv_mul hg' hE',add_apply,
      smul_apply,smul_apply,
      smul_eq_mul,smul_eq_mul,← deriv_time_slice hE']
    have hl := hcons t ht x
    rw [show deriv (fun r => e (r,x)) t =
      -divergence (fun y => S (t,y)) x by linarith]
    ring
  have hxder (x v : Vec) : fderiv ℝ (fun y => g (t,y)) x v = fderiv ℝ g (t,x) (0,v) := by
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hh := ((hg.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    change HasFDerivAt (fun y => g (t,y)) _ x at hh
    rw [hh.fderiv]
    simp
  have hh : deriv (fun r => ∫ x : Vec, g (r,x) * e (r,x)) t =
      ∫ x : Vec, fderiv ℝ g (t,x) (1,0) * e (t,x) +
        fderiv ℝ g (t,x) (0,S (t,x)) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g (r,x) * e (r,x)) t 1 = _
    rw [hi]
    simp only [heq]
    rw [integral_sub hIt hIa,integral_mul_divergence hS hgg hgC,sub_neg_eq_add]
    simp_rw [← hxder]
    exact (integral_add hIt hIs).symm
  exact hh ▸ hd.differentiableAt.hasDerivAt
lemma cone_energy_integrand_nonpos {R ε t : ℝ} {e : ℝ} {S : Vec}
    (hε : 0 < ε) (ht : t ≤ R) (he : 0 ≤ e) (hS : ‖S‖ ≤ e) (x x₀ : Vec) :
    fderiv ℝ (coneCutoff R ε x₀) (t,x) (1,0) * e +
      fderiv ℝ (coneCutoff R ε x₀) (t,x) (0,S) ≤ 0 := by
  rw [coneCutoff_fderiv,coneCutoff_fderiv]
  simp only [inner_zero_right,mul_zero,mul_one,sub_zero,zero_sub]
  have heq : deriv Real.smoothTransition (coneArgument R ε x₀ (t,x)) *
      ((-2*(R-t))/ε) * e + deriv Real.smoothTransition (coneArgument R ε x₀ (t,x)) *
      (-(2*⟪x-x₀,S⟫)/ε) =
      -((2/ε)*deriv Real.smoothTransition (coneArgument R ε x₀ (t,x)) *
      ((R-t)*e+⟪x-x₀,S⟫)) := by ring
  rw [heq]
  apply neg_nonpos.mpr
  by_cases hr : ‖x-x₀‖ ≤ R-t
  · apply mul_nonneg (mul_nonneg (by positivity) (deriv_transition_nonneg _))
    have hc := real_inner_le_norm (-(x-x₀)) S
    simp only [inner_neg_left,norm_neg] at hc
    nlinarith [mul_le_mul_of_nonneg_left hS (norm_nonneg (x-x₀)),
      mul_le_mul_of_nonneg_right hr he]
  · have hn : coneArgument R ε x₀ (t,x) < 0 := by
      dsimp [coneArgument]
      apply div_neg_of_neg_of_pos _ hε
      have hR : 0 ≤ R-t := sub_nonneg.mpr ht
      push Not at hr
      nlinarith [sq_lt_sq₀ hR (norm_nonneg (x-x₀)) |>.mpr hr]
    simp [deriv_transition_zero_neg hn]

lemma causal_local_energy_vanishes {e : ℝ × Vec → ℝ} {S : ℝ × Vec → Vec} {T : ℝ}
    (hT : 0 ≤ T)
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hS : ContDiffOn ℝ 1 S (Ioi 0 ×ˢ (univ : Set Vec)))
    (hec : ContinuousOn e (Icc 0 T ×ˢ (univ : Set Vec)))
    (he0 : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ e (t,x))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x, ‖S (t,x)‖ ≤ e (t,x))
    (hcons : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (r,x)) t + divergence (fun y => S (t,y)) x = 0)
    (hinit : ∀ x, e (0,x)=0) (x₀ : Vec) : e (T,x₀)=0 := by
  let R := T+1
  let g := coneCutoff R 1 x₀
  let G : ℝ → ℝ := fun t => ∫ x : Vec, g (t,x)*e (t,x)
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 R := by intro t ht; exact ⟨ht.1,by dsimp [R]; linarith [ht.2]⟩
  have hgc : ContDiff ℝ 1 g := contDiff_coneCutoff R 1 x₀
  have hgz : ∀ t ∈ Icc 0 T, ∀ x ∉ closedBall x₀ R, g (t,x)=0 := by
    intro t ht x hx
    exact coneCutoff_zero_outside (by norm_num) (hsub ht) hx
  have hGc : ContinuousOn G (Icc 0 T) := by
    apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ R)
      (hgc.continuous.continuousOn.mul hec)
    intro t ht x hx
    change g (t,x)*e (t,x)=0
    rw [hgz t ht x hx,zero_mul]
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) :=
    deriv_moving_local_energy isOpen_Ioo
      (he.mono (by intro p hp; exact ⟨hp.1.1,hp.2⟩))
      (hS.mono (by intro p hp; exact ⟨hp.1.1,hp.2⟩)) hcons
      (isCompact_closedBall x₀ R) hgc.contDiffOn
      (fun r hr x hx => hgz r ⟨hr.1.le,hr.2.le⟩ x hx) ht
  have hanti : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hGc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t ht).deriv]
      apply integral_nonpos
      intro x
      exact cone_energy_integrand_nonpos (by norm_num) (hsub ⟨ht.1.le,ht.2.le⟩).2
        (he0 t ⟨ht.1.le,ht.2.le⟩ x) (hflux t ht x) x x₀
  have hG0 : G 0 = 0 := by simp [G,hinit]
  have hGn : ∀ x, 0 ≤ g (T,x)*e (T,x) := fun x =>
    mul_nonneg (Real.smoothTransition.nonneg _) (he0 T ⟨hT,le_rfl⟩ x)
  have hGT : G T = 0 := le_antisymm
    (by simpa only [hG0] using hanti ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT)
    (integral_nonneg hGn)
  have hTc : Continuous (fun x => g (T,x)*e (T,x)) :=
    (hgc.continuous.comp (continuous_const.prodMk continuous_id)).mul
      (hec.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨⟨hT,le_rfl⟩,mem_univ x⟩))
  have hI : Integrable (fun x => g (T,x)*e (T,x)) :=
    hTc.integrable_of_hasCompactSupport ((compactSupport_of_zero_off (isCompact_closedBall x₀ R)
      (hgz T ⟨hT,le_rfl⟩)).mul_right)
  have hae := (integral_eq_zero_iff_of_nonneg hGn hI).mp hGT
  have hpoint := congrFun (Measure.eq_of_ae_eq (μ:=volume) hae hTc continuous_const) x₀
  have hval : g (T,x₀)=1 := by simp [g,coneCutoff,coneArgument,R]
  simpa only [hval,one_mul,Pi.zero_apply] using hpoint

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

section CompactParameter
variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] (μ : Measure α) [IsFiniteMeasure μ]
  {ι : α → Vec} (hι : Continuous ι)
include hι

lemma hasFDerivAt_integral_compactParam
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ 1 F) (p : H) :
    HasFDerivAt (fun x => ∫ n : α, F (x,ι n) ∂μ)
      (∫ n : α, (fderiv ℝ F (p,ι n)).comp (ContinuousLinearMap.inl ℝ H Vec)
        ∂μ) p := by
  let D : H × α → H →L[ℝ] W := fun z =>
    (fderiv ℝ F (z.1,ι z.2)).comp (ContinuousLinearMap.inl ℝ H Vec)
  have hD : Continuous D := by
    exact ((hF.continuous_fderiv (by simp)).comp
      (continuous_fst.prodMk (hι.comp continuous_snd))).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall p 1) (bound:=fun _ => C) (F':=fun x n => D (x,n))
    (closedBall_mem_nhds p (by norm_num))
  · exact Eventually.of_forall (fun x => (hF.continuous.comp
      (continuous_const.prodMk hι)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk hι)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun n x hx => hC _ ⟨(x,n),⟨hx,mem_univ n⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun n x _ => (hF.differentiable (by simp) (x,ι n)).hasFDerivAt.comp x
      (by convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const (ι n) x) using 1 <;> rfl))

omit [SecondCountableTopology α] in
lemma continuous_integral_compactParam
    {H : Type} {W : Type*} [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : H × Vec → W} (hF : Continuous F) :
    Continuous (fun x => ∫ n : α, F (x,ι n) ∂μ) := by
  have hc : Continuous (fun p : H × α => F (p.1,ι p.2)) :=
    hF.comp (continuous_fst.prodMk (hι.comp continuous_snd))
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hc.continuousOn
  intro x n _ hn
  exact (hn (mem_univ n)).elim

lemma contDiff_integral_compactParam_nat
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    (k : ℕ) : ∀ {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W}, ContDiff ℝ k F →
      ContDiff ℝ k (fun x => ∫ n : α, F (x,ι n) ∂μ) := by
  induction k with
  | zero =>
    intro W _ _ _ F hF
    exact contDiff_zero.mpr (continuous_integral_compactParam μ hι hF.continuous)
  | succ k ih =>
    intro W _ _ _ F hF
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.succ_pos k)
    let D : H × Vec → H →L[ℝ] W := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H Vec)
    have hD : ContDiff ℝ k D :=
      ((contDiff_succ_iff_fderiv.mp hF).2.2).clm_comp contDiff_const
    have he : fderiv ℝ (fun x => ∫ n : α, F (x,ι n) ∂μ) =
        (fun x => ∫ n : α, D (x,ι n) ∂μ) := by
      funext x
      exact (hasFDerivAt_integral_compactParam μ hι hF1 x).fderiv
    rw [show (↑(k+1) : ℕ∞ω) = ↑k+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_compactParam μ hι hF1 x).differentiableAt,?_,?_⟩
    · simp
    · rw [he]
      exact ih hD

lemma contDiff_integral_compactParam
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => ∫ n : α, F (x,ι n) ∂μ) := by
  rw [contDiff_infty]
  intro k
  exact contDiff_integral_compactParam_nat μ hι k (contDiff_infty.mp hF k)

end CompactParameter

lemma contDiff_integral_compactSet
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} {K : Set Vec} (hF : ContDiff ℝ ∞ F) (hK : IsCompact K) :
    ContDiff ℝ ∞ (fun x => ∫ v in K, F (x,v)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasureOnCompacts (volume.comap (Subtype.val : K → Vec)) :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hK.measurableSet)
  have hh := contDiff_integral_compactParam (volume.comap (Subtype.val : K → Vec))
    (ι:=Subtype.val) continuous_subtype_val hF
  convert hh using 1
  funext x
  exact (integral_subtype_comap hK.measurableSet (fun v => F (x,v))).symm

lemma contDiff_integral_uniform_compact
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} {K : Set Vec} (hF : ContDiff ℝ ∞ F) (hK : IsCompact K)
    (hzero : ∀ x v, v ∉ K → F (x,v)=0) :
    ContDiff ℝ ∞ (fun x => ∫ v, F (x,v)) := by
  convert contDiff_integral_compactSet hF hK using 1
  funext x
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  exact hzero x

lemma contDiff_rho_uniform_compact {f : Particle} {K : Set Vec}
    (hf : ContDiff ℝ ∞ f) (hK : IsCompact K)
    (hzero : ∀ t x v, v ∉ K → f (t,x,v)=0) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun z => f (p.1,z)) p.2) := by
  exact contDiff_integral_uniform_compact
    (F:=fun z : (ℝ × Vec) × Vec => f (z.1.1,z.1.2,z.2))
    (hf.comp contDiff_reassociate) hK (fun p v hv => hzero p.1 p.2 v hv)

lemma contDiff_current_uniform_compact {f : Particle} {K : Set Vec}
    (hf : ContDiff ℝ ∞ f) (hK : IsCompact K)
    (hzero : ∀ t x v, v ∉ K → f (t,x,v)=0) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun z => f (p.1,z)) p.2) := by
  apply contDiff_integral_uniform_compact
    (F:=fun z : (ℝ × Vec) × Vec => f (z.1.1,z.1.2,z.2) • velocity z.2)
    ((hf.comp contDiff_reassociate).smul (contDiff_velocity.comp contDiff_snd)) hK
  intro p v hv
  simp only [hzero p.1 p.2 v hv,zero_smul]

lemma integrable_conePotential {ρ : ℝ × Vec → ℝ} (hρ : Continuous ρ)
    {t : ℝ} (_ht : 0≤t) (x : Vec) :
    IntegrableOn (fun z : Vec => ρ (t-‖z‖,x+z)/‖z‖) (ball 0 t) := by
  have hc : Continuous (fun z : Vec => ρ (t-‖z‖,x+z)) :=
    hρ.comp ((continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id))
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0:Vec) t).image hc).isBounded.exists_norm_le
  apply integrableOn_ball_of_norm_le_rpow (by simp)
    (α:=1) (C:=C) (by simp)
  · apply ae_restrict_of_forall_mem measurableSet_ball
    intro z hz
    have hh := hC _ ⟨z,ball_subset_closedBall hz,rfl⟩
    rw [norm_div,norm_norm,Real.rpow_neg_one,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (norm_nonneg z))
  · exact (hc.measurable.div continuous_norm.measurable).aestronglyMeasurable

lemma sourceWave_ball {ρ : ℝ × Vec → ℝ} (hρ : Continuous ρ)
    {t : ℝ} (ht : 0≤t) (x : Vec) :
    sourceWave ρ (t,x) = (4*Real.pi)⁻¹ *
      ∫ z in ball (0:Vec) t, ρ (t-‖z‖,x+z)/‖z‖ := by
  have hi := (integrable_conePotential hρ ht x).integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball,integral_polar hi]
  have he (n : Sphere) :
      (∫ r in Ioi (0:ℝ), r^2 • (ball (0:Vec) t).indicator
        (fun z => ρ (t-‖z‖,x+z)/‖z‖) (r • n.1)) =
      ∫ r in 0..t, r*ρ (t-r,x+r • n.1) := by
    have hf : ∀ r ∈ Ioi (0:ℝ), r^2 • (ball (0:Vec) t).indicator
        (fun z => ρ (t-‖z‖,x+z)/‖z‖) (r • n.1) =
        (Ioo (0:ℝ) t).indicator (fun r => r*ρ (t-r,x+r • n.1)) r := by
      intro r hr
      change 0<r at hr
      have hn : ‖r • n.1‖=r := by simp [norm_smul,abs_of_pos hr]
      by_cases hh : r<t
      · rw [indicator_of_mem (show r • n.1 ∈ ball (0:Vec) t by simpa [mem_ball_zero_iff,hn] using hh),
          indicator_of_mem (show r ∈ Ioo (0:ℝ) t from ⟨hr,hh⟩),smul_eq_mul,hn]
        field_simp
      · rw [indicator_of_notMem (show r • n.1 ∉ ball (0:Vec) t by simpa [mem_ball_zero_iff,hn] using hh),
          indicator_of_notMem (show r ∉ Ioo (0:ℝ) t from fun h => hh h.2),smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hf,setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self,← integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le ht]
  simp_rw [he]
  have hc : Continuous (fun p : ℝ × Sphere => p.1*ρ (t-p.1,x+p.1 • p.2.1)) :=
    continuous_fst.mul (hρ.comp ((continuous_const.sub continuous_fst).prodMk
      (continuous_const.add (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)))))
  have hi2 : Integrable (fun p : ℝ × Sphere => p.1*ρ (t-p.1,x+p.1 • p.2.1))
      ((volume.restrict (uIoc 0 t)).prod sphereMeasure) := by
    let : IsFiniteMeasure sphereMeasure := inferInstance
    let : IsFiniteMeasureOnCompacts ((volume : Measure ℝ).prod sphereMeasure) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    rw [uIoc_of_le ht,Measure.restrict_prod_eq_prod_univ]
    exact (hc.continuousOn.integrableOn_compact
      (μ := (volume : Measure ℝ).prod sphereMeasure)
      (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono_left Ioc_subset_Icc_self)
  rw [← intervalIntegral_integral_swap hi2]
  have hs : sourceWave ρ (t,x) = (4*Real.pi)⁻¹ *
      ∫ s in 0..t, (t-s)*(∫ n : Sphere, ρ (s,x+(t-s) • n.1) ∂sphereMeasure) := by
    simp only [sourceWave,volterra,sourceWaveKernel,waveK,sphereSum]
    exact intervalIntegral.integral_const_mul _ _
  rw [hs]
  congr 1
  calc
    _ = ∫ r in 0..t, r*(∫ n : Sphere, ρ (t-r,x+r • n.1) ∂sphereMeasure) := by
      have hh := intervalIntegral.integral_comp_sub_left
        (fun r => r*(∫ n : Sphere, ρ (t-r,x+r • n.1) ∂sphereMeasure)) (a:=0) (b:=t) t
      simpa only [sub_self,sub_zero,sub_sub_cancel] using hh
    _ = _ := intervalIntegral.integral_congr (fun r _ => (integral_const_mul _ _).symm)

end RVM

end

end OAI
