import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.ParamPrimitive

namespace OAI

noncomputable section

section
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
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma dirD_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : Differentiable ℝ F) (p e : H) (i : Fin 3) :
    dirD (fun z => F z i) e p = dirD F e p i := by
  have h := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp p (hF p).hasFDerivAt
  change HasFDerivAt (fun z => F z i) _ p at h
  unfold dirD
  rw [h.fderiv]
  rfl

lemma divergence_smul {g : Vec → ℝ} {F : Vec → Vec} {x : Vec}
    (hg : DifferentiableAt ℝ g x) (hF : DifferentiableAt ℝ F x) :
    divergence (fun y => g y • F y) x =
      dot (gradient g x) (F x) + g x * divergence F x := by
  have hc (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF
  have hm (i : Fin 3) : spatialPartial (fun y => g y * F y i) x i =
      g x * spatialPartial (fun y => F y i) x i + F x i * spatialPartial g x i :=
    spatialPartial_mul hg (hc i) i
  simp only [divergence,PiLp.smul_apply,smul_eq_mul,hm,dot,
    gradient_apply,Finset.sum_add_distrib,Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def waveGradient (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => dirD u (0,basis i) p)

lemma waveGradient_apply (u : ℝ × Vec → ℝ) (p : ℝ × Vec) (i : Fin 3) :
    waveGradient u p i = dirD u (0,basis i) p := rfl

lemma contDiff_waveGradient {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (waveGradient u) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_dirD hu (0,basis i)

lemma waveGradient_slice {u : ℝ × Vec → ℝ} (hu : Differentiable ℝ u) (t : ℝ) (x : Vec) :
    waveGradient u (t,x) = gradient (fun y => u (t,y)) x := by
  ext i
  rw [waveGradient_apply,gradient_apply,spatialPartial_time_slice (hu (t,x))]
  rfl

lemma divergence_waveGradient {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    divergence (fun y => waveGradient u (t,y)) x = laplace (fun y => u (t,y)) x := by
  have he : (fun y => waveGradient u (t,y)) = gradient (fun y => u (t,y)) :=
    funext (waveGradient_slice (hu.differentiable (by simp)) t)
  rw [he]
  rfl

lemma waveGradient_time {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    deriv (fun r => waveGradient u (r,x)) t = waveGradient (dirD u (1,0)) (t,x) := by
  rw [deriv_slice_eq_dirD ((contDiff_waveGradient hu).differentiable (by simp))]
  ext i
  rw [← dirD_component ((contDiff_waveGradient hu).differentiable (by simp)),waveGradient_apply]
  exact dirD_comm hu (0,basis i) (1,0) (t,x)

def waveEnergy (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  ((dirD u (1,0) p)^2+‖waveGradient u p‖^2)/2

def waveFlux (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : Vec :=
  -(dirD u (1,0) p) • waveGradient u p

lemma contDiff_waveEnergy {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (waveEnergy u) :=
  (((contDiff_dirD hu (1,0)).pow 2).add ((contDiff_waveGradient hu).norm_sq ℝ)).div_const 2

lemma contDiff_waveFlux {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (waveFlux u) := (contDiff_dirD hu (1,0)).neg.smul (contDiff_waveGradient hu)

lemma waveEnergy_nonneg (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : 0 ≤ waveEnergy u p := by
  dsimp [waveEnergy]
  positivity

lemma waveFlux_bound (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : ‖waveFlux u p‖ ≤ waveEnergy u p := by
  rw [waveFlux,norm_smul,Real.norm_eq_abs,abs_neg]
  have h := sq_nonneg (|dirD u (1,0) p|-‖waveGradient u p‖)
  have hh := sq_abs (dirD u (1,0) p)
  dsimp [waveEnergy]
  nlinarith

lemma waveEnergy_deriv {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    deriv (fun r => waveEnergy u (r,x)) t =
      dirD u (1,0) (t,x)*dirD (dirD u (1,0)) (1,0) (t,x) +
      dot (waveGradient u (t,x)) (waveGradient (dirD u (1,0)) (t,x)) := by
  have ht : DifferentiableAt ℝ (fun r : ℝ => dirD u (1,0) (r,x)) t := by
    exact DifferentiableAt.comp (f:=fun r : ℝ => (r,x)) (g:=dirD u (1,0)) t
      ((contDiff_dirD hu (1,0)).differentiable (by simp) (t,x))
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hx : DifferentiableAt ℝ (fun r : ℝ => waveGradient u (r,x)) t := by
    exact DifferentiableAt.comp (f:=fun r : ℝ => (r,x)) (g:=waveGradient u) t
      ((contDiff_waveGradient hu).differentiable (by simp) (t,x))
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hd := ((ht.hasDerivAt.pow 2).add hx.hasDerivAt.norm_sq).div_const 2
  change HasDerivAt (fun r => waveEnergy u (r,x)) _ t at hd
  rw [hd.deriv,deriv_slice_eq_dirD ((contDiff_dirD hu (1,0)).differentiable (by simp)),
    waveGradient_time hu,← dot_eq_inner]
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
  ring

lemma waveFlux_divergence {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    divergence (fun y => waveFlux u (t,y)) x =
      -dirD u (1,0) (t,x)*laplace (fun y => u (t,y)) x -
      dot (waveGradient u (t,x)) (waveGradient (dirD u (1,0)) (t,x)) := by
  have ht : DifferentiableAt ℝ (fun y : Vec => dirD u (1,0) (t,y)) x :=
    ((contDiff_dirD hu (1,0)).differentiable (by simp) (t,x)).comp x
    ((differentiableAt_const t).prodMk differentiableAt_id)
  have hx : DifferentiableAt ℝ (fun y : Vec => waveGradient u (t,y)) x :=
    ((contDiff_waveGradient hu).differentiable (by simp) (t,x)).comp x
    ((differentiableAt_const t).prodMk differentiableAt_id)
  unfold waveFlux
  rw [divergence_smul (g:=fun y => -(dirD u (1,0) (t,y))) ht.neg hx,
    divergence_waveGradient hu]
  have hg : gradient (fun y => -dirD u (1,0) (t,y)) x = -waveGradient (dirD u (1,0)) (t,x) := by
    ext i
    rw [gradient_apply,PiLp.neg_apply,waveGradient_apply]
    unfold spatialPartial
    rw [fderiv_fun_neg,neg_apply]
    congr 1
    exact spatialPartial_time_slice ((contDiff_dirD hu (1,0)).differentiable (by simp) (t,x)) i
  rw [hg]
  simp only [dot,PiLp.neg_apply,neg_mul,Finset.sum_neg_distrib]
  have hc : (∑ i : Fin 3, waveGradient (dirD u (1,0)) (t,x) i * waveGradient u (t,x) i) =
      ∑ i : Fin 3, waveGradient u (t,x) i * waveGradient (dirD u (1,0)) (t,x) i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  ring

lemma wave_local_energy {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec)
    (hw : deriv (deriv (fun r => u (r,x))) t = laplace (fun y => u (t,y)) x) :
    deriv (fun r => waveEnergy u (r,x)) t + divergence (fun y => waveFlux u (t,y)) x = 0 := by
  rw [waveEnergy_deriv hu,waveFlux_divergence hu,← deriv_deriv_slice_eq_dirD hu,hw]
  ring

lemma dirD_add {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F G : H → W}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (e : H) :
    dirD (fun p => F p+G p) e = fun p => dirD F e p+dirD G e p := by
  funext p
  simp only [dirD,fderiv_fun_add (hF p) (hG p),add_apply]

lemma dirD_sub {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F G : H → W}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (e : H) :
    dirD (fun p => F p-G p) e = fun p => dirD F e p-dirD G e p := by
  funext p
  simp only [dirD,fderiv_fun_sub (hF p) (hG p),sub_apply]

lemma dirD_sum {H W ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (S : Finset ι) {F : ι → H → W}
    (hF : ∀ i ∈ S, Differentiable ℝ (F i)) (e : H) :
    dirD (fun p => ∑ i ∈ S, F i p) e = fun p => ∑ i ∈ S, dirD (F i) e p := by
  funext p
  simp only [dirD,fderiv_fun_sum (fun i hi => hF i hi p),sum_apply]

lemma dirD_third_comm {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e a p : H) :
    dirD (dirD (dirD F a) a) e p = dirD (dirD (dirD F e) a) a p := by
  rw [dirD_comm (contDiff_dirD hF a) a e]
  have hh : dirD (dirD F a) e = dirD (dirD F e) a :=
    funext (dirD_comm hF a e)
  rw [hh]

def waveBox (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  dirD (dirD u (1,0)) (1,0) p -
    ∑ i : Fin 3, dirD (dirD u (0,basis i)) (0,basis i) p

lemma waveBox_eq {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    waveBox u (t,x) = deriv (deriv (fun r => u (r,x))) t -laplace (fun y => u (t,y)) x := by
  rw [deriv_deriv_slice_eq_dirD hu,laplace_slice_eq_dirD hu]
  rfl

lemma contDiff_waveBox {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (waveBox u) :=
  (contDiff_dirD (contDiff_dirD hu (1,0)) (1,0)).sub
    (ContDiff.sum (fun i _ => contDiff_dirD (contDiff_dirD hu (0,basis i)) (0,basis i)))

lemma waveBox_sub {u v : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    waveBox (fun p => u p-v p) = fun p => waveBox u p-waveBox v p := by
  have hdd (e a p : ℝ × Vec) :
      dirD (dirD (fun p => u p-v p) e) a p =
      dirD (dirD u e) a p-dirD (dirD v e) a p := by
    rw [dirD_sub (hu.differentiable (by simp)) (hv.differentiable (by simp)),
      dirD_sub ((contDiff_dirD hu e).differentiable (by simp))
        ((contDiff_dirD hv e).differentiable (by simp))]
  funext p
  simp only [waveBox,hdd,Finset.sum_sub_distrib]
  ring

lemma waveBox_add {u v : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    waveBox (fun p => u p+v p) = fun p => waveBox u p+waveBox v p := by
  have hdd (e a p : ℝ × Vec) :
      dirD (dirD (fun p => u p+v p) e) a p =
      dirD (dirD u e) a p+dirD (dirD v e) a p := by
    rw [dirD_add (hu.differentiable (by simp)) (hv.differentiable (by simp)),
      dirD_add ((contDiff_dirD hu e).differentiable (by simp))
        ((contDiff_dirD hv e).differentiable (by simp))]
  funext p
  simp only [waveBox,hdd,Finset.sum_add_distrib]
  ring

lemma waveBox_dirD {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (e : ℝ × Vec) (p : ℝ × Vec) :
    waveBox (dirD u e) p = dirD (waveBox u) e p := by
  have hf := (contDiff_dirD (contDiff_dirD hu (1,0)) (1,0)).differentiable (by simp)
  have hi (i : Fin 3) :=
    (contDiff_dirD (contDiff_dirD hu (0,basis i)) (0,basis i)).differentiable (by simp)
  have hs : Differentiable ℝ (fun p => ∑ i : Fin 3, dirD (dirD u (0,basis i)) (0,basis i) p) :=
    Differentiable.fun_sum (fun i _ => hi i)
  unfold waveBox
  rw [dirD_sub hf hs]
  dsimp only
  rw [dirD_sum Finset.univ (fun i _ => hi i)]
  simp only [dirD_third_comm hu]

lemma waveBox_timeDerivative_zero {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    (hw : ∀ t, 0<t → ∀ x, waveBox u (t,x)=0) {t : ℝ} (ht : 0<t) (x : Vec) :
    waveBox (dirD u (1,0)) (t,x)=0 := by
  rw [waveBox_dirD hu,← deriv_slice_eq_dirD ((contDiff_waveBox hu).differentiable (by simp))]
  have he : (fun r => waveBox u (r,x)) =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [lt_mem_nhds ht] with r hr
    exact hw r hr x
  rw [he.deriv_eq,deriv_const]

lemma waveK_box {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) {t : ℝ} (ht : 0≤t) (x : Vec) :
    waveBox (waveK g) (t,x)=0 := by
  rw [waveBox_eq (contDiff_waveK hg),waveK_equation hg x ht,sub_self]

def freeWave (g h : Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  dirD (waveK g) (1,0) p + waveK h p

lemma contDiff_freeWave {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (freeWave g h) :=
  (contDiff_dirD (contDiff_waveK hg) (1,0)).add (contDiff_waveK hh)

lemma freeWave_initial {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) :
    freeWave g h (0,x)=g x := by
  rw [freeWave,← deriv_slice_eq_dirD ((contDiff_waveK hg).differentiable (by simp)),
    waveK_initial_velocity hg,waveK_zero,add_zero]

lemma freeWave_initial_velocity {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h) (x : Vec) :
    deriv (fun t => freeWave g h (t,x)) 0 = h x := by
  rw [deriv_slice_eq_dirD ((contDiff_freeWave hg hh).differentiable (by simp))]
  change dirD (fun p => dirD (waveK g) (1,0) p+waveK h p) (1,0) (0,x)=_
  rw [dirD_add ((contDiff_dirD (contDiff_waveK hg) (1,0)).differentiable (by simp))
    ((contDiff_waveK hh).differentiable (by simp))]
  dsimp only
  rw [← deriv_deriv_slice_eq_dirD (contDiff_waveK hg),waveK_equation hg x (by norm_num),
    ← deriv_slice_eq_dirD ((contDiff_waveK hh).differentiable (by simp)),waveK_initial_velocity hh]
  simp only [waveK_zero]
  simp [laplace,divergence,gradient,spatialPartial]

lemma freeWave_box {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    {t : ℝ} (ht : 0<t) (x : Vec) : waveBox (freeWave g h) (t,x)=0 := by
  unfold freeWave
  rw [waveBox_add (contDiff_dirD (contDiff_waveK hg) (1,0)) (contDiff_waveK hh)]
  dsimp only
  rw [waveBox_timeDerivative_zero (contDiff_waveK hg) (fun _ hr y => waveK_box hg hr.le y) ht x,
    waveK_box hh ht.le,zero_add]

lemma sourceWave_box {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) {t : ℝ} (ht : 0≤t) (x : Vec) :
    waveBox (sourceWave ρ) (t,x)=ρ (t,x) := by
  rw [waveBox_eq (contDiff_sourceWave hρ),sourceWave_equation hρ x ht]
  ring

lemma waveGradient_initial_zero {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x, u (0,x)=0) (x : Vec) : waveGradient u (0,x)=0 := by
  rw [waveGradient_slice (hu.differentiable (by simp))]
  have hh : (fun y => u (0,y)) = fun _ => (0:ℝ) := funext h0
  rw [hh]
  ext i
  simp

lemma waveEnergy_initial_zero {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x, u (0,x)=0) (h1 : ∀ x, deriv (fun t => u (t,x)) 0=0) (x : Vec) :
    waveEnergy u (0,x)=0 := by
  rw [waveEnergy,waveGradient_initial_zero hu h0,
    ← deriv_slice_eq_dirD (hu.differentiable (by simp)),h1]
  norm_num

lemma wave_zero_on {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    {T : ℝ} (hT : 0≤T)
    (hw : ∀ t ∈ Ioo 0 T, ∀ x, waveBox u (t,x)=0)
    (h0 : ∀ x, u (0,x)=0) (h1 : ∀ x, deriv (fun t => u (t,x)) 0=0)
    (x : Vec) : u (T,x)=0 := by
  have hezero (t : ℝ) (ht : t ∈ Icc 0 T) (y : Vec) : waveEnergy u (t,y)=0 := by
    apply causal_local_energy_vanishes ht.1
      ((contDiff_waveEnergy hu).of_le (by simp)).contDiffOn
      ((contDiff_waveFlux hu).of_le (by simp)).contDiffOn
      (contDiff_waveEnergy hu).continuous.continuousOn
      (fun _ _ z => waveEnergy_nonneg u (_,z))
      (fun _ _ z => waveFlux_bound u (_,z))
      _ (waveEnergy_initial_zero hu h0 h1)
    intro r hr z
    apply wave_local_energy hu
    have hh := hw r ⟨hr.1,hr.2.trans_le ht.2⟩ z
    rw [waveBox_eq hu] at hh
    linarith
  have htzero (t : ℝ) (ht : t ∈ Icc 0 T) : deriv (fun r => u (r,x)) t=0 := by
    rw [deriv_slice_eq_dirD (hu.differentiable (by simp))]
    have he := hezero t ht x
    unfold waveEnergy at he
    nlinarith [sq_nonneg (dirD u (1,0) (t,x)),sq_nonneg ‖waveGradient u (t,x)‖]
  have hdiff (t : ℝ) : DifferentiableAt ℝ (fun r => u (r,x)) t :=
    DifferentiableAt.comp (f:=fun r : ℝ => (r,x)) (g:=u) t
      (hu.differentiable (by simp) (t,x))
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hn := (convex_Icc (0:ℝ) T).norm_image_sub_le_of_norm_deriv_le
    (fun t (_ht : t ∈ Icc 0 T) => hdiff t)
    (C:=0) (fun t ht => by rw [htzero t ht]; simp) ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩
  simp only [zero_mul,h0,sub_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

lemma wave_zero {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    (hw : ∀ t, 0<t → ∀ x, waveBox u (t,x)=0)
    (h0 : ∀ x, u (0,x)=0) (h1 : ∀ x, deriv (fun t => u (t,x)) 0=0)
    {T : ℝ} (hT : 0≤T) (x : Vec) : u (T,x)=0 :=
  wave_zero_on hu hT (fun t ht y => hw t ht.1 y) h0 h1 x

lemma wave_unique {u v : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hw : ∀ t, 0<t → ∀ x, waveBox u (t,x)=waveBox v (t,x))
    (h0 : ∀ x, u (0,x)=v (0,x))
    (h1 : ∀ x, deriv (fun t => u (t,x)) 0=deriv (fun t => v (t,x)) 0)
    {T : ℝ} (hT : 0≤T) (x : Vec) : u (T,x)=v (T,x) := by
  apply sub_eq_zero.mp
  apply wave_zero (hu.sub hv) _ _ _ hT x
  · intro t ht y
    rw [waveBox_sub hu hv]
    exact sub_eq_zero.mpr (hw t ht y)
  · intro y
    exact sub_eq_zero.mpr (h0 y)
  · intro y
    rw [deriv_slice_eq_dirD ((hu.sub hv).differentiable (by simp)),
      dirD_sub (hu.differentiable (by simp)) (hv.differentiable (by simp))]
    dsimp only
    rw [← deriv_slice_eq_dirD (hu.differentiable (by simp)),
      ← deriv_slice_eq_dirD (hv.differentiable (by simp)),h1,sub_self]

lemma wave_unique_on {u v : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    {T : ℝ} (hT : 0≤T)
    (hw : ∀ t ∈ Ioo 0 T, ∀ x, waveBox u (t,x)=waveBox v (t,x))
    (h0 : ∀ x, u (0,x)=v (0,x))
    (h1 : ∀ x, deriv (fun t => u (t,x)) 0=deriv (fun t => v (t,x)) 0)
    (x : Vec) : u (T,x)=v (T,x) := by
  apply sub_eq_zero.mp
  apply wave_zero_on (hu.sub hv) hT _ _ _ x
  · intro t ht y
    rw [waveBox_sub hu hv]
    exact sub_eq_zero.mpr (hw t ht y)
  · intro y
    exact sub_eq_zero.mpr (h0 y)
  · intro y
    rw [deriv_slice_eq_dirD ((hu.sub hv).differentiable (by simp)),
      dirD_sub (hu.differentiable (by simp)) (hv.differentiable (by simp))]
    dsimp only
    rw [← deriv_slice_eq_dirD (hu.differentiable (by simp)),
      ← deriv_slice_eq_dirD (hv.differentiable (by simp)),h1,sub_self]

def retardedWave (g h : Vec → ℝ) (ρ : ℝ × Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  freeWave g h p + sourceWave ρ p

lemma contDiff_retardedWave {g h : Vec → ℝ} {ρ : ℝ × Vec → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (retardedWave g h ρ) :=
  (contDiff_freeWave hg hh).add (contDiff_sourceWave hρ)

lemma retardedWave_initial {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (ρ : ℝ × Vec → ℝ) (x : Vec) :
    retardedWave g h ρ (0,x)=g x := by
  rw [retardedWave,freeWave_initial hg,sourceWave_initial_value,add_zero]

lemma retardedWave_initial_velocity {g h : Vec → ℝ} {ρ : ℝ × Vec → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (hρ : ContDiff ℝ ∞ ρ) (x : Vec) :
    deriv (fun t => retardedWave g h ρ (t,x)) 0=h x := by
  rw [deriv_slice_eq_dirD ((contDiff_retardedWave hg hh hρ).differentiable (by simp))]
  unfold retardedWave
  rw [dirD_add ((contDiff_freeWave hg hh).differentiable (by simp))
    ((contDiff_sourceWave hρ).differentiable (by simp))]
  dsimp only
  rw [← deriv_slice_eq_dirD ((contDiff_freeWave hg hh).differentiable (by simp)),
    freeWave_initial_velocity hg hh,
    ← deriv_slice_eq_dirD ((contDiff_sourceWave hρ).differentiable (by simp)),
    sourceWave_initial_velocity hρ,add_zero]

lemma retardedWave_box {g h : Vec → ℝ} {ρ : ℝ × Vec → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (hρ : ContDiff ℝ ∞ ρ)
    {t : ℝ} (ht : 0<t) (x : Vec) : waveBox (retardedWave g h ρ) (t,x)=ρ (t,x) := by
  unfold retardedWave
  rw [waveBox_add (contDiff_freeWave hg hh) (contDiff_sourceWave hρ)]
  dsimp only
  rw [freeWave_box hg hh ht,sourceWave_box hρ ht.le,zero_add]

lemma wave_representation {u : ℝ × Vec → ℝ} {g h : Vec → ℝ} {ρ : ℝ × Vec → ℝ}
    (hu : ContDiff ℝ ∞ u) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hρ : ContDiff ℝ ∞ ρ) (hw : ∀ t, 0<t → ∀ x, waveBox u (t,x)=ρ (t,x))
    (h0 : ∀ x, u (0,x)=g x) (h1 : ∀ x, deriv (fun t => u (t,x)) 0=h x)
    {T : ℝ} (hT : 0≤T) (x : Vec) : u (T,x)=retardedWave g h ρ (T,x) := by
  apply wave_unique hu (contDiff_retardedWave hg hh hρ)
    (fun t ht y => (hw t ht y).trans (retardedWave_box hg hh hρ ht y).symm)
    (fun y => (h0 y).trans (retardedWave_initial hg ρ y).symm)
    (fun y => (h1 y).trans (retardedWave_initial_velocity hg hh hρ y).symm) hT

lemma wave_representation_on {u : ℝ × Vec → ℝ} {g h : Vec → ℝ} {ρ : ℝ × Vec → ℝ}
    (hu : ContDiff ℝ ∞ u) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hρ : ContDiff ℝ ∞ ρ) {T : ℝ} (hT : 0≤T)
    (hw : ∀ t ∈ Ioo 0 T, ∀ x, waveBox u (t,x)=ρ (t,x))
    (h0 : ∀ x, u (0,x)=g x) (h1 : ∀ x, deriv (fun t => u (t,x)) 0=h x)
    (x : Vec) : u (T,x)=retardedWave g h ρ (T,x) := by
  apply wave_unique_on hu (contDiff_retardedWave hg hh hρ) hT
    (fun t ht y => (hw t ht y).trans (retardedWave_box hg hh hρ ht.1 y).symm)
    (fun y => (h0 y).trans (retardedWave_initial hg ρ y).symm)
    (fun y => (h1 y).trans (retardedWave_initial_velocity hg hh hρ y).symm)

def curlA : Fin 3 → Fin 3 := ![1,2,0]
def curlB : Fin 3 → Fin 3 := ![2,0,1]

def spaceCurl (F : Field) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => dirD F (0,basis (curlA i)) p (curlB i) -
    dirD F (0,basis (curlB i)) p (curlA i))

lemma spaceCurl_apply (F : Field) (p : ℝ × Vec) (i : Fin 3) :
    spaceCurl F p i = dirD F (0,basis (curlA i)) p (curlB i) -
      dirD F (0,basis (curlB i)) p (curlA i) := rfl

lemma contDiff_spaceCurl {F : Field} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (spaceCurl F) := by
  apply contDiff_euclidean.mpr
  intro i
  exact (contDiff_component (contDiff_dirD hF _) _).sub
    (contDiff_component (contDiff_dirD hF _) _)

lemma spaceCurl_slice {F : Field} (hF : Differentiable ℝ F) (t : ℝ) (x : Vec) :
    spaceCurl F (t,x) = curl (fun y => F (t,y)) x := by
  have hc (i : Fin 3) : Differentiable ℝ (fun p => F p i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiable.comp hF
  have hh (i j : Fin 3) : spatialPartial (fun y => F (t,y) i) x j =
      dirD F (0,basis j) (t,x) i := by
    rw [spatialPartial_time_slice (hc i (t,x))]
    exact dirD_component hF (t,x) (0,basis j) i
  ext i
  fin_cases i <;> simp [spaceCurl_apply,curl,curlA,curlB,hh]

lemma dirD_spaceCurl {F : Field} (hF : ContDiff ℝ ∞ F) (e p : ℝ × Vec) :
    dirD (spaceCurl F) e p = spaceCurl (dirD F e) p := by
  ext i
  rw [← dirD_component ((contDiff_spaceCurl hF).differentiable (by simp))]
  change dirD (fun q => dirD F (0,basis (curlA i)) q (curlB i) -
    dirD F (0,basis (curlB i)) q (curlA i)) e p = _
  rw [dirD_sub ((contDiff_component (contDiff_dirD hF _) _).differentiable (by simp))
    ((contDiff_component (contDiff_dirD hF _) _).differentiable (by simp))]
  dsimp only
  rw [dirD_component ((contDiff_dirD hF _).differentiable (by simp)),
    dirD_component ((contDiff_dirD hF _).differentiable (by simp)),
    dirD_comm hF (0,basis (curlA i)) e,dirD_comm hF (0,basis (curlB i)) e]
  rfl

lemma spaceCurl_sub {F G : Field} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) :
    spaceCurl (fun p => F p-G p) = fun p => spaceCurl F p-spaceCurl G p := by
  funext p
  ext i
  simp only [spaceCurl_apply,dirD_sub hF hG,PiLp.sub_apply]
  ring

lemma spaceCurl_add {F G : Field} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) :
    spaceCurl (fun p => F p+G p) = fun p => spaceCurl F p+spaceCurl G p := by
  funext p
  ext i
  simp only [spaceCurl_apply,dirD_add hF hG,PiLp.add_apply]
  ring

lemma spaceCurl_neg (F : Field) : spaceCurl (fun p => -F p) = fun p => -spaceCurl F p := by
  funext p
  ext i
  simp [spaceCurl_apply,dirD,fderiv_fun_neg,PiLp.neg_apply]
  ring

lemma contDiff_field_slice {F : Field} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => F (t,x)) := hF.comp (contDiff_const.prodMk contDiff_id)

lemma spaceCurl_spaceCurl_component {F : Field} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (x : Vec) (i : Fin 3) :
    spaceCurl (spaceCurl F) (t,x) i =
      spatialPartial (divergence (fun y => F (t,y))) x i-laplace (fun y => F (t,y) i) x := by
  rw [spaceCurl_slice ((contDiff_spaceCurl hF).differentiable (by simp))]
  have he : (fun y => spaceCurl F (t,y)) = curl (fun y => F (t,y)) :=
    funext (spaceCurl_slice (hF.differentiable (by simp)) t)
  rw [he,curl_curl_component (contDiff_field_slice hF t)]

lemma dirD_eq_of_eventuallyEq {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F G : H → W} {p : H}
    (h : F =ᶠ[𝓝 p] G) (e : H) : dirD F e p = dirD G e p := by
  unfold dirD
  rw [h.fderiv_eq]

lemma positive_time_eventuallyEq {W : Type*} {F G : ℝ × Vec → W}
    (h : ∀ t, 0<t → ∀ x, F (t,x)=G (t,x)) {t : ℝ} (ht : 0<t) (x : Vec) :
    F =ᶠ[𝓝 (t,x)] G := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds ht] with p hp
  exact h p.1 hp p.2

lemma spaceCurl_eq_of_eventuallyEq {F G : Field} {p : ℝ × Vec}
    (h : F =ᶠ[𝓝 p] G) : spaceCurl F p=spaceCurl G p := by
  ext i
  simp only [spaceCurl_apply,dirD_eq_of_eventuallyEq h]

lemma interval_time_eventuallyEq {W : Type*} {F G : ℝ × Vec → W} {a b t : ℝ}
    (h : ∀ r ∈ Ioo a b, ∀ x, F (r,x)=G (r,x)) (ht : t ∈ Ioo a b) (x : Vec) :
    F =ᶠ[𝓝 (t,x)] G := by
  filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds ht] with p hp
  exact h p.1 hp p.2

lemma dirD_dirD_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : ContDiff ℝ ∞ F) (e v p : H) (i : Fin 3) :
    dirD (dirD (fun q => F q i) e) v p = dirD (dirD F e) v p i := by
  have hh : dirD (fun q => F q i) e = fun q => dirD F e q i :=
    funext (fun q => dirD_component (hF.differentiable (by simp)) q e i)
  rw [hh,dirD_component ((contDiff_dirD hF e).differentiable (by simp))]

lemma waveBox_component_eq {F : Field} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : Vec) (i : Fin 3) :
    waveBox (fun p => F p i) (t,x) = dirD (dirD F (1,0)) (1,0) (t,x) i -
      laplace (fun y => F (t,y) i) x := by
  rw [waveBox_eq (contDiff_component hF i),
    deriv_deriv_slice_eq_dirD (contDiff_component hF i),dirD_dirD_component hF]

lemma maxwell_electric_wave {E B j : Field} {ρ : ℝ × Vec → ℝ} {a b t : ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (hj : ContDiff ℝ ∞ j)
    (hEt : ∀ r ∈ Ioo a b, ∀ x, dirD E (1,0) (r,x)=spaceCurl B (r,x)-j (r,x))
    (hBt : ∀ r ∈ Ioo a b, ∀ x, dirD B (1,0) (r,x) = -spaceCurl E (r,x))
    (hDiv : ∀ r ∈ Ioo a b, ∀ x, divergence (fun y => E (r,y)) x=ρ (r,x))
    (ht : t ∈ Ioo a b) (x : Vec) (i : Fin 3) :
    waveBox (fun p => E p i) (t,x) = -spatialPartial (fun y => ρ (t,y)) x i-
      dirD j (1,0) (t,x) i := by
  have hdd := dirD_eq_of_eventuallyEq (interval_time_eventuallyEq (F:=dirD E (1,0)) (G:=fun p => spaceCurl B p-j p) hEt ht x) (1,0)
  rw [dirD_sub ((contDiff_spaceCurl hB).differentiable (by simp))
    (hj.differentiable (by simp))] at hdd
  dsimp only at hdd
  rw [dirD_spaceCurl hB] at hdd
  have hc := spaceCurl_eq_of_eventuallyEq (interval_time_eventuallyEq (F:=dirD B (1,0)) (G:=fun p => -spaceCurl E p) hBt ht x)
  rw [spaceCurl_neg] at hc
  rw [hc] at hdd
  rw [waveBox_component_eq hE,hdd,PiLp.sub_apply,PiLp.neg_apply,
    spaceCurl_spaceCurl_component hE]
  have hd : divergence (fun y => E (t,y)) = fun y => ρ (t,y) := funext (hDiv t ht)
  rw [hd]
  ring

lemma maxwell_magnetic_wave {E B j : Field} {a b t : ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (hj : ContDiff ℝ ∞ j)
    (hEt : ∀ r ∈ Ioo a b, ∀ x, dirD E (1,0) (r,x)=spaceCurl B (r,x)-j (r,x))
    (hBt : ∀ r ∈ Ioo a b, ∀ x, dirD B (1,0) (r,x) = -spaceCurl E (r,x))
    (hDiv : ∀ r ∈ Ioo a b, ∀ x, divergence (fun y => B (r,y)) x=0)
    (ht : t ∈ Ioo a b) (x : Vec) (i : Fin 3) :
    waveBox (fun p => B p i) (t,x) = spaceCurl j (t,x) i := by
  have hdd := dirD_eq_of_eventuallyEq (interval_time_eventuallyEq (F:=dirD B (1,0)) (G:=fun p => -spaceCurl E p) hBt ht x) (1,0)
  have hn : dirD (fun p => -spaceCurl E p) (1,0) (t,x) = -dirD (spaceCurl E) (1,0) (t,x) := by
    simp [dirD,fderiv_fun_neg]
  rw [hn,dirD_spaceCurl hE] at hdd
  have hc := spaceCurl_eq_of_eventuallyEq (interval_time_eventuallyEq (F:=dirD E (1,0)) (G:=fun p => spaceCurl B p-j p) hEt ht x)
  rw [spaceCurl_sub ((contDiff_spaceCurl hB).differentiable (by simp))
    (hj.differentiable (by simp))] at hc
  dsimp only at hc
  rw [hc] at hdd
  rw [waveBox_component_eq hB,hdd,PiLp.neg_apply,PiLp.sub_apply,
    spaceCurl_spaceCurl_component hB]
  have hd : divergence (fun y => B (t,y)) = fun _ => (0:ℝ) := funext (hDiv t ht)
  rw [hd]
  simp [spatialPartial]
end RVM

end

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
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma dirD_spatial_slice {F : ℝ × Vec → ℝ} (hF : Differentiable ℝ F)
    (t : ℝ) (x : Vec) (i : Fin 3) :
    dirD F (0,basis i) (t,x)=spatialPartial (fun y => F (t,y)) x i :=
  (spatialPartial_time_slice (hF (t,x)) i).symm

lemma waveBox_dirD_sourceWave {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {t : ℝ} (ht : 0<t) (x : Vec) (e : ℝ × Vec) :
    waveBox (dirD (sourceWave ρ) e) (t,x)=dirD ρ e (t,x) := by
  rw [waveBox_dirD (contDiff_sourceWave hρ)]
  apply dirD_eq_of_eventuallyEq
  exact positive_time_eventuallyEq (fun r hr y => sourceWave_box hρ hr.le y) ht x

lemma sourceWave_space_initial {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (x : Vec) (i : Fin 3) : dirD (sourceWave ρ) (0,basis i) (0,x)=0 := by
  rw [dirD_spatial_slice ((contDiff_sourceWave hρ).differentiable (by simp))]
  have hh : (fun y => sourceWave ρ (0,y)) = fun _ => (0:ℝ) :=
    funext (sourceWave_initial_value ρ)
  rw [hh]
  simp [spatialPartial]

lemma sourceWave_time_initial {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (x : Vec) : dirD (sourceWave ρ) (1,0) (0,x)=0 := by
  rw [← deriv_slice_eq_dirD ((contDiff_sourceWave hρ).differentiable (by simp)),
    sourceWave_initial_velocity hρ]

lemma sourceWave_time_time_initial {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (x : Vec) : dirD (dirD (sourceWave ρ) (1,0)) (1,0) (0,x)=ρ (0,x) := by
  rw [← deriv_deriv_slice_eq_dirD (contDiff_sourceWave hρ),
    sourceWave_equation hρ x (le_refl 0)]
  have hh : (fun y => sourceWave ρ (0,y)) = fun _ => (0:ℝ) :=
    funext (sourceWave_initial_value ρ)
  rw [hh]
  simp [laplace,divergence,spatialPartial]

lemma sourceWave_space_time_initial {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (x : Vec) (i : Fin 3) :
    dirD (dirD (sourceWave ρ) (0,basis i)) (1,0) (0,x)=0 := by
  rw [dirD_comm (contDiff_sourceWave hρ),
    dirD_spatial_slice ((contDiff_dirD (contDiff_sourceWave hρ) _).differentiable (by simp))]
  have hh : (fun y => dirD (sourceWave ρ) (1,0) (0,y)) = fun _ => (0:ℝ) :=
    funext (sourceWave_time_initial hρ)
  rw [hh]
  simp [spatialPartial]

def electricPotentialComponent (ρ : ℝ × Vec → ℝ) (j : Field) (i : Fin 3) : ℝ × Vec → ℝ :=
  fun p => -dirD (sourceWave ρ) (0,basis i) p - dirD (sourceWave (fun q => j q i)) (1,0) p

lemma contDiff_electricPotentialComponent {ρ : ℝ × Vec → ℝ} {j : Field}
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) (i : Fin 3) :
    ContDiff ℝ ∞ (electricPotentialComponent ρ j i) :=
  (contDiff_dirD (contDiff_sourceWave hρ) _).neg.sub
    (contDiff_dirD (contDiff_sourceWave (contDiff_component hj i)) _)

lemma electricPotentialComponent_initial {ρ : ℝ × Vec → ℝ} {j : Field}
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) (x : Vec) (i : Fin 3) :
    electricPotentialComponent ρ j i (0,x)=0 := by
  simp only [electricPotentialComponent,sourceWave_space_initial hρ,
    sourceWave_time_initial (contDiff_component hj i),neg_zero,sub_zero]

lemma electricPotentialComponent_initial_velocity {ρ : ℝ × Vec → ℝ} {j : Field}
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) (x : Vec) (i : Fin 3) :
    deriv (fun t => electricPotentialComponent ρ j i (t,x)) 0 = -j (0,x) i := by
  rw [deriv_slice_eq_dirD ((contDiff_electricPotentialComponent hρ hj i).differentiable (by simp))]
  unfold electricPotentialComponent
  rw [dirD_sub ((contDiff_dirD (contDiff_sourceWave hρ) _).neg.differentiable (by simp))
    ((contDiff_dirD (contDiff_sourceWave (contDiff_component hj i)) _).differentiable (by simp))]
  dsimp only
  simp only [dirD,fderiv_fun_neg,neg_apply]
  change -dirD (dirD (sourceWave ρ) (0,basis i)) (1,0) (0,x) -
    dirD (dirD (sourceWave (fun p => j p i)) (1,0)) (1,0) (0,x) = _
  rw [sourceWave_space_time_initial hρ,sourceWave_time_time_initial (contDiff_component hj i)]
  ring

lemma waveBox_neg (u : ℝ × Vec → ℝ) :
    waveBox (fun p => -u p)=fun p => -waveBox u p := by
  have hd (F : ℝ × Vec → ℝ) (e : ℝ × Vec) :
      dirD (fun p => -F p) e=fun p => -dirD F e p := by
    funext p
    simp [dirD,fderiv_fun_neg]
  funext p
  simp only [waveBox,hd,Finset.sum_neg_distrib]
  ring

lemma electricPotentialComponent_box {ρ : ℝ × Vec → ℝ} {j : Field}
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) {t : ℝ} (ht : 0<t)
    (x : Vec) (i : Fin 3) :
    waveBox (electricPotentialComponent ρ j i) (t,x)=
      -spatialPartial (fun y => ρ (t,y)) x i - dirD j (1,0) (t,x) i := by
  unfold electricPotentialComponent
  rw [waveBox_sub (contDiff_dirD (contDiff_sourceWave hρ) _).neg
    (contDiff_dirD (contDiff_sourceWave (contDiff_component hj i)) _),
    waveBox_neg]
  dsimp only
  rw [waveBox_dirD_sourceWave hρ ht,waveBox_dirD_sourceWave (contDiff_component hj i) ht,
    dirD_spatial_slice (hρ.differentiable (by simp)),dirD_component (hj.differentiable (by simp))]

lemma maxwell_electric_potential_representation {E B j : Field} {ρ : ℝ × Vec → ℝ} {T : ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (hj : ContDiff ℝ ∞ j)
    (hρ : ContDiff ℝ ∞ ρ) (hT : 0≤T)
    (hEt : ∀ r ∈ Icc 0 T, ∀ x, dirD E (1,0) (r,x)=spaceCurl B (r,x)-j (r,x))
    (hBt : ∀ r ∈ Ioo 0 T, ∀ x, dirD B (1,0) (r,x) = -spaceCurl E (r,x))
    (hDiv : ∀ r ∈ Ioo 0 T, ∀ x, divergence (fun y => E (r,y)) x=ρ (r,x))
    (x : Vec) (i : Fin 3) :
    E (T,x) i = freeWave (fun y => E (0,y) i) (fun y => spaceCurl B (0,y) i) (T,x) +
      electricPotentialComponent ρ j i (T,x) := by
  have hg := contDiff_component (contDiff_field_slice hE 0) i
  have hh := contDiff_component (contDiff_field_slice (contDiff_spaceCurl hB) 0) i
  have hfree := contDiff_freeWave hg hh
  have hpot := contDiff_electricPotentialComponent hρ hj i
  apply wave_unique_on (contDiff_component hE i) (hfree.add hpot) hT
  · intro r hr y
    rw [waveBox_add hfree hpot]
    dsimp only
    rw [freeWave_box hg hh hr.1,electricPotentialComponent_box hρ hj hr.1,zero_add]
    exact maxwell_electric_wave hE hB hj
      (fun r hr => hEt r ⟨hr.1.le,hr.2.le⟩) hBt hDiv hr y i
  · intro y
    rw [freeWave_initial hg,electricPotentialComponent_initial hρ hj,add_zero]
  · intro y
    have hfdy : DifferentiableAt ℝ (fun t => freeWave (fun z => E (0,z) i)
        (fun z => spaceCurl B (0,z) i) (t,y)) 0 := by
      exact (((hfree.differentiable (by simp)).comp
        (differentiable_id.prodMk (differentiable_const y))) 0)
    have hpdy : DifferentiableAt ℝ (fun t => electricPotentialComponent ρ j i (t,y)) 0 := by
      exact (((hpot.differentiable (by simp)).comp
        (differentiable_id.prodMk (differentiable_const y))) 0)
    rw [deriv_fun_add hfdy hpdy,
      freeWave_initial_velocity hg hh,electricPotentialComponent_initial_velocity hρ hj,
      deriv_slice_eq_dirD ((contDiff_component hE i).differentiable (by simp)),
      dirD_component (hE.differentiable (by simp)),hEt 0 ⟨le_rfl,hT⟩]
    rfl
def magneticPotentialComponent (j : Field) (i : Fin 3) : ℝ × Vec → ℝ :=
  fun p => dirD (sourceWave (fun q => j q (curlB i))) (0,basis (curlA i)) p -
    dirD (sourceWave (fun q => j q (curlA i))) (0,basis (curlB i)) p

lemma contDiff_magneticPotentialComponent {j : Field} (hj : ContDiff ℝ ∞ j) (i : Fin 3) :
    ContDiff ℝ ∞ (magneticPotentialComponent j i) :=
  (contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _).sub
    (contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _)

lemma magneticPotentialComponent_initial {j : Field} (hj : ContDiff ℝ ∞ j) (x : Vec) (i : Fin 3) :
    magneticPotentialComponent j i (0,x)=0 := by
  simp only [magneticPotentialComponent,sourceWave_space_initial (contDiff_component hj _),sub_self]

lemma magneticPotentialComponent_initial_velocity {j : Field} (hj : ContDiff ℝ ∞ j)
    (x : Vec) (i : Fin 3) : deriv (fun t => magneticPotentialComponent j i (t,x)) 0 = 0 := by
  rw [deriv_slice_eq_dirD ((contDiff_magneticPotentialComponent hj i).differentiable (by simp))]
  unfold magneticPotentialComponent
  rw [dirD_sub ((contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _).differentiable (by simp))
    ((contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _).differentiable (by simp))]
  dsimp only
  rw [sourceWave_space_time_initial (contDiff_component hj _),
    sourceWave_space_time_initial (contDiff_component hj _),sub_self]

lemma magneticPotentialComponent_box {j : Field} (hj : ContDiff ℝ ∞ j)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    waveBox (magneticPotentialComponent j i) (t,x)=spaceCurl j (t,x) i := by
  unfold magneticPotentialComponent
  rw [waveBox_sub (contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _)
    (contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _)]
  dsimp only
  rw [waveBox_dirD_sourceWave (contDiff_component hj _) ht,
    waveBox_dirD_sourceWave (contDiff_component hj _) ht,
    dirD_component (hj.differentiable (by simp)),dirD_component (hj.differentiable (by simp))]
  rfl

lemma maxwell_magnetic_potential_representation {E B j : Field} {T : ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (hj : ContDiff ℝ ∞ j) (hT : 0≤T)
    (hEt : ∀ r ∈ Ioo 0 T, ∀ x, dirD E (1,0) (r,x)=spaceCurl B (r,x)-j (r,x))
    (hBt : ∀ r ∈ Icc 0 T, ∀ x, dirD B (1,0) (r,x) = -spaceCurl E (r,x))
    (hDiv : ∀ r ∈ Ioo 0 T, ∀ x, divergence (fun y => B (r,y)) x=0)
    (x : Vec) (i : Fin 3) :
    B (T,x) i = freeWave (fun y => B (0,y) i) (fun y => -spaceCurl E (0,y) i) (T,x) +
      magneticPotentialComponent j i (T,x) := by
  have hg := contDiff_component (contDiff_field_slice hB 0) i
  have hh := (contDiff_component (contDiff_field_slice (contDiff_spaceCurl hE) 0) i).neg
  have hfree := contDiff_freeWave hg hh
  have hpot := contDiff_magneticPotentialComponent hj i
  apply wave_unique_on (contDiff_component hB i) (hfree.add hpot) hT
  · intro r hr y
    rw [waveBox_add hfree hpot]
    dsimp only
    rw [freeWave_box hg hh hr.1,magneticPotentialComponent_box hj hr.1,zero_add]
    exact maxwell_magnetic_wave hE hB hj hEt
      (fun r hr => hBt r ⟨hr.1.le,hr.2.le⟩) hDiv hr y i
  · intro y
    rw [freeWave_initial hg,magneticPotentialComponent_initial hj,add_zero]
  · intro y
    have hfdy : DifferentiableAt ℝ (fun t => freeWave (fun z => B (0,z) i)
        (fun z => -spaceCurl E (0,z) i) (t,y)) 0 := by
      exact (((hfree.differentiable (by simp)).comp
        (differentiable_id.prodMk (differentiable_const y))) 0)
    have hpdy : DifferentiableAt ℝ (fun t => magneticPotentialComponent j i (t,y)) 0 := by
      exact (((hpot.differentiable (by simp)).comp
        (differentiable_id.prodMk (differentiable_const y))) 0)
    rw [deriv_fun_add hfdy hpdy,
      freeWave_initial_velocity hg hh,magneticPotentialComponent_initial_velocity hj,
      deriv_slice_eq_dirD ((contDiff_component hB i).differentiable (by simp)),
      dirD_component (hB.differentiable (by simp)),hBt 0 ⟨le_rfl,hT⟩]
    simp
end RVM

end

end OAI
