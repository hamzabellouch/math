import Mathlib
import OAI.Analysis.Conductivity.Geometry.TorusLeadingDecay
import OAI.Analysis.Conductivity.Fourier.PeriodicFamilyCorrection
import OAI.Analysis.Conductivity.Flux.TorusBoxFlux
import OAI.Analysis.Conductivity.Fourier.FlatFourierFlux

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma torusCellIntegral_norm_le {T C t : ℝ} (hT : 0≤T) {f : Coord3 → ℝ}
    (hf : ∀ y z,‖f ![t,y,z]‖≤C) : ‖torusCellIntegral T f t‖≤C*T^2 := by
  have hz (y : ℝ) : ‖∫ z in (0:ℝ)..T,f ![t,y,z]‖≤C*T := by
    simpa only [sub_zero,abs_of_nonneg hT] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=T) (fun z _ => hf y z))
  have hy := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=T) (fun y _ => hz y)
  simpa only [sub_zero,abs_of_nonneg hT,torusCellIntegral,pow_two,mul_assoc] using hy

lemma torusCellIntegral_tendsto_zero {T : ℝ} (hT : 0≤T) {f : Coord3 → ℝ} {b : ℝ→ℝ}
    (hb : Tendsto b atTop (𝓝 0)) (hf : ∀ᶠ t in atTop,∀ y z,‖f ![t,y,z]‖≤b t) :
    Tendsto (torusCellIntegral T f) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (hf.mono (fun t ht => torusCellIntegral_norm_le hT ht))
  simpa using hb.mul_const (T^2)

lemma flatFourier_exponential_bound {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B gap : ℝ} (ha : ∀ h,|a h|≤B) (hg : 0≤gap)
    (hr : ∀ h,a h≠0 → gap≤torusRate s h) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ x : Coord3,1≤x 0 →
      ‖iteratedFDeriv ℝ n (flatFourier s a phase) x‖≤C*exp (-gap*(x 0-1)) := by
  let C := ∑' h,B*((torusRate s h+torusSize h)^n*exp (-torusRate s h))
  have hB : 0≤B := (abs_nonneg (a 0)).trans (ha 0)
  refine ⟨C,tsum_nonneg (fun h => ?_),?_⟩
  · have ht := sqrt_nonneg (torusQuadratic s h)
    have hz := torusSize_nonneg h
    exact mul_nonneg hB (mul_nonneg (pow_nonneg (add_nonneg ht hz) n) (exp_nonneg _))
  · intro x hx
    have he : ![0,x 1,x 2]+![x 0,0,0]=x := by ext i; fin_cases i <;> simp
    have hh := flatFourier_shift_uniform_bound (a:=a) (phase:=phase) (lam:=0) (R:=0) (T:=x 0)
      hs ha le_rfl hg (by simpa only [zero_add] using hr) (by simpa using hx)
      n (x:=![0,x 1,x 2]) (by simp)
    rw [he] at hh
    simpa [C,mul_comm] using hh

lemma tendsto_exp_neg_gap {gap : ℝ} (hg : 0<gap) :
    Tendsto (fun t : ℝ => exp (-gap*(t-1))) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  exact (tendsto_atTop_add_const_right atTop (-1) tendsto_id).const_mul_atTop_of_neg (neg_neg_of_pos hg)

lemma flatFourier_mean_axial_flux_zero {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B gap t : ℝ} (ha : ∀ h,|a h|≤B) (hg : 0<gap)
    (hr : ∀ h,a h≠0 → gap≤torusRate s h) (ht : 0<t) :
    torusCellIntegral (2*Real.pi) (fun x => fderiv ℝ (flatFourier s a phase) x (flatAxis 0)) t=0 := by
  apply torus_flux_zero_of_tendsto (F:=flatModeFlux s (flatFourier s a phase)) ht
    (by positivity) (flatModeFlux_smoothOn (axial_halfspace_open 0) (flatFourier_smooth hs ha))
    (flatModeFlux_periodic (flatFourier_angularPeriodic s a phase))
    (fun x hx => flatFourier_flux_divergence hs ha hx)
  obtain ⟨C,hC,hb⟩ := flatFourier_exponential_bound (phase:=phase) hs ha hg.le hr 1
  apply torusCellIntegral_tendsto_zero (by positivity : (0:ℝ)≤2*Real.pi)
    (by simpa using (tendsto_exp_neg_gap hg).const_mul C)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht'
  intro y z
  simp only [flatModeFlux,Matrix.cons_val_zero]
  rw [←neg_mul]
  have hn : ‖flatAxis (0:Fin 3)‖=1 := by simp [flatAxis,Pi.norm_single]
  have hh := (fderiv ℝ (flatFourier s a phase) ![t,y,z]).le_opNorm (flatAxis 0)
  rw [hn,mul_one,←norm_iteratedFDeriv_one] at hh
  exact hh.trans (hb _ ht')

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma coordinateDivergence_smul_at {f : Coord3 → ℝ} {F : Coord3 → Coord3} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) (hF : DifferentiableAt ℝ F x) :
    coordinateDivergence (fun y => f y • F y) x=
      f x*coordinateDivergence F x+fderiv ℝ f x (F x) := by
  have he (i : Fin 3) :
      fderiv ℝ (fun y => (f y • F y) i) x (Pi.single i 1)=
        f x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)+
        F x i*fderiv ℝ f x (Pi.single i 1) := by
    change fderiv ℝ (fun y => f y*F y i) x _=_
    rw [fderiv_fun_mul hf ((hasFDerivAt_pi'.mp hF.hasFDerivAt i).differentiableAt)]
    rfl
  simp only [coordinateDivergence,he,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [←coordinate_fderiv_expansion]

lemma coordinateDivergence_sub_at {F G : Coord3 → Coord3} {x : Coord3}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    coordinateDivergence (fun y => F y-G y) x=coordinateDivergence F x-coordinateDivergence G x := by
  unfold coordinateDivergence
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ (fun y => F y i-G y i) x _=_
  rw [fderiv_fun_sub ((hasFDerivAt_pi'.mp hF.hasFDerivAt i).differentiableAt)
    ((hasFDerivAt_pi'.mp hG.hasFDerivAt i).differentiableAt)]
  rfl

lemma flat_flux_pairing (s : Fin 3→ℝ) (f g : Coord3→ℝ) (x : Coord3) :
    fderiv ℝ g x (flatModeFlux s f x)=fderiv ℝ f x (flatModeFlux s g x) := by
  rw [coordinate_fderiv_expansion,coordinate_fderiv_expansion]
  simp only [Fin.sum_univ_three,flatModeFlux,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,flatAxis]
  ring

def flatCrossFlux (s : Fin 3→ℝ) (f g : Coord3→ℝ) (x : Coord3) : Coord3 :=
  g x • flatModeFlux s f x-f x • flatModeFlux s g x

lemma flatCrossFlux_smoothOn {s : Fin 3→ℝ} {f g : Coord3→ℝ} {U : Set Coord3}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f U)
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (flatCrossFlux s f g) U :=
  (hg.smul (flatModeFlux_smoothOn hU hf)).sub (hf.smul (flatModeFlux_smoothOn hU hg))

lemma flatModeFlux_differentiableAt {s : Fin 3→ℝ} {f : Coord3→ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ (↑(⊤:ℕ∞)) f x) : DifferentiableAt ℝ (flatModeFlux s f) x := by
  have hd := (hf.fderiv_right (m:=1)
    (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))).differentiableAt (by simp)
  have he (i : Fin 3) := hd.clm_apply (differentiableAt_const (flatAxis i))
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · exact he 0
  · exact ((he 1).const_mul _).add ((he 2).const_mul _)
  · exact ((he 1).const_mul _).add ((he 2).const_mul _)

lemma flatCrossFlux_divergence {s : Fin 3→ℝ} {f g : Coord3→ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ (↑(⊤:ℕ∞)) f x) (hg : ContDiffAt ℝ (↑(⊤:ℕ∞)) g x) :
    coordinateDivergence (flatCrossFlux s f g) x=
      g x*flatTensorLaplacian s f x-f x*flatTensorLaplacian s g x := by
  have hfd := hf.differentiableAt (by simp)
  have hgd := hg.differentiableAt (by simp)
  have hff := flatModeFlux_differentiableAt (s:=s) hf
  have hgf := flatModeFlux_differentiableAt (s:=s) hg
  unfold flatCrossFlux
  rw [coordinateDivergence_sub_at (F:=fun y => g y • flatModeFlux s f y)
    (G:=fun y => f y • flatModeFlux s g y) (hgd.smul hff) (hfd.smul hgf),
    coordinateDivergence_smul_at hgd hff,coordinateDivergence_smul_at hfd hgf,
    flatModeFlux_divergence hf,flatModeFlux_divergence hg,flat_flux_pairing s f g x]
  ring

lemma flatCrossFlux_periodic {s : Fin 3→ℝ} {f g : Coord3→ℝ} {T : ℝ}
    (hf : AngularPeriodic T f) (hg : AngularPeriodic T g) : AngularPeriodic T (flatCrossFlux s f g) := by
  intro n x
  unfold flatCrossFlux
  rw [hg n x,hf n x,flatModeFlux_periodic hf n x,flatModeFlux_periodic hg n x]

end ScalarConductivity

end

end OAI
