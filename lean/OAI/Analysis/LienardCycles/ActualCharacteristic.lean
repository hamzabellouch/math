import OAI.Analysis.LienardCycles.PositiveBase

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuinticFit
noncomputable def b (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := PositiveWidth.baseAtWidth (QuinticProfile.profile a) ((0,t),s)
def Adm (a : Fin 6 → ℝ) (t s : ℝ) : Prop := PositiveWidth.Admissible (QuinticProfile.profile a) ((0,t),s)
noncomputable def point (a : Fin 6 → ℝ) (t s : ℝ) : ℝ × ℝ := (b a t s,s)
noncomputable def m (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := M a (point a t s)
noncomputable def v (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := V a (point a t s)
noncomputable def A (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := m a t s/s
noncomputable def g (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := s^2-(m a t s)^2
noncomputable def k (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := ScaledProfile.slope a (b a t s)
noncomputable def c (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := ScaledProfile.curvature a (b a t s)
lemma base_spec {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    0<b a t r ∧ b a t r<t ∧ PositiveWidth.widthFamily (QuinticProfile.profile a) ((0,t),b a t r)=r :=
  PositiveWidth.base_spec _ he
lemma radius_pos {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : 0<r :=
  (base_spec he).2.2 ▸ PositiveWidth.width_pos _ (fun _ h => QuinticProfile.analytic a h) (base_spec he).1 (base_spec he).2.1
lemma m_abs_lt {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : |m a t r|<r :=
  M_abs_lt a (base_spec he).1 (radius_pos he)
lemma v_abs_lt {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : |v a t r|<1 :=
  V_abs_lt a (base_spec he).1 (radius_pos he)
lemma A_abs_lt {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : |A a t r|<1 := by
  dsimp only [A]
  rw [abs_div,abs_of_pos (radius_pos he)]
  exact (div_lt_one (radius_pos he)).mpr (m_abs_lt he)
lemma g_pos {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : 0<g a t r :=
  sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos (radius_pos he)] using m_abs_lt he))
lemma base_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (b a t) r :=
  (PositiveWidth.base_analytic _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) he).comp r
    (contDiffAt_const.prodMk contDiffAt_id)
lemma adm_eventually {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ∀ᶠ s in 𝓝 r, Adm a t s :=
  (continuousAt_const.prodMk continuousAt_id).eventually
    (PositiveWidth.base_local _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) he).2
lemma point_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (point a t) r :=
  (base_analytic he).prodMk contDiffAt_id
lemma m_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (m a t) r :=
  (M_analytic a (base_spec he).1 (radius_pos he)).comp (f:=point a t) r (point_analytic he)
lemma v_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (v a t) r :=
  (V_analytic a (base_spec he).1 (radius_pos he)).comp (f:=point a t) r (point_analytic he)
lemma A_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (A a t) r :=
  (m_analytic he).div contDiffAt_id (radius_pos he).ne'
lemma k_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (k a t) r :=
  (ScaledProfile.slope_analytic a (base_spec he).1).comp r (base_analytic he)
lemma c_analytic {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : ContDiffAt ℝ ω (c a t) r :=
  (ScaledProfile.curvature_analytic a (base_spec he).1).comp r (base_analytic he)
lemma base_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : HasDerivAt (b a t) (-g a t r/r) r := by
  have hd := PositiveWidth.base_width_deriv _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) he
  have hm := PositiveWidth.base_midpoint _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) he
  change m a t r=_ at hm
  rw [←hm] at hd
  exact hd
lemma along_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) {f : ℝ × ℝ → ℝ}
    (hf : DifferentiableAt ℝ f (point a t r)) :
    HasDerivAt (fun s => f (point a t s)) (-g a t r/r*D a f (point a t r)) r := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt r ((base_deriv he).prodMk (hasDerivAt_id r))
  rw [fderiv_pair] at hd
  convert! hd using 1
  change -g a t r/r*(first f (point a t r)-r/g a t r*second f (point a t r)) = _
  field_simp [(radius_pos he).ne',(g_pos he).ne']
  ring
lemma m_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (m a t) (-m a t r/r+g a t r/r*k a t r) r := by
  have ht := PositiveTransport.transport_midpoint (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) (base_spec he).1 (radius_pos he)
  have hp : HasDerivAt (fun u => QuinticProfile.profile a (0,u)) (ScaledProfile.slope a (b a t r)) (b a t r) := ScaledProfile.profile_hasDerivAt a (base_spec he).1
  rw [hp.deriv] at ht
  change D a (M a) (point a t r)=m a t r/g a t r-k a t r at ht
  have hd := along_deriv he ((M_analytic a (base_spec he).1 (radius_pos he)).differentiableAt (by simp))
  rw [ht] at hd
  convert! hd using 1
  field_simp [(radius_pos he).ne',(g_pos he).ne']
  ring
lemma v_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (v a t) (2*m a t r*(1-(v a t r)^2)/g a t r) r := by
  have ht := PositiveTransport.transport_v (QuinticProfile.profile a) (fun _ h => QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) (base_spec he).1 (radius_pos he)
  change D a (V a) (point a t r)= -2*m a t r*r*(1-(v a t r)^2)/(g a t r)^2 at ht
  have hd := along_deriv he ((V_analytic a (base_spec he).1 (radius_pos he)).differentiableAt (by simp))
  rw [ht] at hd
  convert! hd using 1
  field_simp [(radius_pos he).ne',(g_pos he).ne']
lemma A_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (A a t) (k a t r*(1-(A a t r)^2)-2*A a t r/r) r := by
  convert! (m_deriv he).div (hasDerivAt_id r) (radius_pos he).ne' using 1
  dsimp only [A,g,id_eq]
  field_simp [(radius_pos he).ne']
  ring
lemma k_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (k a t) (-g a t r/r*c a t r) r := by
  convert! (ScaledProfile.slope_hasDerivAt a (base_spec he).1).comp r (base_deriv he) using 1
  exact mul_comm _ _
lemma c_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    HasDerivAt (c a t) (-g a t r/r*ScaledProfile.third a (b a t r)) r := by
  convert! (ScaledProfile.curvature_hasDerivAt a (base_spec he).1).comp r (base_deriv he) using 1
  exact mul_comm _ _
noncomputable def L (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := angle (v a t s)
noncomputable def rate (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := 2*A a t s/(s*(1-(A a t s)^2))
lemma L_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) : HasDerivAt (L a t) (rate a t r) r := by
  have hd := (angle_deriv (v_abs_lt he)).comp r (v_deriv he)
  convert! hd using 1
  dsimp only [rate,A,g]
  have hv : 1-(v a t r)^2≠0 := by
    have ht := sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1) |>.mpr (v_abs_lt he)
    nlinarith [sq_abs (v a t r)]
  field_simp [(radius_pos he).ne',hv]
lemma adm_le {a : Fin 6 → ℝ} {t r s : ℝ} (he : Adm a t r) (hs : 0<s) (hsr : s≤r) : Adm a t s := by
  have hb := base_spec he
  apply PositiveWidth.base_exists_le _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hb.1 hb.2.1 hs
  rw [hb.2.2]
  exact hsr
lemma base_tendsto {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    Tendsto (b a t) (𝓝[>] (0:ℝ)) (𝓝 t) :=
  PositiveWidth.base_tendsto _ (fun _ h => QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (base_spec he).1 (base_spec he).2.1
lemma small_limits {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) :
    Tendsto (A a t) (𝓝[>] (0:ℝ)) (𝓝 0) ∧ Tendsto (L a t) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (k a t) (𝓝[>] (0:ℝ)) (𝓝 (ScaledProfile.slope a t)) ∧
    Tendsto (c a t) (𝓝[>] (0:ℝ)) (𝓝 (ScaledProfile.curvature a t)) := by
  have ht : 0<t := (base_spec he).1.trans (base_spec he).2.1
  have hl := QuinticFit.normalized_limits (a:=a) ht (base_tendsto he)
    (tendsto_id.mono_left inf_le_left) self_mem_nhdsWithin
  refine ⟨hl.1,?_,(ScaledProfile.slope_analytic a ht).continuousAt.tendsto.comp (base_tendsto he),
    (ScaledProfile.curvature_analytic a ht).continuousAt.tendsto.comp (base_tendsto he)⟩
  change Tendsto (fun s=>angle (V a (b a t s,s))) (𝓝[>] (0:ℝ)) (𝓝 0)
  simpa only [angle_zero,Function.comp_def,id_eq] using
    (angle_analytic (by norm_num : |(0:ℝ)|<1)).continuousAt.tendsto.comp hl.2
end QuinticLienard.ActualCharacteristic

end OAI
