import OAI.Analysis.LienardCycles.ActualReflection

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
namespace QuinticLienard.ScaledProfile
lemma intercept_ratio_strictMono {a : Fin 6 → ℝ} {d : ℝ}
    (hp : ∀ u, 0<u → 0<u*curvature a u-slope a u+d) :
    StrictMonoOn (fun u=>(slope a u-d)/u) (Ioi 0) := by
  have hd (u : ℝ) (hu : 0<u) := ((slope_hasDerivAt a hu).sub_const d).div (hasDerivAt_id u) hu.ne'
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun u hu=>(hd u hu).continuousAt.continuousWithinAt)
  intro u hu
  have hu' : 0<u := interior_subset hu
  rw [(hd u hu').deriv]
  apply div_pos _ (sq_pos_of_pos hu')
  simp only [id_eq,mul_one]
  nlinarith [hp u hu']
end QuinticLienard.ScaledProfile
namespace QuinticLienard.QuinticFit
open ScaledProfile QuadraticCoordinates PartialCalculus
noncomputable def intercept (a : Fin 6 → ℝ) (d : ℝ) (q : ℝ × ℝ) : ℝ := lambda a q-q.1*kappa a q-d
lemma intercept_analytic (a : Fin 6 → ℝ) (d : ℝ) {h r : ℝ} (hh : 0<h) (hr : 0<r) :
    ContDiffAt ℝ ω (intercept a d) (h,r) :=
  ((lambda_analytic a hh hr).sub (contDiffAt_fst.mul (kappa_analytic a hh hr))).sub contDiffAt_const
lemma profile_gt_intercept {a : Fin 6 → ℝ} {h κ d : ℝ} (hh : 0<h)
    (hp : ∀ u, 0<u → 0<u*curvature a u-slope a u+d)
    (hκ : κ≤(slope a h-d)/h) :
    ∀ u, h<u → QuinticProfile.profile a (0,u)-QuinticProfile.profile a (0,h)>
      (d+h*κ)*(u-h)+κ*(u-h)^2/2 := by
  let f : ℝ → ℝ := fun u=>QuinticProfile.profile a (0,u)-(d+h*κ)*(u-h)-κ*(u-h)^2/2
  have hd (u : ℝ) (hu : h≤u) : HasDerivAt f (slope a u-d-κ*u) u := by
    convert! ((profile_hasDerivAt a (hh.trans_le hu)).sub
      (((hasDerivAt_id u).sub_const h).const_mul (d+h*κ))).sub
        ((((hasDerivAt_id u).sub_const h).pow 2).const_mul κ |>.div_const 2) using 1
    simp only [id_eq]
    ring
  have hm : StrictMonoOn f (Ici h) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici h)
      (fun u hu=>(hd u hu).continuousAt.continuousWithinAt)
    intro u hu
    have hhu : h<u := by simpa only [interior_Ici,mem_Ioi] using hu
    rw [(hd u hhu.le).deriv]
    have hx := hκ.trans_lt (intercept_ratio_strictMono hp hh (hh.trans hhu) hhu)
    have hx' := (lt_div_iff₀ (hh.trans hhu)).mp hx
    linarith
  intro u hu
  have he := hm (show h ∈ Set.Ici h by exact le_refl h) (show u ∈ Set.Ici h by exact hu.le) hu
  dsimp [f] at he
  nlinarith
lemma intercept_zero_slope_gt {a : Fin 6 → ℝ} {d h r : ℝ} (hh : 0<h) (hr : 0<r)
    (hp : ∀ u, 0<u → 0<u*curvature a u-slope a u+d)
    (hz : intercept a d (h,r)=0) : slope a h<lambda a (h,r) := by
  by_contra! hn
  have hl : lambda a (h,r)=d+h*kappa a (h,r) := by
    dsimp only [intercept] at hz
    linarith
  have hk : kappa a (h,r)≤(slope a h-d)/h := (le_div_iff₀ hh).mpr (by nlinarith)
  have hm := midpoint_gt_quadratic hh hr (profile_gt_intercept hh hp hk)
  rw [←hl] at hm
  change H (fit a (h,r)) < M a (h,r) at hm
  rw [(spec a hh hr).1] at hm
  exact (lt_irrefl _) hm
end QuinticLienard.QuinticFit
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuadraticCoordinates
noncomputable def interceptRate (a : Fin 6 → ℝ) (t s : ℝ) : ℝ :=
  g a t s/s*((S (QuinticFit.fit a (point a t s))+b a t s*R (QuinticFit.fit a (point a t s)))/G (QuinticFit.fit a (point a t s)))*
    (QuinticFit.lambda a (point a t s)-k a t s)
lemma intercept_deriv {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r) (d : ℝ) :
    HasDerivAt (fun s=>QuinticFit.intercept a d (point a t s)) (-interceptRate a t r) r := by
  have hl := along_deriv he ((QuinticFit.lambda_analytic a (base_spec he).1 (radius_pos he)).differentiableAt (by simp))
  have hk := along_deriv he ((QuinticFit.kappa_analytic a (base_spec he).1 (radius_pos he)).differentiableAt (by simp))
  have htr := QuinticFit.fit_transport a (base_spec he).1 (radius_pos he)
  have hL : QuinticFit.D a (QuinticFit.lambda a) (point a t r)=QuinticFit.kappa a (point a t r)+
      S (QuinticFit.fit a (point a t r))/G (QuinticFit.fit a (point a t r))*(QuinticFit.lambda a (point a t r)-k a t r) := by
    dsimp only [point,k]
    linarith only [htr.2.2]
  dsimp only [point] at hk
  rw [htr.2.1] at hk
  rw [hL] at hl
  convert! (hl.sub ((base_deriv he).mul hk)).sub_const d using 1
  dsimp only [interceptRate,point,k]
  ring
lemma intercept_small {a : Fin 6 → ℝ} {t r d : ℝ} (he : Adm a t r)
    (hp : ∀ u, 0<u → 0<u*ScaledProfile.curvature a u-ScaledProfile.slope a u+d) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), QuinticFit.intercept a d (point a t s)<0 := by
  have ht : 0<t := (base_spec he).1.trans (base_spec he).2.1
  have hl := QuinticFit.fit_limits (a:=a) ht (base_tendsto he)
    (tendsto_id.mono_left inf_le_left) self_mem_nhdsWithin
  have hlim := (hl.1.sub ((base_tendsto he).mul hl.2)).sub_const d
  have hn : ScaledProfile.slope a t-t*ScaledProfile.curvature a t-d<0 := by linarith [hp t ht]
  exact hlim.eventually (eventually_lt_nhds hn)
lemma intercept_lt {a : Fin 6 → ℝ} {t r d : ℝ} (he : Adm a t r)
    (hp : ∀ u, 0<u → 0<u*ScaledProfile.curvature a u-ScaledProfile.slope a u+d) :
    QuinticFit.intercept a d (point a t r)<0 := by
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s ∧ s<r ∧ QuinticFit.intercept a d (point a t s)<0 := by
    filter_upwards [intercept_small he hp,self_mem_nhdsWithin,
      (eventually_lt_nhds (radius_pos he)).filter_mono inf_le_left] with s hs hs0 hsr
    exact ⟨hs0,hsr,hs⟩
  obtain ⟨s,hs,hsr,hIs⟩ := hev.exists
  have hd (u : ℝ) (hu : u ∈ Icc s r) : HasDerivAt
      (fun v=>-QuinticFit.intercept a d (point a t v)) (interceptRate a t u) u := by
    convert! (intercept_deriv (adm_le he (hs.trans_le hu.1) hu.2) d).const_mul (-1) using 1 <;> simp
  have hit := RealAnalysis.positive_of_deriv_pos_at_zero hsr
    (fun u hu=>(hd u hu).continuousAt.continuousWithinAt) hd (neg_pos.mpr hIs).le (fun u hu hz=>?_)
  · exact neg_pos.mp hit
  · have heu := adm_le he (hs.trans_le hu.1) hu.2
    have hI : QuinticFit.intercept a d (point a t u)=0 := neg_eq_zero.mp hz
    have hslope := QuinticFit.intercept_zero_slope_gt (base_spec heu).1 (radius_pos heu) hp hI
    dsimp only [interceptRate]
    exact mul_pos (mul_pos (div_pos (g_pos heu) (radius_pos heu))
      (div_pos (add_pos (S_pos (radius_pos heu)) (mul_pos (base_spec heu).1 (R_pos (radius_pos heu))))
        (G_pos (radius_pos heu)))) (sub_pos.mpr hslope)
end QuinticLienard.ActualCharacteristic
namespace QuinticLienard.QuinticFit
theorem intercept_negative {a : Fin 6 → ℝ} {h r d : ℝ} (hh : 0<h) (hr : 0<r)
    (hp : ∀ u, 0<u → 0<u*ScaledProfile.curvature a u-ScaledProfile.slope a u+d) :
    lambda a (h,r)-h*kappa a (h,r)<d := by
  let t := PositiveWidth.peakAtWidth (QuinticProfile.profile a) ((0,h),r)
  have ht := PositiveWidth.peak_spec (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
    (QuinticProfile.local_flow a) (p:=0) hh hr
  have he : ActualCharacteristic.Adm a t r := ⟨h,hh,ht.1,ht.2⟩
  have hb : ActualCharacteristic.b a t r=h := PositiveWidth.base_eq _
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) hh ht.1 ht.2
  have hi := ActualCharacteristic.intercept_lt he hp
  dsimp only [intercept,ActualCharacteristic.point] at hi
  rw [hb] at hi
  linarith
end QuinticLienard.QuinticFit

end OAI
