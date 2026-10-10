import OAI.Probability.FirstPassage.PlaneGeometry
import OAI.Probability.GammaPassage.Target
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

namespace OAI

namespace GammaFPP.Analytic
open PlanarFPP Set Filter MeasureTheory
open scoped Topology
noncomputable def swapPlane : Plane ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

@[simp] lemma swapPlane_zero (v : Plane) : swapPlane v 0=v 1 := by
  simp [swapPlane,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
@[simp] lemma swapPlane_one (v : Plane) : swapPlane v 1=v 0 := by
  simp [swapPlane,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
@[simp] lemma swapPlane_swap (v : Plane) : swapPlane (swapPlane v)=v := by
  ext i; fin_cases i <;> simp

theorem plane_coordinate_le_norm (v : Plane) (i : Fin 2) : |v i| ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

theorem timeConstantNorm_lipschitz_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v w, |μ v - μ w| ≤ B * ‖v-w‖ := by
  let e0 : Plane := PiLp.single 2 0 1
  let e1 : Plane := PiLp.single 2 1 1
  let B := μ e0 + μ e1 + 1
  have hB : 0 < B := by dsimp [B]; linarith [hμ.nonneg e0, hμ.nonneg e1]
  have hu (v : Plane) : μ v ≤ B * ‖v‖ := by
    have he : v = v 0 • e0 + v 1 • e1 := by
      ext i; fin_cases i <;> simp [e0, e1]
    have ht := hμ.triangle (v 0 • e0) (v 1 • e1)
    rw [← he, hμ.homogeneous, hμ.homogeneous] at ht
    have h0 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 0) (hμ.nonneg e0)
    have h1 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 1) (hμ.nonneg e1)
    dsimp [B]
    nlinarith [norm_nonneg v]
  refine ⟨B, hB, ?_⟩
  intro v w
  apply abs_le.mpr
  have h1 := hμ.triangle (v-w) w
  have h2 := hμ.triangle (w-v) v
  simp only [sub_add_cancel] at h1 h2
  have hu1 := hu (v-w)
  have hu2 := hu (w-v)
  rw [norm_sub_rev] at hu2
  constructor <;> linarith

theorem timeConstantNorm_continuous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    Continuous μ := by
  obtain ⟨B, hB, hb⟩ := timeConstantNorm_lipschitz_bound μ hμ
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε/B, div_pos hε hB, ?_⟩
  intro w hw
  have hd : ‖w-v‖ < ε/B := hw
  have he := (lt_div_iff₀ hB).mp hd
  have hl := hb w v
  change |μ w-μ v| < ε
  nlinarith

theorem norm_direction_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    0 < μ (direction b) := by
  have hn : direction b ≠ 0 := by
    intro hh
    have := congrArg xCoord hh
    norm_num [direction] at this
  exact lt_of_le_of_ne (hμ.nonneg _) (Ne.symm ((hμ.zero_iff _).not.mpr hn))

lemma norm_differentiable_smul (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (u : Plane) (t : ℝ) (ht : t ≠ 0) (hu : DifferentiableAt ℝ μ u) :
    DifferentiableAt ℝ μ (t • u) := by
  have hi : DifferentiableAt ℝ μ (t⁻¹ • (t • u)) := by simpa [smul_smul,ht] using hu
  have hc := hi.comp (t • u) (differentiableAt_id.const_smul t⁻¹)
  have hd := hc.const_mul |t|
  have he : (fun z : Plane => |t| *μ (t⁻¹ • z))=μ := by
    funext z
    rw [hμ.homogeneous,abs_inv,← mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr ht),one_mul]
  simpa only [Function.comp_def,he] using hd

lemma convex_continuous_deriv (φ : ℝ → ℝ) (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) : Continuous (deriv φ) := by
  let g := fun x => deriv φ x+x
  have hm : Monotone g := fun x y h => add_le_add
    (hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ x) (mem_univ y) h) h
  have hg (x : ℝ) : HasDerivAt (fun t => φ t+t^2/2) (g x) x := by
    have hq : HasDerivAt (fun t : ℝ => t^2/2) x x := by
      simpa using ((hasDerivAt_id x).pow 2).div_const 2
    exact (hd x).hasDerivAt.add hq
  have hsurj : Function.Surjective g := by
    intro y
    let a := min 0 (y-deriv φ 0-1)
    let b := max 0 (y-deriv φ 0+1)
    have ha : a ≤ 0 := min_le_left ..
    have hb : 0 ≤ b := le_max_left ..
    have hda := hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ a) (mem_univ 0) ha
    have hdb := hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ 0) (mem_univ b) hb
    have hay : a ≤ y-deriv φ 0-1 := min_le_right ..
    have hby : y-deriv φ 0+1 ≤ b := le_max_right ..
    have hga : g a < y := by dsimp [g]; linarith
    have hgb : y < g b := by dsimp [g]; linarith
    obtain ⟨x,_hx,hx⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt (ha.trans hb)
      (fun x _ => (hg x).hasDerivWithinAt) hga hgb
    exact ⟨x,hx⟩
  have hcont := hm.continuous_of_surjective hsurj
  convert hcont.sub continuous_id using 1
  funext x
  dsimp [g]
  ring

lemma convex_contDiff_one (φ : ℝ → ℝ) (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) : ContDiff ℝ 1 φ :=
  contDiff_one_iff_deriv.mpr ⟨hd,convex_continuous_deriv φ hc hd⟩

lemma plane_direction_representation (v : Plane) (hx : v 0 ≠ 0) :
    v 0 • direction (v 1/v 0)=v := by
  ext i
  fin_cases i <;> simp [direction,PiLp.smul_apply]
  field_simp

lemma contDiff_direction : ContDiff ℝ 1 direction := by
  have hh : ContDiff ℝ 1 (fun t : ℝ => direction 0+t • transverseUnit) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have he : (fun t : ℝ => direction 0+t • transverseUnit)=direction := by
    funext t; ext i; fin_cases i <;> simp [direction,transverseUnit,PiLp.add_apply,PiLp.smul_apply]
  rwa [he] at hh

noncomputable def sphereChart (μ : Plane → ℝ) (c t : ℝ) : Plane :=
  (c/μ (direction t)) • direction t
noncomputable def directionRatio (v : Plane) : ℝ := v 1/v 0

lemma sphereChart_coordinates (μ : Plane → ℝ) (c t : ℝ) :
    sphereChart μ c t 0=c/μ (direction t) ∧ sphereChart μ c t 1=(c/μ (direction t))*t := by
  simp [sphereChart,direction,PiLp.smul_apply]

lemma sphereChart_ratio (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    directionRatio (sphereChart μ c t)=t := by
  obtain ⟨h0,h1⟩ := sphereChart_coordinates μ c t
  unfold directionRatio
  rw [h0,h1]
  have hp := norm_direction_pos μ hμ t
  field_simp

lemma sphereChart_mem (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (c : ℝ) (hc : |c|=1) (t : ℝ) :
    μ (sphereChart μ c t)=1 ∧ 0 < c*sphereChart μ c t 0 := by
  have hp := norm_direction_pos μ hμ t
  have hc0 : c ≠ 0 := by intro he; simp [he] at hc
  constructor
  · rw [sphereChart,hμ.homogeneous,abs_div,hc,abs_of_pos hp]
    field_simp
  · rw [(sphereChart_coordinates μ c t).1]
    have hcs : 0 < c*c := mul_self_pos.mpr hc0
    exact (div_pos hcs hp).trans_eq (by ring)

lemma sphereChart_reconstruct (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (c : ℝ) (hc : |c|=1) (v : Plane) (hv : μ v=1) (hsign : 0 < c*v 0) :
    sphereChart μ c (directionRatio v)=v := by
  have hx : v 0 ≠ 0 := by intro he; rw [he,mul_zero] at hsign; exact lt_irrefl _ hsign
  have hrep := plane_direction_representation v hx
  change v 0 • direction (directionRatio v)=v at hrep
  have hnorm : |v 0| *μ (direction (directionRatio v))=1 := by
    rw [← hμ.homogeneous,hrep,hv]
  have hcx : c*|v 0|=v 0 := by
    rcases eq_or_eq_neg_of_abs_eq hc with hc | hc
    · rw [hc] at hsign ⊢
      simp only [one_mul] at hsign ⊢
      exact abs_of_pos hsign
    · rw [hc] at hsign ⊢
      have hvneg : v 0 < 0 := by linarith
      rw [abs_of_neg hvneg]
      ring
  have he : c/μ (direction (directionRatio v))=v 0 := by
    apply (div_eq_iff (ne_of_gt (norm_direction_pos μ hμ _))).mpr
    rw [← hcx,mul_assoc,hnorm,mul_one]
  rw [sphereChart,he]
  exact hrep

lemma sphereChart_contDiff (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) :
    ContDiff ℝ 1 (sphereChart μ c) :=
  (contDiff_const.div hφ (fun t => ne_of_gt (norm_direction_pos μ hμ t))).smul contDiff_direction

lemma sphereChart_regular (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    ∃ d : Plane, HasDerivAt (sphereChart μ c) d t ∧ d ≠ 0 := by
  have hg := ((sphereChart_contDiff μ hμ hφ c).differentiable (by norm_num) t).hasDerivAt
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hx : sphereChart μ c t 0 ≠ 0 := by
    rw [(sphereChart_coordinates μ c t).1]
    exact div_ne_zero hc (ne_of_gt (norm_direction_pos μ hμ t))
  have hyc : ContDiffAt ℝ 1 (fun z : Plane => z 1) (sphereChart μ c t) := y.contDiff.contDiffAt
  have hxc : ContDiffAt ℝ 1 (fun z : Plane => z 0) (sphereChart μ c t) := xCoord.contDiff.contDiffAt
  have hr : DifferentiableAt ℝ directionRatio (sphereChart μ c t) :=
    (hyc.div hxc hx).differentiableAt (by norm_num)
  have hchain := hr.hasFDerivAt.comp_hasDerivAt t hg
  have he : (directionRatio ∘ sphereChart μ c)=id := funext (sphereChart_ratio μ hμ c hc)
  rw [he] at hchain
  have hid := hchain.unique (hasDerivAt_id t)
  refine ⟨_,hg,?_⟩
  intro hz
  rw [hz,map_zero] at hid
  norm_num at hid

lemma sphere_horizontal_chart (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) (hc : |c|=1)
    (v : Plane) (hv : μ v=1) (hsign : 0 < c*v 0) : HasC1CurveChart {z | μ z=1} v := by
  let U : Set Plane := {z | 0 < c*z 0}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.mul xCoord.continuous)
  have hc0 : c ≠ 0 := by intro he; simp [he] at hc
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hθ : ContinuousOn directionRatio U := y.continuous.continuousOn.div xCoord.continuous.continuousOn
    (fun z hz => by intro he; change 0<c*z 0 at hz; rw [he,mul_zero] at hz; exact lt_irrefl _ hz)
  exact ⟨U,hU,hsign,hv,sphereChart μ c,directionRatio,sphereChart_contDiff μ hμ hφ c,hθ,
    sphereChart_mem μ hμ c hc,sphereChart_ratio μ hμ c hc0,
    fun z hz => sphereChart_reconstruct μ hμ c hc z hz.1 hz.2,sphereChart_regular μ hμ hφ c hc0⟩

theorem norm_ball_frontier (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    frontier {v | μ v ≤ 1}={v | μ v=1} := by
  apply Subset.antisymm (frontier_le_subset_eq (timeConstantNorm_continuous μ hμ) continuous_const)
  intro v hv
  change μ v=1 at hv
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (show μ v ≤ 1 by exact hv.le),?_⟩
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝[>] (1 : ℝ)) (𝓝 v) := by
    have hh : ContinuousAt (fun t : ℝ => t • v) 1 := continuous_id.smul continuous_const |>.continuousAt
    simpa only [one_smul] using hh.mono_left (show 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 1<t at ht
  change ¬μ (t • v) ≤ 1
  rw [hμ.homogeneous,hv,abs_of_pos (show 0<t by linarith)]
  linarith

lemma chart_preimage_isometry (S : Set Plane) (v : Plane)
    (e : Plane ≃ₗᵢ[ℝ] Plane) (h : HasC1CurveChart S (e v)) :
    HasC1CurveChart (e ⁻¹' S) v := by
  obtain ⟨U,hU,hv,hvS,γ,θ,hγ,hθ,hmem,hleft,hright,hreg⟩ := h
  refine ⟨e ⁻¹' U,hU.preimage e.continuous,hv,hvS,e.symm ∘ γ,θ ∘ e,?_,?_,?_,?_,?_,?_⟩
  · exact e.symm.toContinuousLinearEquiv.contDiff.comp hγ
  · exact hθ.comp e.continuous.continuousOn (fun _ hz => hz)
  · intro t
    simpa only [Function.comp_apply,mem_inter_iff,mem_preimage,e.apply_symm_apply] using hmem t
  · intro t
    simpa only [Function.comp_apply,e.apply_symm_apply] using hleft t
  · intro z hz
    change e.symm (γ (θ (e z)))=z
    rw [hright (e z) hz,e.symm_apply_apply]
  · intro t
    obtain ⟨d,hd,hne⟩ := hreg t
    refine ⟨e.symm d,e.symm.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t hd,?_⟩
    intro hz
    exact hne (e.symm.injective (by simpa using hz))

end GammaFPP.Analytic

end OAI
