import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.RayAdvance

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma neg_cost_ray_lipschitz (z : TangentBundle 𝓘(ℝ,Model n) M) (y : M) :
    ∃ K, LipschitzWith K (fun t => -cost (sprayFlow t z).1 y) := by
  let C : ℝ≥0 := ⟨Metric.diam (univ:Set M),Metric.diam_nonneg⟩
  have hC : ∀ x y : M,dist x y≤C := fun x y =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  have H : LipschitzWith C (fun x : M => cost x y) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x x'
    simpa only [Real.dist_eq] using cost_lipschitz_of_distance_bound hC x x' y
  exact ⟨C*‖z.2‖₊,(H.comp (lipschitz_spray_projection z)).neg⟩

def rayMountainDifference (z : TangentBundle 𝓘(ℝ,Model n) M) (y : M)
    (a vy b B0 By : ℝ) (t : ℝ) : ℝ :=
  -cost (sprayFlow t z).1 y+(1-t)^2*‖z.2‖^2/2+(a-vy-b*(By-B0))

omit [Nonempty M] in
lemma rayMountainDifference_lipschitzOn (z : TangentBundle 𝓘(ℝ,Model n) M) (y : M)
    (a vy b B0 By T : ℝ) :
    ∃ K, LipschitzOnWith K (rayMountainDifference z y a vy b B0 By) (Icc 0 T) := by
  obtain ⟨K,hK⟩ := neg_cost_ray_lipschitz z y
  have hc : ContDiff ℝ 1 (fun t : ℝ => (1-t)^2*‖z.2‖^2/2) := by fun_prop
  obtain ⟨L,hL⟩ := hc.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 T) isCompact_Icc
  refine ⟨K+L,?_⟩
  have H := (hK.lipschitzOnWith.add hL).add (LipschitzWith.const (a-vy-b*(By-B0))).lipschitzOnWith
  simp only [add_zero] at H
  exact H

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma rayMountainDifference_hasDerivAt {z : TangentBundle 𝓘(ℝ,Model n) M} {y : M}
    (a vy b B0 By : ℝ) {t d : ℝ}
    (hd : HasDerivAt (fun s => -cost (sprayFlow s z).1 y) d t) :
    HasDerivAt (rayMountainDifference z y a vy b B0 By) (d-(1-t)*‖z.2‖^2) t := by
  have hc0 := ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2).mul_const (‖z.2‖^2)).div_const 2
  have hc : HasDerivAt (fun s : ℝ => (1-s)^2*‖z.2‖^2/2) (-(1-t)*‖z.2‖^2) t := by
    convert hc0 using 1 <;> norm_num
    ring
  have H := (hd.add hc).add_const (a-vy-b*(By-B0))
  have he' : d+(-(1-t)*‖z.2‖^2)=d-(1-t)*‖z.2‖^2 := by ring
  rw [he'] at H
  exact H

omit [Nonempty M] in
lemma middle_mountain_barrier {z : TangentBundle 𝓘(ℝ,Model n) M} {y : M}
    {a vy b B0 By D T : ℝ} (hb : 0≤b) (hD : 0<D) (hT : 0≤T) (hT1 : T≤1/2)
    (hs : D/16≤vy-a) (hB : B0+1≤By)
    (hstart : rayMountainDifference z y a vy b B0 By 0≤-b/2) :
    ∀ t∈Icc 0 T, rayMountainDifference z y a vy b B0 By t≤-b/2 := by
  obtain ⟨K,hK⟩ := rayMountainDifference_lipschitzOn z y a vy b B0 By T
  apply lipschitzOn_barrier hT hK hstart
  obtain ⟨C,hC⟩ := neg_cost_ray_lipschitz z y
  have hae : ∀ᵐ t : ℝ, DifferentiableAt ℝ (fun s => -cost (sprayFlow s z).1 y) t :=
    hC.ae_differentiableAt
  filter_upwards [hae] with t ht htI hval
  have hd := ht.hasDerivAt
  have H := spray_neg_cost_deriv_le hd
  have hmul : b≤b*(By-B0) := by nlinarith only [mul_nonneg hb (sub_nonneg.mpr hB)]
  have hgap : dist (sprayFlow t z).1 y^2≤(1-t)^2*‖z.2‖^2-D/8 := by
    dsimp only [rayMountainDifference,cost] at hval
    linarith only [hval,hs,hmul,hb]
  have Hn := norm_deficit_advance dist_nonneg (norm_nonneg z.2) htI.1 (htI.2.trans hT1)
    (show 0≤D/8 by positivity) hgap
  rw [(rayMountainDifference_hasDerivAt a vy b B0 By hd).deriv]
  linarith only [H,Hn,hD]

end

open Set MeasureTheory
open scoped Topology Interval ContDiff

def templateEps : ℝ := (2:ℝ)^(-10:ℤ)

def centerGamma : ℝ := 8*Real.log 2047

def centerTemplate (s : ℝ) : ℝ :=
  1-2/(1+Real.exp (-centerGamma*(s-5/8)))

lemma templateEps_eq : templateEps=1/1024 := by norm_num [templateEps]
lemma centerGamma_pos : 0 < centerGamma := by
  unfold centerGamma
  positivity

lemma centerTemplate_smooth : ContDiff ℝ ∞ centerTemplate := by
  unfold centerTemplate
  have hden : ∀ s:ℝ,1+Real.exp (-centerGamma*(s-5/8))≠0 :=
    fun s => ne_of_gt (by positivity)
  exact contDiff_const.sub (contDiff_const.div (contDiff_const.add
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))) hden)

lemma centerTemplate_bounds (s : ℝ) : -1 < centerTemplate s ∧ centerTemplate s < 1 := by
  have hp := Real.exp_pos (-centerGamma*(s-5/8))
  have hden : 0 < 1+Real.exp (-centerGamma*(s-5/8)) := by positivity
  unfold centerTemplate
  constructor
  · have H : 2/(1+Real.exp (-centerGamma*(s-5/8))) < 2 :=
      (div_lt_iff₀ hden).mpr (by linarith)
    linarith
  · have H : 0 < 2/(1+Real.exp (-centerGamma*(s-5/8))) := by positivity
    linarith

lemma centerTemplate_left {s:ℝ} (hs : s ≤ 1/2) :
    1-templateEps ≤ centerTemplate s := by
  have Hs : centerGamma/8 ≤ -centerGamma*(s-5/8) := by
    nlinarith [centerGamma_pos]
  have he : Real.exp (centerGamma/8)=2047 := by
    rw [centerGamma]
    convert Real.exp_log (by norm_num : (0:ℝ)<2047) using 1
    congr 1
    ring
  have H := Real.exp_le_exp.mpr Hs
  rw [he] at H
  have hden : 0 < 1+Real.exp (-centerGamma*(s-5/8)) := by positivity
  have HH : 2/(1+Real.exp (-centerGamma*(s-5/8))) ≤ (1:ℝ)/1024 :=
    (div_le_iff₀ hden).mpr (by linarith only [H])
  rw [templateEps_eq]
  unfold centerTemplate
  linarith only [HH]

lemma centerTemplate_right {s:ℝ} (hs : 3/4 ≤ s) : centerTemplate s < 0 := by
  have hs' : -centerGamma*(s-5/8) < 0 := by nlinarith [centerGamma_pos]
  have he : Real.exp (-centerGamma*(s-5/8)) < 1 := Real.exp_lt_one_iff.mpr hs'
  have hden : 0 < 1+Real.exp (-centerGamma*(s-5/8)) := by positivity
  have HH : 1 < 2/(1+Real.exp (-centerGamma*(s-5/8))) :=
    (lt_div_iff₀ hden).mpr (by linarith only [he])
  unfold centerTemplate
  linarith only [HH]

lemma hasDerivAt_centerTemplate (s:ℝ) :
    HasDerivAt centerTemplate
      (-2*centerGamma*Real.exp (-centerGamma*(s-5/8))/
        (1+Real.exp (-centerGamma*(s-5/8)))^2) s := by
  have he := (((hasDerivAt_id s).sub_const (5/8:ℝ)).const_mul (-centerGamma)).exp
  have H := (hasDerivAt_const s (1:ℝ)).sub ((hasDerivAt_const s (2:ℝ)).div
    ((hasDerivAt_const s (1:ℝ)).add he) (by
      change 1+Real.exp (-centerGamma*(s-5/8))≠0
      exact ne_of_gt (by positivity)))
  have H' : HasDerivAt centerTemplate
      (0-(0*(1+Real.exp (-centerGamma*(s-5/8)))-
        2*(0+Real.exp (-centerGamma*(s-5/8))*(-centerGamma*1)))/
        (1+Real.exp (-centerGamma*(s-5/8)))^2) s := H
  convert H' using 1
  ring

lemma centerTemplate_deriv_neg (s:ℝ) : deriv centerTemplate s < 0 := by
  rw [(hasDerivAt_centerTemplate s).deriv]
  have hden : 0 < (1+Real.exp (-centerGamma*(s-5/8)))^2 := by positivity
  apply div_neg_of_neg_of_pos _ hden
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) centerGamma_pos)
    (Real.exp_pos _)

def outerVelocity (M0 K eta s : ℝ) : ℝ :=
  let kappa := K+1
  let A := M0+3
  let L := 128*A*kappa
  let h0 := 1/(128*kappa)
  (L-kappa*s)*Real.smoothTransition ((s+3*eta)/eta)*
    (1-Real.smoothTransition ((s-h0)/h0))

def outerPrimitive (M0 K eta s : ℝ) : ℝ :=
  1+templateEps/2+∫ q in (0:ℝ)..s,outerVelocity M0 K eta q

def outerTemplate (M0 K eta s : ℝ) : ℝ :=
  outerPrimitive M0 K eta s*
    (1-Real.smoothTransition ((s-(1-eta))/eta))

lemma outerVelocity_smooth (M0 K eta : ℝ) : ContDiff ℝ ∞ (outerVelocity M0 K eta) := by
  unfold outerVelocity
  fun_prop

lemma outerVelocity_zero_left {M0 K eta s:ℝ} (heta : 0 < eta) (hs : s ≤ -3*eta) :
    outerVelocity M0 K eta s=0 := by
  have H : (s+3*eta)/eta ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) heta.le
  simp only [outerVelocity,Real.smoothTransition.zero_of_nonpos H,mul_zero,zero_mul]

lemma outerVelocity_zero_right {M0 K eta s:ℝ} (hK : 1 ≤ K)
    (hs : 2*(1/(128*(K+1))) ≤ s) : outerVelocity M0 K eta s=0 := by
  have hh : 0 < 1/(128*(K+1)) := by positivity
  have H : 1 ≤ (s-1/(128*(K+1)))/(1/(128*(K+1))) :=
    (le_div_iff₀ hh).mpr (by linarith only [hs])
  simp only [outerVelocity,Real.smoothTransition.one_of_one_le H,sub_self,mul_zero]

lemma outerVelocity_core {M0 K eta s:ℝ} (heta : 0 < eta)
    (hs : -2*eta ≤ s) (hs' : s ≤ 1/(128*(K+1))) (hK : 1 ≤ K) :
    outerVelocity M0 K eta s=128*(M0+3)*(K+1)-(K+1)*s := by
  have hh : 0 < 1/(128*(K+1)) := by positivity
  have Hl : 1 ≤ (s+3*eta)/eta := (le_div_iff₀ heta).mpr (by linarith only [hs])
  have Hr : (s-1/(128*(K+1)))/(1/(128*(K+1))) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith only [hs']) hh.le
  simp only [outerVelocity,Real.smoothTransition.one_of_one_le Hl,
    Real.smoothTransition.zero_of_nonpos Hr,sub_zero,mul_one]

end WeakMTWTransport

end

end OAI
