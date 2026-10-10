import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ProfileFrequencyEnergy

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

theorem compact_profile_slope_bound (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ H > 0, ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
      ∀ x ∈ K, ‖fderiv ℝ φ x‖ ≤ H*profileFrequencyScale g φ x := by
  obtain ⟨S,hS,hbound⟩ := metricFrameSet_inverse_bound g hK
  refine ⟨S,hS,?_⟩
  intro φ hφ x hx
  obtain ⟨F,hF⟩ := metricFrameSet_fiber_nonempty g hx
  let q : NormalWaveParameter := (x,F)
  have hq : q ∈ metricFrameSet g K := hF
  let a := gradient (normalWaveProfile g φ q) 0
  have ha : ‖a‖ ≤ profileFrequencyScale g φ x := by
    have he := profileFrequencyEnergy_frame g hφ hq
    have hs := profileFrequencyScale_sq g φ x
    have hp := profileFrequencyScale_ge_one g φ x
    change profileFrequencyEnergy g φ x = 1+‖a‖^2 at he
    nlinarith [norm_nonneg a]
  have heq : fderiv ℝ φ x = (InnerProductSpace.toDual ℝ PhaseSpace a).comp q.2.inverse := by
    ext v
    change fderiv ℝ φ q.1 v = inner ℝ a (q.2.inverse v)
    rw [normalWaveProfile_gradient_pairing g hφ,frame_inverse_apply g hq]
  rw [heq]
  calc
    _ ≤ ‖InnerProductSpace.toDual ℝ PhaseSpace a‖*‖q.2.inverse‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖a‖*‖q.2.inverse‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ profileFrequencyScale g φ x*S :=
      mul_le_mul ha (hbound q hq) (norm_nonneg _) (by linarith [profileFrequencyScale_ge_one g φ x])
    _ = _ := by ring

lemma normalized_real_growth_bounds {L ℓ ε H : ℝ} (hL : 0 < L) (hℓ : L ≤ ℓ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hH : 0 ≤ H)
    (a : NormalWaveSpace →L[ℝ] ℝ) (ha : ‖a‖ ≤ H*L) (i : Fin 3) :
    Real.exp (-H) ≤ Real.exp ((ε/ℓ)*a (EuclideanSpace.basisFun (Fin 3) ℝ i)) ∧
    Real.exp ((ε/ℓ)*a (EuclideanSpace.basisFun (Fin 3) ℝ i)) ≤ Real.exp H := by
  have hℓ0 : 0 < ℓ := hL.trans_le hℓ
  have hi : |a (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ H*L := by
    have hi' := a.le_opNorm (EuclideanSpace.basisFun (Fin 3) ℝ i)
    simpa using hi'.trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have hεℓ : 0 ≤ ε/ℓ := div_nonneg hε hℓ0.le
  have hh : |(ε/ℓ)*a (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ H := by
    rw [abs_mul,abs_of_nonneg hεℓ]
    calc
      _ ≤ ε/ℓ*(H*L) := mul_le_mul_of_nonneg_left hi hεℓ
      _ = H*ε*(L/ℓ) := by ring
      _ ≤ H*ε := mul_le_of_le_one_right (mul_nonneg hH hε) ((div_le_one hℓ0).mpr hℓ)
      _ ≤ H := mul_le_of_le_one_right hH hε1
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hh).1,Real.exp_le_exp.mpr (abs_le.mp hh).2⟩

lemma endpoint_norm_lower {u v : ℂ} {a ε : ℝ} (ha : 0 < a)
    (hε : ε ≤ 1/2) (θ : ℝ)
    (h : ‖u-(a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*v‖ ≤
      ε*‖(a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*v‖) :
    (a/2)*‖v‖ ≤ ‖u‖ := by
  have he : ‖(a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*v‖ = a*‖v‖ := by
    simp [Complex.norm_exp,abs_of_pos ha]
  have ht := norm_sub_norm_le ((a : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)*v) u
  rw [norm_sub_rev,he] at ht
  rw [he] at h
  have hp := mul_le_mul_of_nonneg_right hε (mul_nonneg ha.le (norm_nonneg v))
  nlinarith
end



open Set Filter
open scoped Topology ContDiff RealInnerProductSpace

lemma compact_profile_unit_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ K, ∀ x : E, ‖x-q‖ ≤ 1 →
      ‖fderiv ℝ φ x‖ ≤ C ∧ |φ x-φ q| ≤ C*‖x-q‖ := by
  let L := (fun p : E×E => p.1+p.2) '' (K ×ˢ Metric.closedBall 0 1)
  have hL : IsCompact L := (hK.prod (isCompact_closedBall 0 1)).image
    (continuous_fst.add continuous_snd)
  obtain ⟨C,hbound⟩ := hL.exists_bound_of_continuousOn
    (hφ.fderiv_right (m := ∞) (by simp)).continuous.continuousOn
  let H := max 1 C
  have hb (q) (hq : q ∈ K) (x) (hx : ‖x-q‖ ≤ 1) : ‖fderiv ℝ φ x‖ ≤ H := by
    apply (hbound x ?_).trans (le_max_right _ _)
    refine ⟨(q,x-q),⟨hq,?_⟩,add_sub_cancel q x⟩
    simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  refine ⟨H,le_max_left _ _,?_⟩
  intro q hq x hx
  refine ⟨hb q hq x hx,?_⟩
  have hh := (convex_closedBall q (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hφ.differentiable (by simp) y)
    (fun y hy => hb q hq y (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy))
    (Metric.mem_closedBall_self zero_le_one)
    (show x ∈ Metric.closedBall q 1 by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  exact hh

lemma packet_value_lower_of_endpoint (φ : NormalWaveSpace → ℝ)
    {q x : NormalWaveSpace} {n H M r : ℝ} (hn : 1 ≤ n) (hH : 0 ≤ H)
    (hr : 0 ≤ r) (hMr : M*r ≤ 1/2) (hstep : n*‖x-q‖ ≤ 1)
    (hd : ‖fderiv ℝ φ q‖ ≤ H) (hval : |φ x-φ q| ≤ H*‖x-q‖)
    (u : NormalWaveSpace → ℂ) (β : NormalWaveSpace →L[ℝ] ℝ)
    (huq : u q = Complex.exp ((n : ℂ)*(φ q : ℂ)))
    (hend : ‖u x-(Real.exp (n*fderiv ℝ φ q (x-q)) : ℂ)*
      Complex.exp (((n*β (x-q) : ℝ) : ℂ)*Complex.I)*u q‖ ≤
      (M*r)*‖(Real.exp (n*fderiv ℝ φ q (x-q)) : ℂ)*
      Complex.exp (((n*β (x-q) : ℝ) : ℂ)*Complex.I)*u q‖) :
    (Real.exp (-2*H)/2)*Real.exp (n*φ x) ≤ ‖u x‖ := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hd' : |n*fderiv ℝ φ q (x-q)| ≤ H := by
    rw [abs_mul,abs_of_nonneg hn0]
    calc
      _ ≤ n*(‖fderiv ℝ φ q‖*‖x-q‖) := mul_le_mul_of_nonneg_left ((fderiv ℝ φ q).le_opNorm _) hn0
      _ ≤ n*(H*‖x-q‖) := by gcongr
      _ = H*(n*‖x-q‖) := by ring
      _ ≤ H := mul_le_of_le_one_right hH hstep
  have hv' : |n*(φ x-φ q)| ≤ H := by
    rw [abs_mul,abs_of_nonneg hn0]
    calc
      _ ≤ n*(H*‖x-q‖) := mul_le_mul_of_nonneg_left hval hn0
      _ = H*(n*‖x-q‖) := by ring
      _ ≤ H := mul_le_of_le_one_right hH hstep
  rw [← abs_of_nonneg hr] at hMr hend
  have hl := endpoint_norm_lower (Real.exp_pos (n*fderiv ℝ φ q (x-q))) hMr
    (n*β (x-q)) hend
  have hnorm : ‖u q‖ = Real.exp (n*φ q) := by
    rw [huq,Complex.norm_exp]
    simp
  rw [hnorm] at hl
  refine le_trans ?_ hl
  have he : -2*H+n*φ x ≤ n*fderiv ℝ φ q (x-q)+n*φ q := by
    have h1 := (abs_le.mp hd').1
    have h2 := (abs_le.mp hv').2
    nlinarith
  have hh := Real.exp_le_exp.mpr he
  rw [Real.exp_add,Real.exp_add] at hh
  nlinarith

end YauCounterexamples
end

end OAI
