import Mathlib
import OAI.Geometry.SmoothYau.Geometry.RadialFiniteDualNorm

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples

theorem exists_fixed_radial_constants (K S c : ℝ) (hc : 0 < c) :
    ∃ δ g₀ : ℝ, 0 < δ ∧ 0 < g₀ ∧ g₀ ≤ 1 ∧
      9216*K*S*δ^2 ≤ 1 ∧ g₀ = Real.sqrt (1+δ^2*c^2/16)-1 := by
  have h1 : Tendsto (fun δ : ℝ => 9216*K*S*δ^2) (𝓝 0) (𝓝 0) := by
    convert (show Continuous (fun δ : ℝ => 9216*K*S*δ^2) by fun_prop).tendsto 0 using 1; norm_num
  have h2 : Tendsto (fun δ : ℝ => δ^2*c^2/16) (𝓝 0) (𝓝 0) := by
    convert (show Continuous (fun δ : ℝ => δ^2*c^2/16) by fun_prop).tendsto 0 using 1; norm_num
  have hs : ∀ᶠ δ : ℝ in 𝓝 0, 9216*K*S*δ^2 < 1 ∧ δ^2*c^2/16 < 3 :=
    (h1.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))).and
      (h2.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 3)))
  have hs' : ∀ᶠ δ : ℝ in 𝓝[>] 0, 9216*K*S*δ^2 < 1 ∧ δ^2*c^2/16 < 3 :=
    hs.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hj : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ 9216*K*S*δ^2 < 1 ∧ δ^2*c^2/16 < 3 :=
    Filter.Eventually.and hpos hs'
  obtain ⟨δ,hδ,ha,hb⟩ := Filter.Eventually.exists hj
  have hp : 0 < δ^2*c^2/16 := by positivity
  have hgt : 1 < Real.sqrt (1+δ^2*c^2/16) := by
    have hh := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (show (1:ℝ) < 1+δ^2*c^2/16 by linarith)
    simpa using hh
  have hle : Real.sqrt (1+δ^2*c^2/16) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith⟩
  exact ⟨δ,Real.sqrt (1+δ^2*c^2/16)-1,hδ,sub_pos.mpr hgt,by linarith,ha.le,rfl⟩
end YauCounterexamples

end

namespace YauCounterexamples
noncomputable section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

structure FixedRadialChoice where
  β : ℝ → ℝ
  smooth : ContDiff ℝ ∞ β
  zero_at_zero : β 0 = 0
  range_bound : ∀ t, β t ∈ Icc 0 1
  zero_above : ∀ t, (1:ℝ)/256 ≤ t → β t = 0
  Fmax : ℝ
  S : ℝ
  K : ℝ
  Fmax_pos : 0 < Fmax
  S_pos : 0 < S
  K_pos : 0 < K
  coefficients : ∀ z, 0 ≤ periodicRadialSpeed β (1/4) z ∧
    periodicRadialSpeed β (1/4) z ≤ Fmax ∧
    0 ≤ periodicAngularSecond β (1/4) z ∧
    (periodicRadialSpeed β (1/4) z)^2 ≤ S*periodicAngularSecond β (1/4) z ∧
    |periodicRadialSecond β (1/4) z| ≤ K
  q : ProfilePlane
  ρ : ℝ
  c : ℝ
  δ : ℝ
  g₀ : ℝ
  radius_pos : 0 < ρ
  radius_le : ρ ≤ 1/4
  speed_pos : 0 < c
  delta_pos : 0 < δ
  gain_pos : 0 < g₀
  gain_le : g₀ ≤ 1
  gain_eq : g₀ = Real.sqrt (1+δ^2*c^2/16)-1
  smallness : 9216*K*S*δ^2 ≤ 1
  window : ∀ z, profileTorusQuotient z ∈
    ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ →
    c ≤ periodicRadialSpeed β (1/4) z

theorem fixedRadialChoice_nonempty : Nonempty FixedRadialChoice := by
  obtain ⟨β,hβ,hβc,hβs,hβv,hmid⟩ := exists_radial_derivative
    (show (1:ℝ)/1024 < 1/256 by norm_num)
  have hz₀ : β 0 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    have hh := (hβs h).1
    norm_num at hh)
  have hz : ∀ t, (1:ℝ)/256 ≤ t → β t = 0 := by
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact (not_lt_of_ge ht) (hβs h).2
  obtain ⟨Fmax,S,K,hM,hS,hK,hcoef⟩ := periodicRadial_coefficients_bounded hβ hβc hβv
    (show (0:ℝ) < 1/4 by norm_num)
  obtain ⟨q,ρ,c,hρ,hρ1,hc,hw⟩ := exists_radial_phase_window hβ
    (show (0:ℝ) < 1/1024 by norm_num) (show (1:ℝ)/1024 < 1/256 by norm_num)
    (show (1:ℝ)/256 < (1/4)^2 by norm_num) (show (0:ℝ) < 1/4 by norm_num)
    (show 2*(1/4:ℝ) < 1 by norm_num) hmid
  obtain ⟨δ,g₀,hδ,hg,hg1,hs,he⟩ := exists_fixed_radial_constants K S c hc
  exact ⟨⟨β,hβ,hz₀,hβv,hz,Fmax,S,K,hM,hS,hK,hcoef,q,ρ,c,δ,g₀,hρ,hρ1,hc,hδ,hg,hg1,he,hs,hw⟩⟩

noncomputable def fixedRadialChoice : FixedRadialChoice := Classical.choice fixedRadialChoice_nonempty

def FixedRadialChoice.fraction (D : FixedRadialChoice) : ℝ := (2*D.ρ)^2

lemma FixedRadialChoice.fraction_pos (D : FixedRadialChoice) : 0 < D.fraction := by
  dsimp [FixedRadialChoice.fraction]
  exact sq_pos_of_pos (by linarith [D.radius_pos])

lemma FixedRadialChoice.fraction_le (D : FixedRadialChoice) : D.fraction ≤ 1 := by
  dsimp [FixedRadialChoice.fraction]
  nlinarith [D.radius_pos,D.radius_le]

end
end YauCounterexamples

end OAI
