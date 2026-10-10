import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerEnergy
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral
import OAI.Geometry.PrescribedRicci.KahlerEnergyChain
import OAI.Geometry.PrescribedRicci.MongeAmpereEnergy

namespace OAI

/-! Weighted Monge Ampere Energy. -/

section

 
noncomputable section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma integral_weighted_energy_segment [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ)
    (hd : 0 < d) (W : X → ℝ) (hW : Continuous W) (hWpos : ∀ x, 0 ≤ W x)
    (s : ℝ) (hs : s ∈ Ico 0 1) :
    (1 - s) ^ (d - 1) * g.integral (fun x => W x * (g.energy φ φ).value x) ≤
      (g.deform (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)).integral
        (fun x => W x * ((g.deform (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)).energy φ φ).value x) := by
  let gs := g.deform (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)
  rw [← g.integral_const_mul, ← g.integral_density (φ.realSMul s) (hp.segment ⟨hs.1, hs.2.le⟩)]
  apply g.integral_mono (continuous_const.fun_mul (hW.fun_mul (g.energy φ φ).continuous))
    ((hW.fun_mul (gs.energy φ φ).continuous).fun_mul (g.potentialDensity _).continuous)
  intro x
  have he := mul_le_mul_of_nonneg_left (g.energy_segment_coercive φ hp hd s hs x) (hWpos x)
  change (1-s)^(d-1) * (W x * (g.energy φ φ).value x) ≤
    (W x * (gs.energy φ φ).value x) * (g.potentialDensity (φ.realSMul s)).value x
  nlinarith only [he]

lemma integral_weighted_energy_half_segment [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ)
    (hd : 0 < d) (W : X → ℝ) (hW : Continuous W) (hWpos : ∀ x, 0 ≤ W x)
    (s : ℝ) (hs : s ∈ Icc 0 (1/2)) :
    (1/2 : ℝ) ^ (d - 1) * g.integral (fun x => W x * (g.energy φ φ).value x) ≤
      (g.deform (φ.realSMul s) (hp.segment ⟨hs.1, by linarith [hs.2]⟩)).integral
        (fun x => W x * ((g.deform (φ.realSMul s) (hp.segment ⟨hs.1, by linarith [hs.2]⟩)).energy φ φ).value x) := by
  have hs' : s ∈ Ico 0 1 := ⟨hs.1, by linarith [hs.2]⟩
  refine le_trans ?_ (g.integral_weighted_energy_segment φ hp hd W hW hWpos s hs')
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by norm_num) (by linarith [hs.2]) (d - 1))
    (g.integral_nonneg (fun x => mul_nonneg (hWpos x) (g.energy_nonneg φ x)))

 

theorem mongeAmpere_weighted_energy [T2Space X] [CompactSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ) (hd : 0 < d)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hFpos : ∀ x, 0 ≤ deriv F x) :
    (1/2 : ℝ) ^ d * g.integral (fun x => deriv F (φ.value x) * (g.energy φ φ).value x) ≤
      g.integral (fun x => F (φ.value x)) -
        g.integral (fun x => F (φ.value x) * (g.potentialDensity φ).value x) := by
  let ψ := φ.compose F hF
  let W (x : X) := deriv F (φ.value x)
  have hW : Continuous W := (hF.continuous_deriv (by simp)).comp φ.continuous
  let f (t : ℝ) := g.integral (fun x => ψ.value x * (g.potentialDensity (φ.realSMul t)).value x)
  have hf (s : ℝ) (hs : s ∈ Icc 0 1) := g.volume_firstVariation φ ψ s (hp.segment hs)
  have hfc : ContinuousOn f (Icc 0 1) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hfd : DifferentiableOn ℝ f (interior (Icc 0 1)) :=
    fun s hs => (hf s (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hae (s : ℝ) (hs : s ∈ Icc 0 1) :
      ((g.deform (φ.realSMul s) (hp.segment hs)).energy ψ φ).value =
        fun x => W x * ((g.deform (φ.realSMul s) (hp.segment hs)).energy φ φ).value x := by
    funext x
    exact (g.deform (φ.realSMul s) (hp.segment hs)).energy_comp_left φ φ F hF x
  have ha : AntitoneOn f (Icc 0 1) := antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hfc hfd (by
    intro s hs
    rw [(hf s (interior_subset hs)).deriv, hae s (interior_subset hs)]
    exact neg_nonpos.mpr ((g.deform (φ.realSMul s) (hp.segment (interior_subset hs))).integral_nonneg
      (fun x => mul_nonneg (hFpos _) ((g.deform (φ.realSMul s) (hp.segment (interior_subset hs))).energy_nonneg φ x))))
  have hsub : Icc (0 : ℝ) (1/2) ⊆ Icc 0 1 := fun s hs => ⟨hs.1, by linarith [hs.2]⟩
  have hdh : DifferentiableOn ℝ f (interior (Icc 0 (1/2))) :=
    fun s hs => (hf s (hsub (interior_subset hs))).differentiableAt.differentiableWithinAt
  have hh := (convex_Icc (0 : ℝ) (1/2)).image_sub_le_mul_sub_of_deriv_le
    (hfc.mono hsub) hdh
    (C := -((1/2 : ℝ) ^ (d - 1) * g.integral (fun x => W x * (g.energy φ φ).value x)))
    (by
      intro s hs
      rw [(hf s (hsub (interior_subset hs))).deriv, hae s (hsub (interior_subset hs))]
      exact neg_le_neg (g.integral_weighted_energy_half_segment φ hp hd W hW (fun x => hFpos _) s (interior_subset hs)))
    0 (by norm_num) (1/2) (by norm_num) (by norm_num)
  have he := ha (show (1/2 : ℝ) ∈ Icc 0 1 by norm_num) (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num)
  have h0 : f 0 = g.integral ψ.value := by
    dsimp only [f]
    simp_rw [g.potentialDensity_smul_zero, mul_one]
  have h1 : f 1 = g.integral (fun x => ψ.value x * (g.potentialDensity φ).value x) := by
    dsimp only [f]
    simp_rw [g.potentialDensity_smul_one]
  have hpow : (1/2 : ℝ) ^ d = (1/2 : ℝ) ^ (d - 1) * (1/2) := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
  rw [h0] at hh
  rw [h1] at he
  rw [hpow]
  change ((1/2 : ℝ) ^ (d - 1) * (1/2)) * g.integral (fun x => W x * (g.energy φ φ).value x) ≤
    g.integral ψ.value - g.integral (fun x => ψ.value x * (g.potentialDensity φ).value x)
  nlinarith

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
