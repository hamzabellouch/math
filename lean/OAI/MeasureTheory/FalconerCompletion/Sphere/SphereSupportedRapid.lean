import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.FarPairError
import OAI.MeasureTheory.FalconerCompletion.Graphs.SpherePairFarSupported

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real
open scoped ContDiff ComplexConjugate Topology
attribute [local instance] Classical.propDecidable

theorem sphere_supported_rapidND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (B T : ℝ) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (U W : Set (SphereAmbientND n)) (b c : SphereAmbientND n → ℂ) (e z : SphereAmbientND n) (A Λ Μ : ℝ),
      ContDiff ℝ ∞ b → ContDiff ℝ ∞ c →
      (∀ w∈U, -w∈U) → (∀ w∈W, -w∈W) → tsupport b ⊆ U → tsupport c ⊆ W →
      ‖e‖=1 → ‖z‖=1 →
      1≤A → A≤R^2 → 0<Λ → 0<Μ → A^2/Λ≤R^(-θ) → A^2/Μ≤R^(-θ) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j c w‖≤C*A^j) →
      R^B*‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖ ≤
        R^B*(if e∈U ∧ z∈W then H*(Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2))/(1+|Λ-Μ|)^2 else 0)+R^(-T) := by
  let q : ℝ := max 0 (B+T)+1
  have hq : 0<q := by dsimp [q]; linarith [le_max_left (0:ℝ) (B+T)]
  have hqBT : B-q < -T := by dsimp [q]; linarith [le_max_right (0:ℝ) (B+T)]
  obtain ⟨J,hJ⟩ := stationary_arbitrary_powerND θ q hθ (n+3)
  obtain ⟨H,D,P,S,hH,hD,hP,hS,hkernel⟩ := sphere_pair_far_supportedND (n := n) hΨ hs C hC J
  refine ⟨J,H,hH,?_⟩
  filter_upwards [far_eventually_const_mul_rpowND (C := P*(2*S*D+D^2)) hqBT,
    eventually_ge_atTop (1:ℝ)] with R hsmall hR
  intro U W b c e z A Λ Μ hb hc hU hW hbU hcW he hz hA hAup hΛ hΜ hratioΛ hratioΜ hbd hcd
  have hRp : 0<R := by linarith
  have hscale : ∀ L : ℝ, 0<L → A^2/L≤R^(-θ) → A^2≤L := by
    intro L hL hrat
    apply (div_le_one hL).mp
    exact hrat.trans (Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith))
  have hsΛ := hscale Λ hΛ hratioΛ
  have hsΜ := hscale Μ hΜ hratioΜ
  have hsq : 1≤A^2 := by nlinarith
  have htail : ∀ L : ℝ, 0<L → A^2/L≤R^(-θ) →
      D*L^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) ≤ D*R^(-q) := by
    intro L hL hrat
    exact comparable_stationary_tailND n J (by linarith) (hsq.trans (hscale L hL hrat)) hD
      (hJ R A L hR hA hL hAup hrat)
  have herr := far_pair_errorND hD hS hP
    (show 0≤D*Μ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) by positivity)
    (Real.rpow_nonneg hRp.le (-q))
    (Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith))
    (htail Λ hΛ hratioΛ) (htail Μ hΜ hratioΜ)
  have herr' : R^B*(P*((D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3))*S+
          (S+D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3))*
            (D*Μ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3)))) ≤ R^(-T) := by
    apply (mul_le_mul_of_nonneg_left herr (Real.rpow_nonneg hRp.le B)).trans
    calc
      _ = (P*(2*S*D+D^2))*(R^B*R^(-q)) := by ring
      _ = (P*(2*S*D+D^2))*R^(B-q) := by rw [← Real.rpow_add hRp]; rfl
      _ ≤ _ := hsmall
  apply (mul_le_mul_of_nonneg_left (hkernel U W b c e z A Λ Μ hb hc hU hW hbU hcW he hz hA hΛ hΜ hsΛ hsΜ hbd hcd)
    (Real.rpow_nonneg hRp.le B)).trans
  rw [mul_add]
  exact add_le_add le_rfl herr'

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
