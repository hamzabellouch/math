import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.FarEventuallyConstMulRpow
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAxisIntegralConj

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

theorem sphere_noncomparable_rapidND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ β : ℝ} (hθ : 0<θ) (hβ : 0<β) (B T : ℝ) :
    ∃ J : ℕ, ∀ᶠ R : ℝ in atTop,
      ∀ (b c : SphereAmbientND n → ℂ) (e z : SphereAmbientND n) (A Λ Μ : ℝ),
      ContDiff ℝ ∞ b → Continuous c → ‖e‖=1 → ‖z‖=1 →
      1≤A → A≤R^2 → R^β≤Λ → A^2/Λ≤R^(-θ) → 0≤Μ → 2*Μ≤Λ →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ w, ‖w‖=1 → ‖c w‖≤C) →
      R^B*‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖≤R^(-T) := by
  obtain ⟨J,k,hdecay⟩ := far_source_arbitrary_powerND n hθ hβ B T
  obtain ⟨H,E,hH,hE,hkernel⟩ := sphere_noncomparable_kernelND (n := n) hΨ hs C hC J k
  refine ⟨J,?_⟩
  filter_upwards [hdecay H E hH hE,eventually_ge_atTop (1:ℝ)] with R hRdec hR
  intro b c e z A Λ Μ hb hc he hz hA hAup hΛlo hratio hΜ hsep hbd hcd
  have hRp : 0<R := by linarith
  have hΛ : 0<Λ := (Real.rpow_pos_of_pos hRp β).trans_le hΛlo
  have hscale : A^2≤Λ := by
    apply (div_le_one hΛ).mp
    exact hratio.trans (Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith))
  exact (mul_le_mul_of_nonneg_left (hkernel b c e z A Λ Μ hb hc he hz hA hΛ hΜ hsep hscale hbd hcd)
    (Real.rpow_nonneg hRp.le B)).trans (hRdec A Λ hA hAup hΛlo hratio)

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
