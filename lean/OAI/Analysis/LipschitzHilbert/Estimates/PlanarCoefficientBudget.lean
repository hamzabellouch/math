import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketFamily

namespace OAI

/-! The proved main-coefficient budget on every short-packet center box.
The same constant works for all reference lengths and all finite families. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert
namespace PlanarPacketFamily

theorem mainCoefficient_localBudget (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ),
      Monotone d → Measurable v → Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      (∀ j i k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      ∀ u y r : ℝ, 0 < r → ∀ b : ℤ × ℤ,
      (∑ j, P.length j * ∑ i : P.BoxFiber u y r b j, ‖P.mainCoefficient d v g j i‖^2) ≤
        A * P.constant^2 * r := by
  obtain ⟨A,hA,hbound⟩ := ReferencePacketFamily.mainCoefficient_carleson hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι instκ instι P d v g hd hv hg hg1 hlow hhigh u y r hr b
  have h := hbound N κ (P.BoxFiber u y r b) (P.referenceBox u y r hr b)
    d v g hd hv hg hg1 (fun j i k => P.wave_measurable j i k)
    (fun j i k y ξ hξ => hlow j i k y ξ hξ)
    (fun j i k y ξ hξ => hhigh j i k y ξ hξ)
  change P.width *
    (∑ j, P.length j * ∑ i : P.BoxFiber u y r b j, ‖P.mainCoefficient d v g j i‖^2) ≤
      A * P.constant^2 * (r * P.width) at h
  apply (mul_le_mul_iff_right₀ P.width_pos).mp
  convert h using 1
  ring

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
