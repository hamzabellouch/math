import Mathlib
import OAI.Geometry.Cannon.Uniformization.ProductFactorSmall

namespace OAI

/-! Quasi-Möbius maps and distortion of cross ratios. -/

section
section
namespace CannonRealization
open Filter Topology Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem RelativeShrink.quasiMobius [PreconnectedSpace X] [PreconnectedSpace Y]
    (f : X ≃ₜ Y) (hf : RelativeShrink f) {Q : ℕ} {P : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q P) (hP : 0 ≤ P)
    (hdiam : ∀ x y : X, dist x y ≤ 1) : CannonQM.QuasiMobius f := by
  obtain ⟨C,α,β,hC,hα,hab,hβ,hcontrol⟩ := hf.power_control f hpack hP hdiam
  exact CannonDistortion.power_control_quasiMobius f f.injective hC hα hβ hab hcontrol

theorem realization_quasiMobius_limit [CompactSpace X] [CompactSpace Y]
    [PreconnectedSpace X] [PreconnectedSpace Y]
    {Q : ℕ} {P : ℝ} (hpack : CannonPacking.PolynomialPacking (X:=X) Q P)
    (hP : 0 ≤ P) (hdiam : ∀ x y : X, dist x y ≤ 1)
    (F : ℕ → C(X,Y)) (hsurj : ∀ n, Function.Surjective (F n))
    (hshrink : EventualRelativeShrink F)
    {p q : X} {u v : Y} (huv : u≠v)
    (hp : ∀ n, F n p=u) (hq : ∀ n, F n q=v) :
    ∃ f : X ≃ₜ Y, CannonQM.QuasiMobius f ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 (⟨f,f.continuous⟩ : C(X,Y))) := by
  obtain ⟨f,hf,φ,hφ,ht⟩ := realization_homeomorph_limit F hsurj hshrink huv hp hq
  exact ⟨f,hf.quasiMobius f hpack hP hdiam,φ,hφ,ht⟩

end CannonRealization

end
end

end OAI
