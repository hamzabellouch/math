import OAI.Geometry.RCD.Heat.ScaledKernelCoupling
import OAI.Geometry.RCD.Sobolev.UniformRealAlgebra

namespace OAI

/-! # Uniform limit of the full logarithmic scaling density -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem scaling_log_density_limit (K : ℕ → C(X × Y, ℝ))
    (F : ℕ → C(X, ℝ)) (G : ℕ → C(Y, ℝ)) (ε : ℕ → ℝ) (x₀ : X) (y₀ : Y)
    (hK : ∀ k z, 0 < K k z) (hF : ∀ k x, 0 < F k x) (hG : ∀ k y, 0 < G k y)
    (q : X × Y → ℝ) (f : X → ℝ) (g : Y → ℝ) (c : ℝ)
    (hkernel : TendstoUniformly (fun k z => ε k*Real.log (K k z)) q atTop)
    (hleft : TendstoUniformly (fun k x => ε k*(Real.log (F k x)-Real.log (F k x₀))) f atTop)
    (hright : TendstoUniformly (fun k y => ε k*(Real.log (G k y)-Real.log (G k y₀))) g atTop)
    (hc : Tendsto (fun k => ε k*(Real.log (F k x₀)+Real.log (G k y₀))) atTop (𝓝 c)) :
    TendstoUniformly (fun k z => ε k*Real.log (scaledContinuousKernel (K k) (F k) (G k) z))
      (fun z => f z.1+q z+g z.2+c) atTop := by
  have h := uniform_real_add (uniform_real_add (uniform_real_add
    (hleft.comp Prod.fst) hkernel) (hright.comp Prod.snd)) hc.tendstoUniformly_const
  convert h using 1
  · funext k z
    change ε k*Real.log (F k z.1*K k z*G k z.2) = _
    rw [Real.log_mul (mul_pos (hF k z.1) (hK k z)).ne' (hG k z.2).ne',
      Real.log_mul (hF k z.1).ne' (hK k z).ne']
    simp only [Function.comp_def]
    ring
  · rfl

end RegularPointCoordinates

end

end OAI
