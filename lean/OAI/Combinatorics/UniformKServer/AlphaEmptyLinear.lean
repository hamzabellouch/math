import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaEmpty
import OAI.Combinatorics.UniformKServer.AdaptiveAlphaLinear

namespace OAI

                                       
section

/-! The true affine potential extended to empty domains. -/
noncomputable section
namespace UniformKServer.AlphaEmptyLinear
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {ι : Type*} [Fintype ι]

def coefficient : Config ι → (ι → ℝ) → ι → ℝ
  | none, _, _ => 0
  | some p, a, i => AdaptiveAlphaLinear.coefficient p a i

theorem affine {p : Config ι} (hp : valid p) (B a : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) :
    potential p B a=∑ i, coefficient p a i*B i := by
  cases p with
  | none => simp [potential,coefficient]
  | some p => exact AdaptiveAlphaLinear.affine hp B a ha

theorem bound {p : Config ι} (hp : valid p) (a : ι → ℝ)
    (ha : state p a) (i : ι) : |coefficient p a i| ≤ 15*scale p := by
  cases p with
  | none => simp [coefficient,scale]
  | some p => exact AdaptiveAlphaLinear.bound hp a ha i

theorem difference {p : Config ι} (hp : valid p) (B B' a : ι → ℝ)
    (ha : state p a) :
    potential p B' a-potential p B a=∑ i, coefficient p a i*(B' i-B i) := by
  rw [affine hp B' a (state_interval ha),affine hp B a (state_interval ha),←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  ring

end UniformKServer.AlphaEmptyLinear

end


end

end OAI
