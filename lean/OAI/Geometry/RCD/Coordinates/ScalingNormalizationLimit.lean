import OAI.Geometry.RCD.Heat.CompactLaplaceLimit
import OAI.Geometry.RCD.Heat.ScalingLogPartition
import OAI.Geometry.RCD.Sobolev.UniformRealAlgebra

namespace OAI

/-! # The scalar normalization of a positive compact kernel scaling pair

The exact row identity and the proved compact Laplace limit determine the
otherwise free sum of the two logarithmic gauges.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]

theorem scaling_normalization_limit (K G : ℕ → C(Y, ℝ)) (A ε : ℕ → ℝ) (y₀ : Y)
    (hA : ∀ k, 0 < A k) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hK : ∀ k y, 0 < K k y) (hG : ∀ k y, 0 < G k y)
    (hrow : ∀ k, A k*(∫ y, K k y*G k y ∂ν)=1)
    (q g : Y → ℝ) (hq : Continuous q) (hg : Continuous g)
    (hkernel : TendstoUniformly (fun k y => ε k*Real.log (K k y)) q atTop)
    (hweight : TendstoUniformly (fun k y => ε k*(Real.log (G k y)-Real.log (G k y₀))) g atTop) :
    ∃ y ∈ ν.support, (∀ z ∈ ν.support, q z+g z ≤ q y+g y) ∧
      Tendsto (fun k => ε k*(Real.log (A k)+Real.log (G k y₀))) atTop (𝓝 (-(q y+g y))) := by
  let F := fun k y => ε k*Real.log (K k y)+ε k*(Real.log (G k y)-Real.log (G k y₀))
  have hF (k : ℕ) : Continuous (F k) := by
    exact (((K k).continuous.log (fun y => (hK k y).ne')).const_mul (ε k)).add
      ((((G k).continuous.log (fun y => (hG k y).ne')).sub continuous_const).const_mul (ε k))
  have hlim : TendstoUniformly F (fun y => q y+g y) atTop := uniform_real_add hkernel hweight
  obtain ⟨y,hy,hmax,hl⟩ := compact_laplace_limit ν F (fun y => q y+g y) hF (hq.add hg) hlim ε hε hε0
  refine ⟨y,hy,hmax,?_⟩
  apply hl.neg.congr'
  exact Eventually.of_forall fun k => by
    have he := scaling_log_partition ν (K k) (G k) y₀ (hA k) (hε k) (hK k) (hG k) (hrow k)
    change -(ε k*Real.log (∫ y, Real.exp (F k y/ε k) ∂ν)) = _
    dsimp only [F]
    rw [he]
    ring

end RegularPointCoordinates

end

end OAI
