import OAI.Geometry.RCD.Heat.CompactLaplaceLimit
import OAI.Geometry.RCD.Heat.CenteredWeightedPartition
import OAI.Geometry.RCD.Sobolev.UniformRealAlgebra

namespace OAI

/-! # Compact weighted heat-integral asymptotics from centered logarithms -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]

theorem weighted_laplace_limit (K G : ℕ → C(Y,ℝ)) (ε : ℕ → ℝ) (y₀ : Y)
    (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hK : ∀ k y, 0 < K k y) (hG : ∀ k y, 0 < G k y)
    (q g : Y → ℝ) (hq : Continuous q) (hg : Continuous g)
    (hkernel : TendstoUniformly (fun k y => ε k*Real.log (K k y)) q atTop)
    (hweight : TendstoUniformly (fun k y => ε k*(Real.log (G k y)-Real.log (G k y₀))) g atTop) :
    ∃ y ∈ ν.support, (∀ z ∈ ν.support, q z+g z ≤ q y+g y) ∧
      Tendsto (fun k => ε k*Real.log (∫ z, K k z*G k z ∂ν)-ε k*Real.log (G k y₀))
        atTop (𝓝 (q y+g y)) := by
  let H := fun k y => ε k*Real.log (K k y)+ε k*(Real.log (G k y)-Real.log (G k y₀))
  have hH (k : ℕ) : Continuous (H k) :=
    (((K k).continuous.log (fun y => (hK k y).ne')).const_mul (ε k)).add
      ((((G k).continuous.log (fun y => (hG k y).ne')).sub continuous_const).const_mul (ε k))
  obtain ⟨y,hy,hmax,hl⟩ := compact_laplace_limit ν H (fun y => q y+g y) hH
    (hq.add hg) (uniform_real_add hkernel hweight) ε hε hε0
  refine ⟨y,hy,hmax,hl.congr' ?_⟩
  apply Eventually.of_forall
  intro k
  have hi : Integrable (fun y => K k y*G k y) ν :=
    ((K k).continuous.mul (G k).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : Function.support (fun y => K k y*G k y)=univ := by
    ext y
    simp [(hK k y).ne',(hG k y).ne']
  have hp : 0 < ∫ y, K k y*G k y ∂ν :=
    (integral_pos_iff_support_of_nonneg (fun y => (mul_pos (hK k y) (hG k y)).le) hi).mpr
      (by rw [hs,measure_univ]; exact zero_lt_one)
  exact (centered_weighted_log_partition ν (K k) (G k) y₀ (hε k) (hK k) (hG k) hp).symm

end RegularPointCoordinates

end

end OAI
