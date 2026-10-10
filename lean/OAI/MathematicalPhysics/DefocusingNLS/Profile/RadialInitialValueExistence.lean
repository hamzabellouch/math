import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInitialValueMap
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! Existence and uniqueness for the truncated radial amplitude shooting equation. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def boundedRadialInitialPicard (R η a₀ M : ℝ)
    (hR : 0 ≤ R) (hη : 0 ≤ η) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (v : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (radialInitialPicard R η a₀ N v)
    (continuous_radialInitialPicard R η a₀ N hN v) (‖a₀‖+M*R^2/24)
    (radialInitialPicard_bound R η a₀ M hR hη hM N hBound v)

theorem radialInitialPicard_contracting (R a₀ L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖) :
    ContractingWith ⟨1/12, by norm_num⟩
      (boundedRadialInitialPicard R (1+L*R) a₀ M hR
        (by positivity) hM N hN hBound) := by
  have hη : 0 < 1+L*R := by positivity
  have hc : L*R/(12*(1+L*R)) ≤ (1/12 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 12*(1+L*R))).2
    linarith
  refine ⟨by change (1/12 : ℝ) < 1; norm_num,LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  rw [dist_eq_norm,dist_eq_norm]
  change ‖_‖ ≤ (1/12 : ℝ)*‖u-v‖
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro r
  exact (radialInitialPicard_lipschitz R (1+L*R) a₀ L hR hη hL N hN hLip u v r).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

theorem existsUnique_radialInitialPicard (R a₀ L M : ℝ) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (N : ℝ → ℝ → ℝ)
    (hN : Continuous (Function.uncurry N))
    (hBound : ∀ t ∈ Icc 0 R, ∀ x : ℝ, ‖N t x‖ ≤ M)
    (hLip : ∀ t ∈ Icc 0 R, ∀ x y : ℝ, ‖N t x-N t y‖ ≤ L*‖x-y‖) :
    ∃! v : ℝ →ᵇ ℝ, ∀ r, v r=radialInitialPicard R (1+L*R) a₀ N v r := by
  let P := boundedRadialInitialPicard R (1+L*R) a₀ M hR
    (by positivity) hM N hN hBound
  have hP : ContractingWith ⟨1/12, by norm_num⟩ P :=
    radialInitialPicard_contracting R a₀ L M hR hL hM N hN hBound hLip
  refine ⟨hP.fixedPoint P,?_,?_⟩
  · intro r
    exact congrArg (fun w : ℝ →ᵇ ℝ => w r) hP.fixedPoint_isFixedPt.symm
  · intro v hv
    apply hP.fixedPoint_unique
    apply BoundedContinuousFunction.ext
    intro r
    exact (hv r).symm

end DefocusingNLS

end OAI
