import OAI.Geometry.SurfaceImmersion.Whitney.SharedParameterArcJoin

namespace OAI

/-! Smooth arc tails retain the exact forward germ needed by the next
piece in the finite source-arc assembly. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

structure SmoothArcTail (f : ℝ → M) (a : ℝ) where
  arc : SmoothCompactArc planeModel M
  parameter : ℝ → ℝ
  smooth : ContDiff ℝ ∞ parameter
  forward : 0 < deriv parameter arc.finish
  value : parameter arc.finish = a
  germ : arc.curve =ᶠ[𝓝 arc.finish] f ∘ parameter

namespace SmoothArcTail
variable {f : ℝ → M} {a b : ℝ}

theorem append (P : SmoothArcTail f a) (Q : SmoothCompactArc planeModel M)
    (l r : ℝ → ℝ) (hl : ContDiff ℝ ∞ l) (hr : ContDiff ℝ ∞ r)
    (hld : 0 < deriv l Q.start) (hrd : 0 < deriv r Q.finish)
    (hlv : l Q.start = a) (hrv : r Q.finish = b)
    (hlg : Q.curve =ᶠ[𝓝 Q.start] f ∘ l)
    (hrg : Q.curve =ᶠ[𝓝 Q.finish] f ∘ r)
    (hcross : ∀ s ∈ Icc P.arc.start P.arc.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.arc.curve s ≠ Q.curve t) :
    ∃ R : SmoothArcTail f b,
      R.arc.curve '' Icc R.arc.start R.arc.finish =
        P.arc.curve '' Icc P.arc.start P.arc.finish ∪ Q.curve '' Icc Q.start Q.finish ∧
      R.arc.curve R.arc.start = P.arc.curve P.arc.start ∧
      R.arc.curve =ᶠ[𝓝 R.arc.start] P.arc.curve := by
  obtain ⟨A,e,hes,hei,hem,hAs,hAf,hAi,hAleft,hAright,hAL,hAR⟩ :=
    join_shared_parameter_arcs f P.arc Q P.parameter l P.smooth hl P.forward hld
      (P.value.trans hlv.symm) P.germ hlg hcross
  have hev : e A.finish = Q.finish := by rw [hAf,e.apply_symm_apply]
  have het : Tendsto e (𝓝 A.finish) (𝓝 Q.finish) := by
    rw [← hev]
    exact e.continuous.continuousAt
  have hrval : (r ∘ e) A.finish = b := by
    dsimp only [Function.comp_apply]
    rw [hev,hrv]
  have hrgerm : A.curve =ᶠ[𝓝 A.finish] f ∘ (r ∘ e) :=
    hAR.trans (hrg.comp_tendsto het)
  have hre : 0 < deriv (r ∘ e) A.finish := by
    have hd := ((hr.differentiable (by simp) (e A.finish)).hasDerivAt).comp A.finish
      ((hes.differentiable (by simp) A.finish).hasDerivAt)
    rw [hd.deriv,hev]
    apply mul_pos hrd
    exact smooth_homeomorph_inverse_deriv_pos e.symm hei hes
      (by intro x y hxy; apply hem.lt_iff_lt.mp; simpa only [e.apply_symm_apply] using hxy) _
  let R : SmoothArcTail f b := ⟨A,r ∘ e,hr.comp hes,hre,hrval,hrgerm⟩
  exact ⟨R,hAi,hAleft,hAL⟩

end SmoothArcTail
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
