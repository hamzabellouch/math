import Mathlib
import OAI.Geometry.PrescribedPotential.PathTraceBound
import OAI.Geometry.PrescribedPotential.TraceEllipticity
import OAI.Geometry.PrescribedPotential.VolumeDeterminantBounds

namespace OAI

/-! Path Ellipticity. -/

section

 

noncomputable section
open Set Matrix
open scoped ComplexOrder MatrixOrder
namespace Anticanonical.SourceSmooth
open KaehlerCalculus
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

 

theorem volumePath_relative_ellipticity (g : KaehlerMetric A)
    (h : SemipositiveAnticanonicalMetric A) :
    ∃ R K : ℝ, 0 < R ∧ 0 < K ∧ ∀ (t b : ℝ) (φ : SmoothRealFunction A),
      t ∈ Icc 0 1 → ∀ _hs : SolvesVolumePath g h t φ b,
      ∀ i : Fin A.count, ∀ z ∈ (A.chart i).target,
        (((R:ℂ) • (g.matrix i z+φ.hessian i z))-g.matrix i z).PosSemidef ∧
        (((K:ℂ) • g.matrix i z)-(g.matrix i z+φ.hessian i z)).PosSemidef := by
  obtain ⟨R,hR,hRb⟩ := volumePath_inverseTrace_bound g h
  let R' := R+1
  let F : C(X,ℝ) := ⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩
  let K := Real.exp (2*‖F‖)*R'^(d-1)
  have hRp : 0 < R' := by dsimp [R']; linarith
  have hKp : 0 < K := mul_pos (Real.exp_pos _) (pow_pos hRp _)
  refine ⟨R',K,hRp,hKp,?_⟩
  intro t b φ ht hs i z hz
  let M := g.deform φ hs.choose
  have hp : (g.matrix i z+φ.hessian i z).PosDef := hs.choose i z hz
  have htr : ((g.matrix i z+φ.hessian i z)⁻¹*g.matrix i z).trace.re ≤ R' := by
    have hh := hRb t b φ ht hs ((A.chart i).symm z)
    change (M.inverseTrace g).localExpression i z ≤ R at hh
    rw [M.inverseTrace_local g i hz] at hh
    exact hh.trans (by dsimp [R']; linarith)
  refine ⟨inverse_trace_lower_psd hp (g.positive i z hz) htr,?_⟩
  exact inverse_trace_relative_upper hp (g.positive i z hz) hRp.le htr
    (volumePath_det_ratio_bounds g h ht hs.choose hs.choose_spec i hz).2
end Anticanonical.SourceSmooth

end
end

end OAI
