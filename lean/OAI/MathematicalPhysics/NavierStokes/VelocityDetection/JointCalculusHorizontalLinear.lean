import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivativesFderiv

namespace OAI

noncomputable section
namespace VelocityDetection.JointCalculus
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

def horizontalLinear : Coord 3 →L[ℝ] Coord 2 :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1]

@[simp] theorem horizontalLinear_apply (X : Coord 3) : horizontalLinear X = horizontal X := by
  ext i
  fin_cases i <;> simp [horizontalLinear, horizontal]

def projection : (ℝ × Coord 3) →L[ℝ] (ℝ × Coord 2) :=
  (ContinuousLinearMap.fst ℝ ℝ (Coord 3)).prod
    (horizontalLinear.comp (ContinuousLinearMap.snd ℝ ℝ (Coord 3)))

@[simp] theorem projection_apply (q : ℝ × Coord 3) :
    projection q = (q.1, horizontal q.2) := by simp [projection]

def lift (a : ℝ × Coord 2 → Coord 2) (g : ℝ × Coord 2 → ℝ) (q : ℝ × Coord 3) : Coord 3 :=
  ![a (projection q) 0, a (projection q) 1, g (projection q)]

@[fun_prop] theorem contDiff_lift {a : ℝ × Coord 2 → Coord 2} {g : ℝ × Coord 2 → ℝ}
    (ha : ContDiff ℝ ∞ a) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (lift a g) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q => a (projection q) 0)
    exact (contDiff_apply ℝ ℝ 0).comp (ha.comp projection.contDiff)
  · change ContDiff ℝ ∞ (fun q => a (projection q) 1)
    exact (contDiff_apply ℝ ℝ 1).comp (ha.comp projection.contDiff)
  · exact hg.comp projection.contDiff

theorem bounded_lift {a : ℝ × Coord 2 → Coord 2} {g : ℝ × Coord 2 → ℝ}
    (ha : ContDiff ℝ ∞ a) (hg : ContDiff ℝ ∞ g)
    (hab : ∀ i, UniformDerivatives.Bounded (fun _ : Unit => fun q => a q i))
    (hgb : UniformDerivatives.Bounded (fun _ : Unit => g)) :
    UniformDerivatives.Bounded (fun _ : Unit => lift a g) := by
  apply UniformDerivatives.Bounded.pi
  · intro _ i
    exact (contDiff_apply ℝ ℝ i).comp (contDiff_lift ha hg)
  · intro i
    have hab' (j : Fin 2) := (hab j).comp (fun _ => (contDiff_apply ℝ ℝ j).comp ha)
      (fun _ => projection.contDiff) (UniformDerivatives.Positive.linear projection)
    have hgb' := hgb.comp (fun _ => hg) (fun _ => projection.contDiff)
      (UniformDerivatives.Positive.linear projection)
    fin_cases i
    · exact hab' 0
    · exact hab' 1
    · exact hgb'

end VelocityDetection.JointCalculus
end

end OAI
