import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.JointCalculus
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def dAlong (v : E) (f : E → F) (q : E) : F := fderiv ℝ f q v

@[fun_prop] theorem contDiff_dAlong (v : E) {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dAlong v f) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

theorem compactSupport_dAlong (v : E) {f : E → F} (hf : HasCompactSupport f) :
    HasCompactSupport (dAlong v f) := hf.fderiv_apply ℝ v

theorem eventuallyEq_dAlong (v : E) {f g : E → F} {q : E} (h : f =ᶠ[𝓝 q] g) :
    dAlong v f =ᶠ[𝓝 q] dAlong v g := (h.fderiv (𝕜 := ℝ)).mono (fun _ h => congrArg (fun A => A v) h)

theorem timeD_eq {n : ℕ} {f : ScalarField n}
    (hf : ContDiff ℝ ∞ (uncurry f)) {t : ℝ} (ht : 0 ≤ t) (X : Coord n) :
    timeD f t X = dAlong (1, 0) (uncurry f) (t, X) := by
  have hline : HasDerivAt (fun s => f s X) (dAlong (1, 0) (uncurry f) (t, X)) t := by
    simpa only [comp_def, dAlong, uncurry_apply_pair, id_eq] using
      ((hf.differentiable (by simp) (t, X)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t X)))
  exact hline.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem spatialD_eq {n : ℕ} {f : ScalarField n}
    (hf : ContDiff ℝ ∞ (uncurry f)) (i : Fin n) (t : ℝ) (X : Coord n) :
    spatialD i f t X = dAlong (0, Pi.single i 1) (uncurry f) (t, X) := by
  have hline : HasDerivAt (fun s => f t (update X i s))
      (dAlong (0, Pi.single i 1) (uncurry f) (t, X)) (X i) := by
    have hd := (hf.differentiable (by simp) (t, update X i (X i))).hasFDerivAt
    have harg := (hasDerivAt_const (X i) t).prodMk (hasDerivAt_update X i (X i))
    simpa only [comp_def, update_eq_self, dAlong, uncurry_apply_pair] using
      hd.comp_hasDerivAt (X i) harg
  exact hline.deriv

def residual (ν : ℝ) (a : ℝ × Coord 2 → Coord 2) (q : ℝ × Coord 2) (i : Fin 2) : ℝ :=
  dAlong (1, 0) (fun p => a p i) q +
    a q 0 * dAlong (0, Pi.single 0 1) (fun p => a p i) q +
    a q 1 * dAlong (0, Pi.single 1 1) (fun p => a p i) q -
    ν * (dAlong (0, Pi.single 0 1) (dAlong (0, Pi.single 0 1) (fun p => a p i)) q +
      dAlong (0, Pi.single 1 1) (dAlong (0, Pi.single 1 1) (fun p => a p i)) q)

@[fun_prop] theorem contDiff_residual (ν : ℝ) {a : ℝ × Coord 2 → Coord 2}
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (residual ν a) := by
  apply contDiff_pi.mpr
  intro i
  have h (j : Fin 2) : ContDiff ℝ ∞ (fun p => a p j) := (contDiff_apply ℝ ℝ j).comp ha
  unfold residual
  exact (((contDiff_dAlong _ (h i)).add ((h 0).mul (contDiff_dAlong _ (h i)))).add
    ((h 1).mul (contDiff_dAlong _ (h i)))).sub
    (contDiff_const.mul ((contDiff_dAlong _ (contDiff_dAlong _ (h i))).add
      (contDiff_dAlong _ (contDiff_dAlong _ (h i)))))

theorem residual_eq_horizontalResidual (ν : ℝ) {a : VectorField 2}
    (ha : ContDiff ℝ ∞ (uncurry a)) {t : ℝ} (ht : 0 ≤ t) (X : Coord 2) :
    residual ν (uncurry a) (t, X) = horizontalResidual ν a t X := by
  ext i
  have h (j : Fin 2) : ContDiff ℝ ∞ (uncurry (fun t X => a t X j)) :=
    (contDiff_apply ℝ ℝ j).comp ha
  have heq (j : Fin 2) : uncurry (spatialD j (fun t X => a t X i)) =
      dAlong (0, Pi.single j 1) (fun p => a p.1 p.2 i) :=
    funext fun q => spatialD_eq (h i) j q.1 q.2
  have hs (j : Fin 2) : ContDiff ℝ ∞ (uncurry (spatialD j (fun t X => a t X i))) := by
    rw [heq]; exact contDiff_dAlong _ (h i)
  simp only [horizontalResidual, advection, laplacian, Fin.sum_univ_two,
    timeD_eq (h i) ht, spatialD_eq (h i), spatialD_eq (hs 0), spatialD_eq (hs 1), heq,
    residual]
  rw [show uncurry (fun s y => a s y i) = (fun p : ℝ × Coord 2 => a p.1 p.2 i) from rfl]
  rw [show uncurry a = (fun p : ℝ × Coord 2 => a p.1 p.2) from rfl]
  ring

theorem eventuallyEq_residual (ν : ℝ) {a b : ℝ × Coord 2 → Coord 2} {q : ℝ × Coord 2}
    (h : a =ᶠ[𝓝 q] b) : residual ν a =ᶠ[𝓝 q] residual ν b := by
  have hi (i : Fin 2) : (fun p => a p i) =ᶠ[𝓝 q] (fun p => b p i) :=
    h.mono (fun _ h => congrFun h i)
  have ht (i : Fin 2) := eventuallyEq_dAlong (1, 0) (hi i)
  have hx (i j : Fin 2) := eventuallyEq_dAlong (0, Pi.single j 1) (hi i)
  have hxx (i j : Fin 2) := eventuallyEq_dAlong (0, Pi.single j 1) (hx i j)
  have hh (i : Fin 2) : (fun p => residual ν a p i) =ᶠ[𝓝 q] (fun p => residual ν b p i) :=
    ((ht i).add ((hi 0).mul (hx i 0)) |>.add ((hi 1).mul (hx i 1))).sub
      (EventuallyEq.rfl.mul ((hxx i 0).add (hxx i 1)))
  filter_upwards [hh 0, hh 1] with p hp0 hp1
  ext i
  fin_cases i
  · exact hp0
  · exact hp1

theorem compactSupport_residual (ν : ℝ) {a : ℝ × Coord 2 → Coord 2}
    (ha : HasCompactSupport a) : HasCompactSupport (residual ν a) := by
  have h (i : Fin 2) : HasCompactSupport (fun p => a p i) :=
    ha.comp_left (g := fun v : Coord 2 => v i) rfl
  have hc (i : Fin 2) : HasCompactSupport (fun p => residual ν a p i) := by
    exact (((compactSupport_dAlong _ (h i)).add (h 0).mul_right).add (h 1).mul_right).sub
      (((compactSupport_dAlong _ (compactSupport_dAlong _ (h i))).add
        (compactSupport_dAlong _ (compactSupport_dAlong _ (h i)))).mul_left)
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_iUnion hc)
  intro q hq
  have hi : ∃ i, residual ν a q i ≠ 0 := by
    by_contra! hi
    exact hq (funext hi)
  obtain ⟨i, hi⟩ := hi
  exact mem_iUnion.mpr ⟨i, subset_closure hi⟩

end VelocityDetection.JointCalculus
end

end OAI
