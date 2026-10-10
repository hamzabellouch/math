import OAI.Geometry.SurfaceImmersion.Correction.SmoothParameterIntegral

namespace OAI

/-! The three linear moment equations for a positive loop density. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LoopDensity

abbrev Plane := Fin 2 → ℝ
abbrev Moments := Fin 3 → ℝ

def augment (v : Plane) : Moments := ![1, v 0, v 1]

def background (p : ℝ → Plane) : Moments := ∫ t in 0..1, augment (p t)

def column (p : ℝ → Plane) (ψ : ℝ → ℝ) : Moments :=
  ∫ t in 0..1, ψ t • augment (p t)

def momentMap (p : ℝ → Plane) (ψ : Fin 3 → ℝ → ℝ) : Moments →L[ℝ] Moments :=
  ∑ i : Fin 3, (ContinuousLinearMap.proj i).smulRight (column p (ψ i))

lemma momentMap_apply (p : ℝ → Plane) (ψ : Fin 3 → ℝ → ℝ) (w : Moments) :
    momentMap p ψ w = ∑ i, w i • column p (ψ i) := by
  simp [momentMap, ContinuousLinearMap.smulRight_apply]

lemma augment_continuous : Continuous augment := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [augment] <;> fun_prop

def density (ε : ℝ) (ψ : Fin 3 → ℝ → ℝ) (w : Moments) (t : ℝ) : ℝ :=
  ε + ∑ i, w i * ψ i t

lemma density_pos {ε : ℝ} (hε : 0 < ε) {ψ : Fin 3 → ℝ → ℝ} {w : Moments}
    (hψ : ∀ i t, 0 ≤ ψ i t) (hw : ∀ i, 0 ≤ w i) (t : ℝ) : 0 < density ε ψ w t := by
  apply add_pos_of_pos_of_nonneg hε
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hψ i t))

lemma density_periodic (ε : ℝ) (ψ : Fin 3 → ℝ → ℝ) (w : Moments)
    (hp : ∀ i, Function.Periodic (ψ i) 1) : Function.Periodic (density ε ψ w) 1 := by
  intro t
  simp only [density]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hp i t]

lemma density_moments {p : ℝ → Plane} (hp : Continuous p)
    {ψ : Fin 3 → ℝ → ℝ} (hψ : ∀ i, Continuous (ψ i)) (ε : ℝ) (w : Moments) :
    (∫ t in 0..1, density ε ψ w t • augment (p t)) =
      ε • background p + momentMap p ψ w := by
  have hc : Continuous (fun t => augment (p t)) := augment_continuous.comp hp
  have he : Continuous (fun t => ε • augment (p t)) := hc.const_smul ε
  have hs : Continuous (fun t => (∑ i, w i * ψ i t) • augment (p t)) :=
    (continuous_finsetSum _ (fun i _ => continuous_const.mul (hψ i))).smul hc
  simp_rw [density, add_smul]
  rw [intervalIntegral.integral_add
    (f := fun t => ε • augment (p t))
    (g := fun t => (∑ i, w i * ψ i t) • augment (p t))
    (he.intervalIntegrable _ _)
    (hs.intervalIntegrable _ _), intervalIntegral.integral_smul]
  congr 1
  simp_rw [Finset.sum_smul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [momentMap_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_smul, intervalIntegral.integral_smul, column]
  · intro i _
    exact ((continuous_const.mul (hψ i)).smul hc).intervalIntegrable _ _

def weights (p : ℝ → Plane) (ψ : Fin 3 → ℝ → ℝ) (ε : ℝ) (c : Plane) : Moments :=
  (momentMap p ψ).inverse (augment c - ε • background p)

/-- Once the moment matrix is invertible, all three equations are solved exactly. -/
theorem solved_moments {p : ℝ → Plane} (hp : Continuous p)
    {ψ : Fin 3 → ℝ → ℝ} (hψ : ∀ i, Continuous (ψ i))
    (hM : (momentMap p ψ).IsInvertible) (ε : ℝ) (c : Plane) :
    (∫ t in 0..1, density ε ψ (weights p ψ ε c) t • augment (p t)) = augment c := by
  rw [density_moments hp hψ]
  unfold weights
  rw [hM.self_apply_inverse]
  abel

end ClosedSurfaceR4.LoopDensity

end

end OAI
