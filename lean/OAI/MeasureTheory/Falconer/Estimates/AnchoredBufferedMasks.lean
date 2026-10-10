import OAI.MeasureTheory.Falconer.Estimates.AnchoredMasks

namespace OAI

/-!
# Buffered masks on the original spatial anchor cells

These masks are jointly measurable, bounded between zero and one, smooth
in every adapted angular chart, and constant in the spatial variable on
all descendants of a reached anchor. Their angular derivative constants
are independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def anchoredBufferedMask {d : ℕ} (Q : DyadicCube d) (g : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (S : Finset (Sphere d))
    (U : List (Fin d → Bool) → Set (Sphere d)) : Space d → Sphere d → ℝ :=
  anchoredMask Q g (fun p w => capCutoffAmbient δ hδ S (U p) w)

theorem anchoredBufferedMask_measurable {d : ℕ} (Q : DyadicCube d) (g : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (U : List (Fin d → Bool) → Set (Sphere d)) :
    Measurable (Function.uncurry (anchoredBufferedMask Q g δ hδ S U)) := by
  apply anchoredMask_measurable
  intro p
  exact (capCutoffAmbient_contDiff hδ S (U p)).continuous.measurable.comp continuous_subtype_val.measurable

theorem anchoredBufferedMask_bounds {d : ℕ} (Q : DyadicCube d) (g : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2)
    (U : List (Fin d → Bool) → Set (Sphere d)) (x : Space d) (w : Sphere d) :
    0 ≤ anchoredBufferedMask Q g δ hδ S U x w ∧
      anchoredBufferedMask Q g δ hδ S U x w ≤ 1 :=
  anchoredMask_bounds Q g _ (fun p _ => (capCutoffAmbient_properties hδ S hcover (U p)).1) x w

theorem anchoredBufferedMask_support {d g : ℕ} (Q : DyadicCube d)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2)
    (U : List (Fin d → Bool) → Set (Sphere d))
    (p : List (Fin d → Bool)) (hp : p.length = g) {x : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d)
    (hw : anchoredBufferedMask Q g δ hδ S U x w ≠ 0) : w ∈ U p := by
  apply (capCutoffAmbient_properties hδ S hcover (U p)).2.1 w
  simpa only [anchoredBufferedMask,anchoredMask_on_cell Q _ p hp hx] using hw

theorem anchoredBufferedMask_core {d g : ℕ} (Q : DyadicCube d)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2)
    (U : List (Fin d → Bool) → Set (Sphere d))
    (p : List (Fin d → Bool)) (hp : p.length = g) {x : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d)
    (hw : ∀ z : Sphere d, dist z w ≤ 2*δ → z ∈ U p) :
    anchoredBufferedMask Q g δ hδ S U x w = 1 := by
  rw [anchoredBufferedMask,anchoredMask_on_cell Q _ p hp hx]
  exact (capCutoffAmbient_properties hδ S hcover (U p)).2.2 w hw

theorem anchoredBufferedMask_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (Q : DyadicCube (n+2)) (g : ℕ)
      (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (U : List (Fin (n+2) → Bool) → Set (Sphere (n+2)))
      (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ (x : Space (n+2)) (u : ℝ), u ∈ Icc (-1 : ℝ) 1 →
      ‖iteratedDeriv m (rotatedChartAmplitude e
        (fun w => (anchoredBufferedMask Q g δ hδ S U x w : ℂ)) y) u‖ ≤ B*(δ⁻¹)^m := by
  obtain ⟨B,hB,hBb⟩ := capCutoffAmbient_chart_derivatives n m
  refine ⟨B,hB,?_⟩
  intro Q g δ hδ hδ1 S hsep hcover U e y hy x u hu
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth g hx
    have he : anchoredBufferedMask Q g δ hδ S U x =
        (fun w : Sphere (n+2) => capCutoffAmbient δ hδ S (U p) w) := by
      funext w
      exact anchoredMask_on_cell Q _ p ((mem_cubePaths (n+2) g p).mp hp) hxp w
    rw [he]
    let f : ℝ → ℝ := fun t => capCutoffAmbient δ hδ S (U p) (rotatedChartCurve e y t)
    have hf : ContDiff ℝ ∞ f :=
      (capCutoffAmbient_contDiff hδ S (U p)).comp (rotatedChartCurve_contDiff e y)
    have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hf.contDiffAt (x := u))
      (show (m : ℕ∞ω) ≤ ∞ by simp)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs] at hn
    change ‖iteratedDeriv m (Complex.ofRealLI ∘ f) u‖ ≤ _
    rw [hn]
    exact hBb δ hδ hδ1 S hsep hcover (U p) e y hy u hu
  · have he : anchoredBufferedMask Q g δ hδ S U x = fun _ => 0 := by
      funext w
      exact anchoredMask_off_parent Q g _ hx w
    rw [he]
    change ‖iteratedDeriv m (fun _ : ℝ => (0 : ℂ)) u‖ ≤ _
    simp only [iteratedDeriv_const,ite_self,norm_zero]
    exact mul_nonneg hB (pow_nonneg (inv_nonneg.mpr hδ.le) m)

end Falconer

end OAI
