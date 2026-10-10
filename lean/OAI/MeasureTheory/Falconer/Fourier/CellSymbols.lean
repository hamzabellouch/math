import OAI.MeasureTheory.Falconer.Angular.CapAmplitudeDerivatives
import OAI.MeasureTheory.Falconer.Estimates.DyadicDisplacements

namespace OAI

/-!
# Cell restrictions inside original endpoint symbols

An indicator in the spatial variable leaves the restricted transform
unchanged and requires no spatial derivative. It makes all nonstationary
geometry hypotheses conditional on genuinely active point labels.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

noncomputable def cellSymbol {d : ℕ} (Q : DyadicCube d)
    (b : Space d → Sphere d → ℂ) (x : Space d) (w : Sphere d) : ℂ :=
  if x ∈ Q.carrier then b x w else 0

theorem cellSymbol_measurable {d : ℕ} (Q : DyadicCube d)
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b)) :
    Measurable (Function.uncurry (cellSymbol Q b)) := by
  exact hb.ite (Q.measurable.preimage measurable_fst) measurable_const

theorem cellSymbol_active {d : ℕ} (Q : DyadicCube d)
    (b : Space d → Sphere d → ℂ) {x : Space d} {w : Sphere d}
    (h : cellSymbol Q b x w ≠ 0) : x ∈ Q.carrier := by
  by_contra hn
  exact h (by simp [cellSymbol,hn])

theorem cellSymbol_bound {d : ℕ} (Q : DyadicCube d)
    (b : Space d → Sphere d → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x w, ‖b x w‖ ≤ B) (x : Space d) (w : Sphere d) :
    ‖cellSymbol Q b x w‖ ≤ B := by
  by_cases hx : x ∈ Q.carrier
  · simpa [cellSymbol,hx] using hb x w
  · simpa [cellSymbol,hx] using hB

theorem endpointTransform_cellSymbol {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (M : ℝ) (b : Space d → Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict Q.carrier) M (cellSymbol Q b) r w =
      endpointTransform (μ.restrict Q.carrier) M b r w := by
  unfold endpointTransform
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem Q.measurable] with x hx
  simp [cellSymbol,hx]

theorem cellSymbol_chart_smooth {n : ℕ} (Q : DyadicCube (n+2))
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
    (b : Space (n+2) → Sphere (n+2) → ℂ) (x : Space (n+2)) (y : Space n)
    (hb : x ∈ Q.carrier → ContDiff ℝ ∞ (rotatedChartAmplitude e (b x) y)) :
    ContDiff ℝ ∞ (rotatedChartAmplitude e (cellSymbol Q b x) y) := by
  by_cases hx : x ∈ Q.carrier
  · have he : cellSymbol Q b x = b x := by funext w; simp [cellSymbol,hx]
    rw [he]
    exact hb hx
  · have he : cellSymbol Q b x = fun _ => 0 := by funext w; simp [cellSymbol,hx]
    rw [he]
    exact contDiff_const

theorem capPair_cell_active {d : ℕ} (Q Q' : DyadicCube d) (η : Sphere d → ℝ)
    (b b' : Space d → Sphere d → ℂ) {x : Space d × Space d} {w : Sphere d}
    (h : capPairAmplitude η (cellSymbol Q b) (cellSymbol Q' b') x w ≠ 0) :
    x.1 ∈ Q.carrier ∧ x.2 ∈ Q'.carrier := by
  have hpair := (mul_ne_zero_iff.mp h).2
  exact ⟨cellSymbol_active Q b (mul_ne_zero_iff.mp hpair).1,
    cellSymbol_active Q' b' (by simpa only [star_ne_zero] using (mul_ne_zero_iff.mp hpair).2)⟩

/-- The phase bounds refer to the actual descendant cubes whenever
there is a nonzero cap amplitude. -/
theorem cellCapPair_displacement_bounds {d n : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    (hp : p.length = n) (hq : q.length = n)
    (η : Sphere d → ℝ) (b b' : Space d → Sphere d → ℂ)
    (x : Space d × Space d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hactive : ∃ w, capPairAmplitude η (cellSymbol (Q.descendant p) b)
      (cellSymbol (Q.descendant q) b') x w ≠ 0) :
    ‖x.1-x.2‖ ≤ Real.sqrt d*Q.side ∧
    ‖(x.1-x.2)-((Q.descendant p).center-(Q.descendant q).center)‖ +
      8*δ*‖(Q.descendant p).center-(Q.descendant q).center‖ ≤
        2*Real.sqrt d*(Q.side/(2 : ℝ)^n)+8*δ*(Real.sqrt d*Q.side) := by
  obtain ⟨w,hw⟩ := hactive
  obtain ⟨hx,hx'⟩ := capPair_cell_active _ _ η b b' hw
  exact ⟨Q.descendant_displacement_bound hQ p q hx hx',
    Q.descendant_cap_error hQ p q hp hq hx hx' hδ⟩

theorem endpointCapCrossTerm_cellSymbols {d : ℕ}
    (Q Q' S S' : DyadicCube d) (μ μ' ν ν' : Measure (Space d))
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    (b b' c c' : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ) :
    endpointCapCrossTerm (μ.restrict Q.carrier) (μ'.restrict Q'.carrier)
      (ν.restrict S.carrier) (ν'.restrict S'.carrier) M M' P P' v Ψ b b' c c' η θ =
    endpointCapCrossTerm (μ.restrict Q.carrier) (μ'.restrict Q'.carrier)
      (ν.restrict S.carrier) (ν'.restrict S'.carrier) M M' P P' v Ψ
      (cellSymbol Q b) (cellSymbol Q' b') (cellSymbol S c) (cellSymbol S' c') η θ := by
  unfold endpointCapCrossTerm
  simp_rw [endpointTransform_cellSymbol]

end Falconer

end OAI
