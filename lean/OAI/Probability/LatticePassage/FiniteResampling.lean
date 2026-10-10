import OAI.Probability.LatticePassage.FiniteProduct
import OAI.Probability.LatticePassage.ResamplingMoment
import OAI.Probability.LatticePassage.ResamplingSymmetry

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma extendLocalCoordinates_update (x : Vertex) (R : ℕ)
    (v : LocalCoordinates x R) (e : ↥(localEdges x R)) (u : ℝ) :
    extendLocalCoordinates x R (Function.update v e u) =
      Function.update (extendLocalCoordinates x R v) e.val u := by
  classical
  funext f
  by_cases hf : f = e.val
  · subst f
    simp [extendLocalCoordinates, e.property]
  · by_cases hm : f ∈ localEdges x R
    · have hne : (⟨f,hm⟩ : ↥(localEdges x R)) ≠ e := by
        intro h
        exact hf (congrArg Subtype.val h)
      simp [extendLocalCoordinates, hm, Function.update_of_ne hf, Function.update_of_ne hne]
    · simp [extendLocalCoordinates, hm, Function.update_of_ne hf]

lemma finite_upward_moment_sum (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (v : LocalCoordinates x R) (hv : ∀ e, 0 ≤ v e)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ e : ↥(localEdges x R), ∫⁻ u,
      ENNReal.ofReal ((max (finitePassageTime x y R (Function.update v e u) -
        finitePassageTime x y R v) 0)^k) ∂expMeasure 1) ≤ (k.factorial : ℝ≥0∞)*R := by
  classical
  have hn : ∀ e, 0 ≤ extendLocalCoordinates x R v e := by
    intro e
    unfold extendLocalCoordinates
    split_ifs with he
    · exact hv ⟨e,he⟩
    · exact le_rfl
  have h := sum_upwardResampling_lmoment (extendLocalCoordinates x R v) hn x y R hR k hk
  rw [← sum_attach (localEdges x R)] at h
  simpa only [attach_eq_univ, finitePassageTime, extendLocalCoordinates_update, upwardResampling]
    using h

lemma finite_coordinates_nonnegative (x : Vertex) (R : ℕ) :
    ∀ᵐ v ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1), ∀ e, 0 ≤ v e := by
  rw [ae_all_iff]
  intro e
  exact ((measurePreserving_eval (fun _ : ↥(localEdges x R) => expMeasure 1) e).quasiMeasurePreserving.ae
    exponential_positive).mono (fun _ h => h.le)

theorem finite_positive_resampling_lmoment (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (k : ℕ) (hk : 1 ≤ k) :
    (∑ e : ↥(localEdges x R), ∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
      ENNReal.ofReal ((max (finitePassageTime x y R (Function.update z.1 e (z.2 e)) -
        finitePassageTime x y R z.1) 0)^k)
      ∂(Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)).prod
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))) ≤
      (k.factorial : ℝ≥0∞)*R := by
  classical
  let μ := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  have he : ∀ e : ↥(localEdges x R),
      (∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
        ENNReal.ofReal ((max (finitePassageTime x y R (Function.update z.1 e (z.2 e)) -
          finitePassageTime x y R z.1) 0)^k) ∂μ.prod μ) =
      ∫⁻ v, ∫⁻ u, ENNReal.ofReal ((max
        (finitePassageTime x y R (Function.update v e u) - finitePassageTime x y R v) 0)^k)
        ∂expMeasure 1 ∂μ := by
    intro e
    rw [lintegral_prod _ (by fun_prop)]
    apply lintegral_congr
    intro v
    have hm := lintegral_map (μ := μ)
      (show Measurable (fun u : ℝ => ENNReal.ofReal ((max
        (finitePassageTime x y R (Function.update v e u) - finitePassageTime x y R v) 0)^k))
          from by fun_prop) (measurable_pi_apply e)
    rw [(measurePreserving_eval (fun _ : ↥(localEdges x R) => expMeasure 1) e).map_eq] at hm
    exact hm.symm
  change (∑ e, ∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
    ENNReal.ofReal ((max (finitePassageTime x y R (Function.update z.1 e (z.2 e)) -
      finitePassageTime x y R z.1) 0)^k) ∂μ.prod μ) ≤ _
  simp_rw [he]
  rw [← lintegral_finsetSum _ (fun e _ => by fun_prop)]
  calc
    _ ≤ ∫⁻ _ : LocalCoordinates x R, (k.factorial : ℝ≥0∞)*R ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [finite_coordinates_nonnegative x R] with v hv
      exact finite_upward_moment_sum x y R hR v hv k hk
    _ = _ := by simp [μ]

theorem finite_absolute_resampling_lmoment (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (k : ℕ) (hk : 1 ≤ k) :
    (∑ e : ↥(localEdges x R), ∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
      ENNReal.ofReal (|finitePassageTime x y R (Function.update z.1 e (z.2 e)) -
        finitePassageTime x y R z.1|^k)
      ∂(Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)).prod
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))) ≤
      2 * (k.factorial : ℝ≥0∞)*R := by
  classical
  simp_rw [resampling_absolute_lintegral (expMeasure 1) (finitePassageTime x y R)
    (measurable_finitePassageTime x y R) _ k hk, ← mul_sum]
  calc
    _ ≤ 2*((k.factorial : ℝ≥0∞)*R) := by
      gcongr
      exact finite_positive_resampling_lmoment x y R hR k hk
    _ = _ := (mul_assoc _ _ _).symm

end CompanionFPP

end OAI
