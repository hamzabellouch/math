import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.OpenPlaneBoxes
import OAI.Analysis.RieszRectifiability.Projections.CountableProjectionLimits
import OAI.Analysis.RieszRectifiability.Limits.GlobalSignedLimit

namespace OAI

/-!
# Global projection heights

Countable projection limits agree on open overlaps and glue to a measurable height on
the coordinate plane. The common subsequence preserves local second moments and
pairings with compactly supported Lipschitz tests.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem exists_global_projection_height {ι : Type*} [Fintype ι] {d : ℕ}
    (I : ℕ → Box ι) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) (s : ℕ → Set (Ambient d))
    (hs : ∀ H, IsOpen (s H)) (hcover : ∀ x, ∃ H, x ∈ s H)
    (μ : ℕ → ℕ → FiniteMeasure (Ambient d))
    (hrestrict : ∀ H j, (μ H j : Measure (Ambient d)) = (σ j).restrict (s H))
    (hplane : ∀ H, (coordinatePlaneMeasure e).restrict (s H) = boxPlaneMeasure (I H) e)
    (hweak : ∀ H, Tendsto (μ H) atTop (𝓝 (boxPlaneFiniteMeasure (I H) e)))
    (hcoords : ∀ H j, ∀ᵐ x ∂(μ H j : Measure (Ambient d)), π x ∈ I H)
    (hheight : ∀ H k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(μ H j : Measure (Ambient d)), dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (w : ℕ → Ambient d → ℝ) (hw : ∀ H j, MemLp (w j) 2 (μ H j : Measure (Ambient d)))
    (B E : ℕ → ℝ) (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(μ H j : Measure (Ambient d))) ≤ B H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (Fintype.card ι) (w j) q.1 q.2)
      ((μ H j : Measure (Ambient d)).prod (μ H j : Measure (Ambient d))))
    (hE : ∀ H j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (Fintype.card ι) (w j) q.1 q.2
      ∂(μ H j : Measure (Ambient d)).prod (μ H j : Measure (Ambient d))) ≤ E H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (s H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, w (φ j) x ^ 2 ∂(σ (φ j)).restrict (s H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (s H)))) ∧
      ∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
        Tendsto (fun j => ∫ x, w (φ j) x * ψ x ∂(σ (φ j)).restrict (s H)) atTop
          (𝓝 (∫ x, f x * ψ x ∂(coordinatePlaneMeasure e).restrict (s H))) := by
  obtain ⟨φ, hφ, v, hsecond, hmoment⟩ := exists_countable_projection_limits I e π K he
    hπ.continuous hleft μ hweak hcoords hheight (fun _ j => w j) hw B E hB henergy hE
  let ν := coordinatePlaneMeasure e
  let : IsFiniteMeasureOnCompacts ν :=
    coordinatePlaneMeasure_finite_on_compacts e π he.continuous.measurable Q hπ hleft
  have hv : ∀ H, MemLp (fun x => v H x) 2 (ν.restrict (s H)) := by
    intro H
    rw [show ν.restrict (s H) = boxPlaneMeasure (I H) e from hplane H]
    exact Lp.memLp (v H)
  have hm : ∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
      Tendsto (fun j => ∫ x, w (φ j) x * ψ x ∂(σ (φ j)).restrict (s H)) atTop
        (𝓝 (∫ x, v H x * ψ x ∂ν.restrict (s H))) := by
    intro H ψ L A _ hLip hA
    have hψ : MemLp ψ 2 (boxPlaneMeasure (I H) e) :=
      MemLp.of_bound hLip.continuous.aestronglyMeasurable A
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hA x)
    have hψj : ∀ j, MemLp ψ 2 (μ H (φ j) : Measure (Ambient d)) :=
      fun _ => MemLp.of_bound hLip.continuous.aestronglyMeasurable A
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hA x)
    rw [show ν.restrict (s H) = boxPlaneMeasure (I H) e from hplane H]
    simpa only [hrestrict] using! hmoment H ψ L hLip hψ hψj
  have hcompat : ∀ H J, (fun x => v H x) =ᵐ[ν.restrict (s H ∩ s J)] (fun x => v J x) := by
    intro H J
    exact local_L2_agreement_on_open_overlap (fun j => σ (φ j)) ν (s H) (s J) (hs H) (hs J)
      (v H) (v J) (hv H) (hv J) (fun j => w (φ j)) (hm H) (hm J)
  obtain ⟨f, hfm, hf⟩ := exists_measurable_glue_of_local_L2 ν s (fun H => (hs H).measurableSet)
    hcover (fun H x => v H x) (fun H => (Lp.stronglyMeasurable (v H)).measurable) hv hcompat
  refine ⟨φ, hφ, f, hfm, (fun H => (hf H).2), ?_, ?_⟩
  · intro H
    have hnorm : (∫ x, f x ^ 2 ∂ν.restrict (s H)) = ‖v H‖ ^ 2 := by
      calc
        _ = ∫ x, v H x ^ 2 ∂ν.restrict (s H) := by
          apply integral_congr_ae
          filter_upwards [(hf H).1] with x hx
          rw [hx]
        _ = ∫ x, v H x ^ 2 ∂boxPlaneMeasure (I H) e := by rw [hplane H]
        _ = ‖v H‖ ^ 2 := by
          symm
          simpa only [Lp.toLp_coeFn] using!
            toLp_norm_sq_eq_integral (boxPlaneMeasure (I H) e) (v H) (Lp.memLp (v H))
    rw [show (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (s H)) = ‖v H‖ ^ 2 from hnorm]
    simpa only [hrestrict] using! hsecond H
  · intro H ψ L A hc hLip hA
    have heq : (∫ x, f x * ψ x ∂ν.restrict (s H)) = ∫ x, v H x * ψ x ∂ν.restrict (s H) := by
      apply integral_congr_ae
      filter_upwards [(hf H).1] with x hx
      rw [hx]
    rw [show (∫ x, f x * ψ x ∂(coordinatePlaneMeasure e).restrict (s H)) =
      ∫ x, v H x * ψ x ∂ν.restrict (s H) from heq]
    exact hm H ψ L A hc hLip hA

end

end RieszRectifiability

end OAI
