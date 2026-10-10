import OAI.Probability.StrongRayleigh.GroupDrift
import OAI.Probability.StrongRayleigh.InnovationInverse

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.GroupInnovation

universe u

abbrev Path := PathRealization.Path

local instance : MeasurableSpace Path := borel Path
local instance : BorelSpace Path := ⟨rfl⟩

variable {Γ : Type u} [Group Γ] [Countable Γ] [DecidableEq Γ]

def drift (μ : ProbabilityMeasure (Γ → Bool))
    (p : ℝ≥0 × (Γ → ℝ)) : Γ → ℝ :=
  groupDrift μ p.1 p.2

theorem measurable_drift (μ : ProbabilityMeasure (Γ → Bool)) :
    Measurable (drift μ) := by
  change Measurable (fun p : ℝ≥0 × (Γ → ℝ) => groupDrift μ (p.1 : ℝ) p.2)
  have htime : Measurable (fun p : ℝ≥0 × (Γ → ℝ) => (p.1 : ℝ)) :=
    measurable_coe_nnreal_real.comp measurable_fst
  have hpair : Measurable (fun p : ℝ≥0 × (Γ → ℝ) => ((p.1 : ℝ), p.2)) :=
    htime.prodMk measurable_snd
  have h := (measurable_groupDrift μ).comp hpair
  exact h

theorem drift_mem_unitInterval (μ : ProbabilityMeasure (Γ → Bool))
    (p : ℝ≥0 × (Γ → ℝ)) (i : Γ) : 0 ≤ drift μ p i ∧ drift μ p i ≤ 1 :=
  groupDrift_mem_Icc μ p.1 p.2 i

theorem abs_drift_le_one (μ : ProbabilityMeasure (Γ → Bool))
    (p : ℝ≥0 × (Γ → ℝ)) (i : Γ) : |drift μ p i| ≤ 1 := by
  rw [abs_of_nonneg (drift_mem_unitInterval μ p i).1]
  exact (drift_mem_unitInterval μ p i).2

def transform (μ : ProbabilityMeasure (Γ → Bool)) : (Γ → Path) → Γ → Path :=
  PathRealization.innovation (drift μ) (measurable_drift μ) 1 (abs_drift_le_one μ)

theorem measurable_transform (μ : ProbabilityMeasure (Γ → Bool)) :
    Measurable (transform μ) :=
  PathRealization.measurable_innovation (measurable_drift μ) 1 (abs_drift_le_one μ)

@[simp] theorem transform_apply (μ : ProbabilityMeasure (Γ → Bool))
    (y : Γ → Path) (i : Γ) (t : ℝ≥0) :
    transform μ y i t = y i t - ∫ s in (0 : ℝ)..(t : ℝ),
      groupDrift μ (s.toNNReal : ℝ) (fun j => y j s.toNNReal) i := by
  rfl

theorem transform_apply_real_time (μ : ProbabilityMeasure (Γ → Bool))
    (y : Γ → Path) (i : Γ) (t : ℝ≥0) :
    transform μ y i t = y i t - ∫ s in (0 : ℝ)..(t : ℝ),
      groupDrift μ s (fun j => y j s.toNNReal) i := by
  rw [transform_apply]
  apply congrArg (fun r : ℝ => y i t - r)
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : (0 : ℝ) ≤ s :=
    (le_min (le_refl (0 : ℝ)) t.property).trans hs.1
  change groupDrift μ (s.toNNReal : ℝ) (fun j => y j s.toNNReal) i =
    groupDrift μ s (fun j => y j s.toNNReal) i
  simp only [Real.toNNReal_of_nonneg hs0, NNReal.coe_mk]

theorem transform_leftTranslate (μ : ProbabilityMeasure (Γ → Bool))
    (hμ : InvariantBinaryLaw μ) (g : Γ) (y : Γ → Path) :
    transform μ (leftTranslate g y) = leftTranslate g (transform μ y) := by
  apply PathRealization.innovation_leftTranslate
  intro g t x i
  exact congrFun (groupDrift_leftTranslate μ hμ g t x) i

theorem exists_equivariant_leftInverse_of_finite_response
    (hresponse : ∀ (F : Type u) [Fintype F] [Nonempty F]
      (ν : ProbabilityMeasure (F → Bool)), StronglyRayleighFinite ν →
      ∀ (i : F) (h h' : F → ℝ) (D : ℝ), 0 ≤ D →
        (∀ j, |h j - h' j| ≤ D) → |tiltMean ν h i - tiltMean ν h' i| ≤ D / 2)
    (μ : ProbabilityMeasure (Γ → Bool))
    (hSR : StronglyRayleighCountable μ) (hInv : InvariantBinaryLaw μ) :
    ∃ Z : (Γ → Path) → (Γ → Path),
      Measurable Z ∧
      (∀ g w, Z (leftTranslate g w) = leftTranslate g (Z w)) ∧
      Function.LeftInverse Z (transform μ) := by
  apply PathRealization.exists_equivariant_innovation_leftInverse
    (measurable_drift μ) 1 (abs_drift_le_one μ) (drift_mem_unitInterval μ)
    ((1 : ℝ) / 2) (by positivity)
  · intro t x y D hD hxy i
    simpa only [drift, div_eq_mul_inv, one_mul, mul_comm] using
      groupDrift_response_of_finite_response hresponse μ hSR t x y D hD hxy i
  · intro g t x i
    exact congrFun (groupDrift_leftTranslate μ hInv g t x) i

end Problem336AdditiveD139.GroupInnovation

end

end OAI
