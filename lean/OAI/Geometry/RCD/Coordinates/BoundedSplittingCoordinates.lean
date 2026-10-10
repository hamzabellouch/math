import OAI.Geometry.RCD.Harmonic.QuadraticModelValues

namespace OAI

/-! # First-order splitting data are local to their representatives -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Local equality in both slots preserves the actual gradient pairing. -/
theorem localGamma_pair_congr_ae {Ω : Set X} {f f' g g' : SobolevSpace μ hQ}
    (hf : SobolevSpace.toLp μ hQ f' =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ f)
    (hg : SobolevSpace.toLp μ hQ g' =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g) :
    localGamma μ hQ f' g' =ᵐ[μ.restrict Ω] localGamma μ hQ f g := by
  filter_upwards [hf, hg,
    ae_restrict_of_ae (localGamma_eq_on_eq μ hQ f' f g'),
    ae_restrict_of_ae (localGamma_comm μ hQ f g'),
    ae_restrict_of_ae (localGamma_eq_on_eq μ hQ g' g f),
    ae_restrict_of_ae (localGamma_comm μ hQ g f)] with x hf hg h₁ h₂ h₃ h₄
  exact (h₁ hf).trans (h₂.trans ((h₃ hg).trans h₄))

/-- Changing global Sobolev extensions preserves every first-order splitting
condition when the local pointwise coordinate representative is unchanged. -/
theorem FirstOrderSplittingOn.congr_representative {n : ℕ} {p : X} {r ε : ℝ}
    {u u' : Fin n → SobolevSpace μ hQ} {v : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ p r ε u v)
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (u' j) =ᵐ[μ.restrict (ball p r)] fun x => v x j) :
    FirstOrderSplittingOn μ hQ p r ε u' v := by
  have heq (j : Fin n) : SobolevSpace.toLp μ hQ (u' j) =ᵐ[μ.restrict (ball p r)]
      SobolevSpace.toLp μ hQ (u j) := (hrep j).trans (h.representative j).symm
  have hg (i j : Fin n) := localGamma_pair_congr_ae μ hQ (heq i) (heq j)
  refine ⟨hrep, h.continuous, fun j => (h.harmonic j).congr_ae μ hQ measurableSet_ball (heq j), ?_, ?_⟩
  · intro j
    filter_upwards [hg j j, h.gradient j] with x hx hb
    rwa [hx]
  · intro i j
    have hi : (∫ x in ball p r, |localGamma μ hQ (u' i) (u' j) x - if i = j then 1 else 0| ∂μ) =
        ∫ x in ball p r, |localGamma μ hQ (u i) (u j) x - if i = j then 1 else 0| ∂μ := by
      apply integral_congr_ae
      filter_upwards [hg i j] with x hx
      rw [hx]
    rw [hi]
    exact h.gram i j

/-- A centered metric approximation supplies globally bounded extensions
of the SAME local splitting map; no global boundedness input is required. -/
theorem bounded_normalized_splitting {n : ℕ} {p : X} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn μ hQ p (4 * r) ε u v) (hv : v p = 0)
    (hmetric : IsPointedApproximation p 0 r 4 ε (fun x => r⁻¹ • v x)) :
    ∃ u' : Fin n → SobolevSpace μ hQ,
      (∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u' j) x| ≤ 5 * r) ∧
      FirstOrderSplittingOn μ hQ p (4 * r) ε u' v := by
  have hb := bounded_metric_coordinates μ hQ hr (by norm_num : (0 : ℝ) ≤ 4) hε
    u v hfirst.harmonic hfirst.representative hv hmetric
  let C : ℝ≥0 := ⟨r * (4 + ε), mul_nonneg hr.le (by positivity)⟩
  let u' := fun j => boundedLocalVersion μ hQ (u j) C
  refine ⟨u', ?_, hfirst.congr_representative μ hQ hb.2.2⟩
  intro j
  filter_upwards [hb.1 j] with x hx
  have hscale : r * (4 + ε) ≤ 5 * r := by nlinarith
  exact hx.trans hscale

end RegularPointCoordinates

end

end OAI
