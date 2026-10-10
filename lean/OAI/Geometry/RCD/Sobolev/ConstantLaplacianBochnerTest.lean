import OAI.Geometry.RCD.Sobolev.ConstantSourceCancellation

namespace OAI

/-! # The local constant-Laplacian Bochner inequality -/

open Set MeasureTheory
open scoped NNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.constant_laplacian_bochner_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] φ)
    (d : Lp ℝ 2 (hausdorff n X)) (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (c : ℝ)
    (hc : d =ᵐ[(hausdorff n X).restrict Ω] fun _ => c)
    (G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic u u)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) {v : X → ℝ} {A : ℝ≥0}
    (hv : LipschitzWith A v) (hw : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] v)
    (hvs : tsupport v ⊆ Ω) (C : ℝ≥0) (hvb : ∀ x, |v x| ≤ C) (hv0 : ∀ x, 0 ≤ v x) :
    0 ≤ -(1 / 2 : ℝ) * energyForm (hausdorff n X) hX.quadratic G w -
      K * inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic w)
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic G) := by
  have h := hX.compact_bochner_test hn hφ hs p u hu d hd G hG w hv hw C hvb hv0
  have hcanc := constant_source_cancellation (hausdorff n X) hX.quadratic u d hd hΩ c hc w v hw hvs
  linarith

theorem NoncollapsedRCD.constant_laplacian_bochner_sobolev_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] φ)
    (d : Lp ℝ 2 (hausdorff n X)) (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (c : ℝ)
    (hc : d =ᵐ[(hausdorff n X).restrict Ω] fun _ => c)
    (G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic u u)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) {v : X → ℝ}
    (hv : Measurable v) (hw : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] v)
    (hvs : tsupport v ⊆ Ω) (C : ℝ≥0) (hvb : ∀ x, |v x| ≤ C) (hv0 : ∀ x, 0 ≤ v x) :
    0 ≤ -(1 / 2 : ℝ) * energyForm (hausdorff n X) hX.quadratic G w -
      K * inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic w)
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic G) := by
  have h := hX.compact_bochner_sobolev_test hn hφ hs p u hu d hd G hG w hv hw C hvb hv0
  have hcanc := constant_source_cancellation (hausdorff n X) hX.quadratic u d hd hΩ c hc w v hw hvs
  linarith

end RegularPointCoordinates

end OAI
