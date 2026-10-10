import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousTorusLinearStep
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffCoordinateInverse

namespace OAI

/-! # Continuous normalized torus data from kernel decay and coordinate transfer -/

open scoped SchwartzMap NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem continuous_torusLinearSteps_of_transfer {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (π : HomogeneousY a k →L[ℝ] F)
    (A : ℝ≥0 → Radius → FourierL2 →L[ℝ] FourierL2)
    (hkernel : ∀ β : ℝ, 0 < β → ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      ∀ T : ℝ≥0, T₀ ≤ T → ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
        ∀ f : FourierL2, ‖f‖ ≤ 1 →
          π (homogeneousLocalizationCLM a k L.1 ha ha1 hk L.2 χ f) = 0 → ‖A T L f‖ < β)
    (hcoord : ∀ T, HasContractingTorusCoordinateTransfer a k ha ha1 hk χ π T (A T))
    (hA : ∀ T, ∃ C : ℝ, 0 ≤ C ∧ ∀ L, ‖A T L‖ ≤ C) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T : ℝ≥0, T₀ ≤ T →
      HasContinuousTorusLinearStep (F := π.range) T (A T) := by
  have hsurj : Function.Surjective π.rangeRestrict := by
    rintro ⟨v, u, hu⟩
    exact ⟨u, Subtype.ext hu⟩
  obtain ⟨C, hC, Lf, ζ, hζc, hζ⟩ := exists_continuous_boundedTorusFrame
    a k ha ha1 hk χ ρ hρ hχ π.rangeRestrict hsurj
  obtain ⟨T₀, hT₀, hT⟩ := hkernel ((1 / 8) / (C * C)) (by positivity)
  refine ⟨T₀, hT₀, ?_⟩
  intro T hTT
  obtain ⟨Lk, hLk⟩ := hT T hTT
  obtain ⟨D, R, hDR, hR, hdefect⟩ := hcoord T
  obtain ⟨CA, hCA, hAb⟩ := hA T
  obtain ⟨CJ, hCJ, hJ⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  let Cπ := ‖π.rangeRestrict‖ * CJ
  have hCπ : 0 ≤ Cπ := mul_nonneg (norm_nonneg π.rangeRestrict) hCJ
  apply continuous_torusLinearStep_of_frames T (A T) ζ
    (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict) D R hDR hR
    (max Lf Lk) C Cπ CA hC.le hCπ hCA
  · intro L hL
    obtain ⟨he, hz, hp⟩ := hζ L ((le_max_left _ _).trans hL)
    exact ⟨fun v => congrArg (fun B : π.range →L[ℝ] π.range => B v) he, hz,
      expandingCoordinates_norm_le a k CJ ha ha1 hk hCJ χ π.rangeRestrict hJ L, hp⟩
  · intro L hL
    have hLf : Lf ≤ L.1 := (le_max_left _ _).trans hL
    have hLR : Lf ≤ (torusEndpointRadius T L).1 := hLf.trans (torusEndpointRadius_ge T L)
    have hb := stableProjectedBlock_of_kernel_bound (ζ L) (ζ (torusEndpointRadius T L))
      (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L)
      (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict (torusEndpointRadius T L))
      (A T L) C ((1 / 8) / (C * C)) hC.le (by positivity)
      (fun v => congrArg (fun B : π.range →L[ℝ] π.range => B v) (hζ L hLf).1)
      (hζ L hLf).2.2 (hζ _ hLR).2.2
    have hunit : ∀ f : FourierL2, ‖f‖ ≤ 1 →
        expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L f = 0 →
        ‖A T L f‖ ≤ (1 / 8) / (C * C) := by
      intro f hf hz
      have he : π (homogeneousLocalizationCLM a k L.1 ha ha1 hk L.2 χ f) = 0 :=
        congrArg (fun v : π.range => (v : F)) hz
      exact (hLk L ((le_max_right _ _).trans hL) f hf he).le
    apply (hb hunit).trans_eq
    field_simp
  · exact hAb
  · exact hdefect
  · apply hζc.mono
    intro L hL
    exact (le_max_left Lf Lk).trans hL
  · exact continuous_expandingCoordinates_apply a k ha ha1 hk χ π.rangeRestrict

end DefocusingNLS

end OAI
