import OAI.MathematicalPhysics.DefocusingNLS.Certificates.CorrectedTorusFrame
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.KernelOperatorBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileOperator

namespace OAI

/-! # Corrected finite frames and the stable torus endpoint blocks -/

open scoped SchwartzMap NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

noncomputable def torusEndpointRadius (T : ℝ≥0) (L : Radius) : Radius :=
  expandingRadiusCurve L.1 T L.2 ⟨T, T.2, le_rfl⟩

theorem torusEndpointRadius_ge (T : ℝ≥0) (L : Radius) : L.1 ≤ (torusEndpointRadius T L).1 :=
  expandingRadius_ge L.1 T L.2 T.2

def HasTorusStableBlocks {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ))
    (π : HomogeneousY a k →L[ℝ] F)
    (A : ℝ≥0 → Radius → FourierL2 →L[ℝ] FourierL2) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Lf : ℝ, ∃ ζ : Radius → π.range →L[ℝ] FourierL2,
    (∀ L : Radius, Lf ≤ L.1 →
      (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L).comp (ζ L) =
        ContinuousLinearMap.id ℝ π.range ∧
      ‖ζ L‖ ≤ C ∧
      ‖stableFrameProjection (ζ L)
        (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L)‖ ≤ C) ∧
    ∀ β : ℝ, 0 < β → ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      ∀ T : ℝ≥0, T₀ ≤ T → ∃ L₀ : ℝ, Lf ≤ L₀ ∧
        ∀ L : Radius, L₀ ≤ L.1 →
          ‖stableProjectedBlock (ζ L) (ζ (torusEndpointRadius T L))
            (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L)
            (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict (torusEndpointRadius T L))
            (A T L)‖ ≤ β

theorem hasTorusStableBlocks_of_kernel_decay {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (π : HomogeneousY a k →L[ℝ] F)
    (A : ℝ≥0 → Radius → FourierL2 →L[ℝ] FourierL2)
    (hstable : ∀ β : ℝ, 0 < β → ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      ∀ T : ℝ≥0, T₀ ≤ T → ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
        ∀ f : FourierL2, ‖f‖ ≤ 1 →
          π (homogeneousLocalizationCLM a k L.1 ha ha1 hk L.2 χ f) = 0 →
          ‖A T L f‖ < β) :
    HasTorusStableBlocks a k ha ha1 hk χ π A := by
  obtain ⟨C, hC, Lf, ζ, hζ⟩ := exists_boundedTorusRangeFrame a k ha ha1 hk χ ρ hρ hχ π
  refine ⟨C, hC, Lf, ζ, hζ, ?_⟩
  intro β hβ
  obtain ⟨T₀, hT₀, hT⟩ := hstable (β / (C * C)) (by positivity)
  refine ⟨T₀, hT₀, ?_⟩
  intro T hTT
  obtain ⟨L₀, hL₀⟩ := hT T hTT
  refine ⟨max Lf L₀, le_max_left _ _, ?_⟩
  intro L hL
  have hLf : Lf ≤ L.1 := (le_max_left _ _).trans hL
  have hLR : Lf ≤ (torusEndpointRadius T L).1 := hLf.trans (torusEndpointRadius_ge T L)
  have hb := stableProjectedBlock_of_kernel_bound (ζ L) (ζ (torusEndpointRadius T L))
    (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L)
    (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict (torusEndpointRadius T L))
    (A T L) C (β / (C * C)) hC.le (by positivity)
    (fun v => congrArg (fun B : π.range →L[ℝ] π.range => B v) (hζ L hLf).1)
    (hζ L hLf).2.2 (hζ _ hLR).2.2
  have hunit : ∀ f : FourierL2, ‖f‖ ≤ 1 →
      expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L f = 0 →
      ‖A T L f‖ ≤ β / (C * C) := by
    intro f hf hzero
    have hz : π (homogeneousLocalizationCLM a k L.1 ha ha1 hk L.2 χ f) = 0 :=
      congrArg (fun v : π.range => (v : F)) hzero
    exact (hL₀ L ((le_max_right _ _).trans hL) f hf hz).le
  apply (hb hunit).trans_eq
  field_simp

end DefocusingNLS

end OAI
