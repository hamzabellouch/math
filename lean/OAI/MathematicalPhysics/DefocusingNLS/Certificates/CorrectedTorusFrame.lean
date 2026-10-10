import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.SampledSchwartzFrame
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.NearIdentityInverse
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphReconstruction

namespace OAI

/-! # Exact, uniformly bounded right inverses of torus coordinates -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem exists_correctedTorusFrame {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (π : HomogeneousY a k →L[ℝ] F) (hπ : Function.Surjective π) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
      ∃ E₀ : F →L[ℝ] FourierL2,
        (expandingCoordinates a k ha ha1 hk χ π L).comp E₀ =
          ContinuousLinearMap.id ℝ F ∧ ‖E₀‖ ≤ C := by
  obtain ⟨B, hB⟩ := exists_homogeneousSchwartz_frame a k ha ha1 hk π hπ
  obtain ⟨C, hC, hCb⟩ := sampledSchwartzFrame_uniform_bound a k ha1 hk B
  obtain ⟨L₀, hL₀⟩ := sampledSchwartzFrame_coordinate_approximation a k ha ha1 hk
    χ ρ hρ hχ π B hB (1 / 2) (by norm_num)
  refine ⟨C * 2, mul_nonneg hC (by norm_num), L₀, ?_⟩
  intro L hL
  obtain ⟨D, _, hAD, hD⟩ := exists_nearIdentity_inverse _ (hL₀ L hL)
  refine ⟨(sampledSchwartzFrame a k ha1 hk B L).comp D, ?_, ?_⟩
  · rw [← ContinuousLinearMap.comp_assoc]
    exact hAD
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hCb L) hD (norm_nonneg _) hC)

theorem exists_boundedTorusFrame {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (π : HomogeneousY a k →L[ℝ] F) (hπ : Function.Surjective π) :
    ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ, ∃ ζ : Radius → F →L[ℝ] FourierL2,
      ∀ L : Radius, L₀ ≤ L.1 →
        (expandingCoordinates a k ha ha1 hk χ π L).comp (ζ L) =
          ContinuousLinearMap.id ℝ F ∧
        ‖ζ L‖ ≤ C ∧
        ‖stableFrameProjection (ζ L) (expandingCoordinates a k ha ha1 hk χ π L)‖ ≤ C := by
  classical
  obtain ⟨Cζ, hCζ, L₀, hframe⟩ := exists_correctedTorusFrame a k ha ha1 hk χ ρ hρ hχ π hπ
  obtain ⟨CJ, hCJ, hJ⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  let Cπ := ‖π‖ * CJ
  have hCπ : 0 ≤ Cπ := mul_nonneg (norm_nonneg _) hCJ
  let ζ : Radius → F →L[ℝ] FourierL2 := fun L =>
    if hL : L₀ ≤ L.1 then (hframe L hL).choose else 0
  have hz (L : Radius) (hL : L₀ ≤ L.1) :
      (expandingCoordinates a k ha ha1 hk χ π L).comp (ζ L) =
        ContinuousLinearMap.id ℝ F ∧ ‖ζ L‖ ≤ Cζ := by
    simpa only [ζ, dite_eq_left hL] using (hframe L hL).choose_spec
  refine ⟨1 + Cζ + Cζ * Cπ, by positivity, L₀, ζ, ?_⟩
  intro L hL
  obtain ⟨he, hb⟩ := hz L hL
  have hπb : ‖expandingCoordinates a k ha ha1 hk χ π L‖ ≤ Cπ :=
    expandingCoordinates_norm_le a k CJ ha ha1 hk hCJ χ π hJ L
  refine ⟨he, by nlinarith, ?_⟩
  calc
    _ ≤ ‖ContinuousLinearMap.id ℝ FourierL2‖ +
        ‖(ζ L).comp (expandingCoordinates a k ha ha1 hk χ π L)‖ := norm_sub_le _ _
    _ ≤ 1 + Cζ * Cπ := add_le_add (ContinuousLinearMap.norm_id_le)
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hb hπb (norm_nonneg _) hCζ))
    _ ≤ _ := by linarith

theorem exists_boundedTorusRangeFrame {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (π : HomogeneousY a k →L[ℝ] F) :
    ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ, ∃ ζ : Radius → π.range →L[ℝ] FourierL2,
      ∀ L : Radius, L₀ ≤ L.1 →
        (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L).comp (ζ L) =
          ContinuousLinearMap.id ℝ π.range ∧
        ‖ζ L‖ ≤ C ∧
        ‖stableFrameProjection (ζ L)
          (expandingCoordinates a k ha ha1 hk χ π.rangeRestrict L)‖ ≤ C := by
  apply exists_boundedTorusFrame a k ha ha1 hk χ ρ hρ hχ π.rangeRestrict
  rintro ⟨v, u, hu⟩
  exact ⟨u, Subtype.ext hu⟩

end DefocusingNLS

end OAI
