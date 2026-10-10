import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ContinuousSampledFrame
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.CorrectedTorusFrame

namespace OAI

/-! # Continuous, uniformly bounded corrected torus frames -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem nearIdentity_ringInverse (A : F →L[ℝ] F)
    (hA : ‖A - ContinuousLinearMap.id ℝ F‖ < 1 / 2) :
    IsUnit A ∧ A.comp (Ring.inverse A) = ContinuousLinearMap.id ℝ F ∧
      (Ring.inverse A).comp A = ContinuousLinearMap.id ℝ F ∧ ‖Ring.inverse A‖ ≤ 2 := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨D, hDA, hAD, hD⟩ := exists_nearIdentity_inverse A hA
  let U : (F →L[ℝ] F)ˣ := ⟨A, D, hAD, hDA⟩
  have hi : Ring.inverse A = D := Ring.inverse_unit U
  exact ⟨⟨U, rfl⟩, hi ▸ hAD, hi ▸ hDA, hi ▸ hD⟩

theorem exists_continuous_boundedTorusFrame
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (π : HomogeneousY a k →L[ℝ] F) (hπ : Function.Surjective π) :
    ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℝ, ∃ ζ : Radius → F →L[ℝ] FourierL2,
      ContinuousOn ζ {L : Radius | L₀ ≤ L.1} ∧
      ∀ L : Radius, L₀ ≤ L.1 →
        (expandingCoordinates a k ha ha1 hk χ π L).comp (ζ L) =
          ContinuousLinearMap.id ℝ F ∧
        ‖ζ L‖ ≤ C ∧
        ‖stableFrameProjection (ζ L) (expandingCoordinates a k ha ha1 hk χ π L)‖ ≤ C := by
  classical
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨B, hB⟩ := exists_homogeneousSchwartz_frame a k ha ha1 hk π hπ
  obtain ⟨CB, hCB, hbound⟩ := sampledSchwartzFrame_uniform_bound a k ha1 hk B
  obtain ⟨L₀, hL₀⟩ := sampledSchwartzFrame_coordinate_approximation a k ha ha1 hk
    χ ρ hρ hχ π B hB (1 / 2) (by norm_num)
  let A := fun L : Radius => (expandingCoordinates a k ha ha1 hk χ π L).comp
    (sampledSchwartzFrame a k ha1 hk B L)
  have hA : Continuous A := continuous_sampledSchwartzFrame_coordinates a k ha ha1 hk χ π B
  have hAi (L : Radius) (hL : L₀ ≤ L.1) := nearIdentity_ringInverse (A L) (hL₀ L hL)
  let ζ := fun L : Radius => (sampledSchwartzFrame a k ha1 hk B L).comp (Ring.inverse (A L))
  have hζc : ContinuousOn ζ {L : Radius | L₀ ≤ L.1} := by
    intro L hL
    obtain ⟨U, hU⟩ := (hAi L hL).1
    have hi : ContinuousAt (fun R => Ring.inverse (A R)) L := by
      exact (hU ▸ NormedRing.inverse_continuousAt U).comp hA.continuousAt
    exact (((continuous_sampledSchwartzFrame a k ha1 hk B).continuousAt).clm_comp hi).continuousWithinAt
  have hζb (L : Radius) (hL : L₀ ≤ L.1) : ‖ζ L‖ ≤ CB * 2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hbound L) (hAi L hL).2.2.2 (norm_nonneg _) hCB)
  obtain ⟨CJ, hCJ, hJ⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  let CP := ‖π‖ * CJ
  have hCP : 0 ≤ CP := mul_nonneg (norm_nonneg _) hCJ
  let C := 1 + CB * 2 + CB * 2 * CP
  refine ⟨C, by dsimp [C]; positivity, L₀, ζ, hζc, ?_⟩
  intro L hL
  refine ⟨?_, (hζb L hL).trans (by
    have hp : 0 ≤ CB * 2 * CP := by positivity
    dsimp [C]
    linarith), ?_⟩
  · dsimp only [ζ]
    rw [← ContinuousLinearMap.comp_assoc]
    exact (hAi L hL).2.1
  · have hp : ‖expandingCoordinates a k ha ha1 hk χ π L‖ ≤ CP :=
      expandingCoordinates_norm_le a k CJ ha ha1 hk hCJ χ π hJ L
    calc
      _ ≤ ‖ContinuousLinearMap.id ℝ FourierL2‖ +
          ‖(ζ L).comp (expandingCoordinates a k ha ha1 hk χ π L)‖ := norm_sub_le _ _
      _ ≤ 1 + CB * 2 * CP := add_le_add ContinuousLinearMap.norm_id_le
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hζb L hL) hp (norm_nonneg _) (by positivity)))
      _ ≤ C := by dsimp [C]; linarith

end DefocusingNLS

end OAI
