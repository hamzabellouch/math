import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPotentialEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedEnergy

namespace OAI

/-! # Integrated local observation for the actual whole-space linear evolution

The constants depend on the fixed profile and k, and are independent of
both initial data and slab length. The proof uses the previously established
mild energy derivative, with no generator-domain hypothesis.
-/

open MeasureTheory Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] homogeneousFreeOperator

theorem homogeneousLinearized_integrated_observation (a b : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (q : HomogeneousY a ((N + 1 : ℕ) : ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : E, ‖homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x‖ ^
      (2 * (m + 1)) ≤ M)
    (hgap : 0 < ((N + 1 : ℕ) : ℝ) + 2 * a - 6 -
      2 * ((2 * ((m + 1 : ℕ) : ℝ) + 1) * M)) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ) (hT : 0 ≤ T) (f : HomogeneousY a ((N + 1 : ℕ) : ℝ)) (t : Icc (0 : ℝ) T),
        let S := homogeneousLinearizedTrajectory a b ((N + 1 : ℕ) : ℝ) T ha ha1 hk hT (m + 1) q f
        ‖S t‖ ^ 2 ≤ Real.exp (-c * (t : ℝ)) * ‖f‖ ^ 2 +
          C * ∫ τ in (0 : ℝ)..(t : ℝ), Real.exp (-c * ((t : ℝ) - τ)) *
            ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) R ha ha1 hk
              (S (projIcc 0 T hT τ))‖ ^ 2 := by
  obtain ⟨c, hc, R, hR, C, hC, henergy⟩ :=
    homogeneousLinearized_energy_observation a N ha ha1 hk m q M hM hQB hgap
  refine ⟨c, hc, R, hR, C, hC, fun T hT f t => ?_⟩
  dsimp only
  let V := homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q
  let S := homogeneousLinearizedTrajectory a b ((N + 1 : ℕ) : ℝ) T ha ha1 hk hT (m + 1) q f
  let r := homogeneousPotentialHistory T hT V S
  let u := homogeneousForcedTrajectory a b ((N + 1 : ℕ) : ℝ) ha ha1 hk f r
  let J := homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) R ha ha1 hk
  have hr : Continuous r := continuous_homogeneousPotentialHistory T hT V S
  have hu : Continuous u := continuous_homogeneousForcedTrajectory a b _ ha ha1 hk f r hr
  have heq (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) : u τ = S (projIcc 0 T hT τ) := by
    change homogeneousFreeOperator a b ((N + 1 : ℕ) : ℝ) τ ha ha1 hk f +
      homogeneousDuhamel a b ((N + 1 : ℕ) : ℝ) ha ha1 hk τ r = S (projIcc 0 T hT τ)
    have hp : projIcc 0 T hT τ = ⟨τ, hτ⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val (projIcc_of_mem hT hτ)
    rw [hp]
    exact (homogeneousLinearizedTrajectory_eq a b _ T ha ha1 hk hT (m + 1) q f ⟨τ,hτ⟩).symm
  have ht : u (t : ℝ) = S t := by
    rw [heq t t.2]
    congr 1
    apply Subtype.ext
    exact congrArg Subtype.val (projIcc_of_mem hT t.2)
  let D := fun τ : ℝ => -a * ‖homogeneousLowEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk (u τ)‖ ^ 2 +
    (6 - 2 * a - ((N + 1 : ℕ) : ℝ)) *
      ‖homogeneousHighEnergy a ((N + 1 : ℕ) : ℝ) ha1 hk (u τ)‖ ^ 2 +
    2 * inner ℝ (u τ) (r τ)
  have hD (τ : ℝ) : HasDerivAt (fun s => ‖u s‖ ^ 2) (D τ) τ :=
    hasDerivAt_homogeneousForcedEnergy a b _ ha ha1 hk f r hr τ
  have hDc : Continuous D := by
    dsimp only [D]
    exact ((continuous_const.mul (((homogeneousLowEnergy a _ ha1 hk).continuous.comp hu).norm.pow 2)).add
      (continuous_const.mul (((homogeneousHighEnergy a _ ha1 hk).continuous.comp hu).norm.pow 2))).add
        (continuous_const.mul (hu.inner hr))
  have hDbound (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) :
      D τ ≤ -c * ‖u τ‖ ^ 2 + C * ‖J (u τ)‖ ^ 2 := by
    have hrt : r τ = V (u τ) := by
      change V (S (projIcc 0 T hT τ)) = V (u τ)
      rw [heq τ hτ]
    dsimp only [D]
    rw [hrt]
    exact henergy (u τ)
  let F := fun τ : ℝ => Real.exp (c * τ) * ‖u τ‖ ^ 2
  let dF := fun τ : ℝ => Real.exp (c * τ) * (c * ‖u τ‖ ^ 2 + D τ)
  have hF (τ : ℝ) : HasDerivAt F (dF τ) τ := by
    have h := (((hasDerivAt_id τ).const_mul c).exp).mul (hD τ)
    convert h using 1
    · rfl
    · dsimp only [dF, id_eq]
      ring
  have hdFc : Continuous dF := by
    dsimp only [dF]
    fun_prop
  have hmono : (∫ τ in (0 : ℝ)..(t : ℝ), dF τ) ≤
      ∫ τ in (0 : ℝ)..(t : ℝ), C * Real.exp (c * τ) * ‖J (u τ)‖ ^ 2 := by
    have hg : Continuous (fun τ : ℝ => C * Real.exp (c * τ) * ‖J (u τ)‖ ^ 2) := by
      fun_prop
    apply intervalIntegral.integral_mono_on t.2.1 (hdFc.intervalIntegrable 0 t)
      (hg.intervalIntegrable 0 t)
    intro τ hτ
    have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans t.2.2⟩
    have h := mul_le_mul_of_nonneg_left (hDbound τ hτT) (Real.exp_nonneg (c * τ))
    dsimp only [dF]
    nlinarith
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun τ _ => hF τ) (hdFc.intervalIntegrable 0 t)
  have hweighted : F (t : ℝ) ≤ F 0 +
      ∫ τ in (0 : ℝ)..(t : ℝ), C * Real.exp (c * τ) * ‖J (u τ)‖ ^ 2 := by
    linarith
  have hF0 : F 0 = ‖f‖ ^ 2 := by
    simp only [F, u, homogeneousForcedTrajectory_zero, mul_zero, Real.exp_zero, one_mul]
  calc
    ‖S t‖ ^ 2 = Real.exp (-c * (t : ℝ)) * F (t : ℝ) := by
      dsimp only [F]
      rw [ht, ← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-c * (t : ℝ)) * (F 0 +
        ∫ τ in (0 : ℝ)..(t : ℝ), C * Real.exp (c * τ) * ‖J (u τ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hweighted (Real.exp_nonneg _)
    _ = _ := by
      rw [hF0, mul_add, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro τ hτ
      have hτT : τ ∈ Icc (0 : ℝ) T := by
        rw [uIcc_of_le t.2.1] at hτ
        exact ⟨hτ.1,hτ.2.trans t.2.2⟩
      dsimp only [J]
      rw [heq τ hτT]
      have hexp : Real.exp (-c * (t : ℝ)) * Real.exp (c * τ) =
          Real.exp (-c * ((t : ℝ) - τ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = C * (Real.exp (-c * (t : ℝ)) * Real.exp (c * τ)) *
            ‖homogeneousLocalL2Observation a ((N + 1 : ℕ) : ℝ) R ha ha1 hk
              (S (projIcc 0 T hT τ))‖ ^ 2 := by ring
        _ = _ := by
          rw [hexp]
          dsimp only [S]
          ring

end DefocusingNLS

end OAI
