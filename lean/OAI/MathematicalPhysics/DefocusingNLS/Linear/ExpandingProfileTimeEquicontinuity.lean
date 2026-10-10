import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalTimeBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileUniformBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonprincipalEnergy

namespace OAI

/-! # Uniform time equicontinuity of actual torus propagators on physical balls -/

open Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_expandingProfile_time_bound (a b k Q M T R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L)
      (q : C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ t, ‖q t‖ ≤ Q)
      (f : FourierL2), ‖f‖ ≤ M → ∀ (s t : Icc (0 : ℝ) T) (y : E), ‖y‖ ≤ R →
      let S := expandingProfileTrajectory a b (k + 2) L T ha ha1 (by linarith) hL hT m Q hQ q hq f;
      ‖expandingTorusFunction a (k + 2) (expandingRadius L t) (S t)
          (euclideanToTorus ((expandingRadius L t)⁻¹ • y)) -
        expandingTorusFunction a (k + 2) (expandingRadius L s) (S s)
          (euclideanToTorus ((expandingRadius L s)⁻¹ • y))‖ ≤ C * |(t : ℝ) - s| := by
  obtain ⟨K, hK, hKb⟩ := exists_expandingProfileTrajectory_bound a b (k + 2) ha ha1 (by linarith) m Q hQ
  obtain ⟨D, hD, hDb⟩ := exists_expandingLinearized_norm_bound a (k + 2) Q ha ha1 (by linarith) hQ m
  let A := (K + 1) * Real.exp ((K + 1) * T) * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := (|a| + |b| + 1 + R / 2) * expandingJetBound a k * A + expandingEmbeddingBound a (k + 2) * (D * A)
  have hC : 0 ≤ C := by dsimp [C, expandingJetBound, expandingEmbeddingBound]; positivity
  refine ⟨C, hC, ?_⟩
  intro L hL q hq f hf s t y hy S
  let l := expandingRadiusCurve L T hL
  let g := expandingReactionHistory T hT (expandingProfileReaction a (k + 2) T ha ha1 (by linarith) m l q 0) S
  have hgcont : Continuous g := continuous_expandingReactionHistory T hT _ S
  have hSb (s : Icc (0 : ℝ) T) : ‖S s‖ ≤ A :=
    ((ContinuousMap.norm_coe_le_norm S s).trans (hKb L T hL hT q hq f)).trans
      (mul_le_mul_of_nonneg_left hf (by positivity))
  have hgb (τ : ℝ) (_hτ : τ ∈ Icc 0 T) : ‖g τ‖ ≤ D * A := by
    let v := projIcc 0 T hT τ
    have he : g τ = expandingLinearizedPotential a (k + 2) (l v).1 ha ha1 (by linarith) (l v).2 m (q v) (S v) := by
      change (-Complex.I) • _ + (0 : FourierL2) = _
      exact add_zero _
    rw [he]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right (hDb (l v).1 (l v).2 (q v) (hq v)) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hSb v) hD))
  have hb := expandingMild_physical_time_bound a b k L T A (D * A) ha ha1 hk hL hT S g f hgcont.continuousOn
    (fun v => expandingProfileTrajectory_eq a b (k + 2) L T ha ha1 (by linarith) hL hT m Q hQ q hq f v)
    hSb hgb y s t
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  dsimp only [C]
  gcongr
  dsimp [expandingJetBound, expandingEmbeddingBound]
  positivity

end DefocusingNLS

end OAI
