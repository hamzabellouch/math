import OAI.Analysis.KadisonSimilarity.Derivation.FiniteDerivationColumns

namespace OAI

/-! The two-test-vector specialization of matrix Kaplansky density and
C*-quotient norm lifting is enough for the scalar commutator closure used
in the final derivation and separability reductions. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Blackadar, I.9.1.3, specialized to two vectors, followed by quotient norm
lifting. This precise published input contains no commutator estimate. -/
def TwoVectorKaplanskyInput (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (P : VonNeumannAlgebra H) : Prop :=
  ∀ b ∈ P, ∀ x y : H, ∀ ε : ℝ, 0 < ε → ∃ a : A,
    ‖a‖ ≤ ‖b‖ + ε ∧ ‖σ a x - b x‖ ≤ ε ∧ ‖σ a y - b y‖ ≤ ε

/-- A bound on the original algebra extends to its von Neumann closure using
only the two vectors needed for each commutator test. -/
theorem scalarKaplanskyClosure_of_twoVector
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (P : VonNeumannAlgebra H)
    (kaplansky : TwoVectorKaplanskyInput σ P) : ScalarKaplanskyClosure σ P := by
  intro V d hd hV
  apply (scalarCommutatorNorm_le_iff P V hd).mpr
  intro b hb
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hd (norm_nonneg b))
  intro x
  apply le_of_forall_pos_le_add
  intro η hη
  let K := ‖V‖ + 1 + d * ‖x‖
  have hK : 0 < K := by dsimp [K]; positivity
  let ε := η / K
  have hε : 0 < ε := div_pos hη hK
  obtain ⟨a, ha, hx, hVx⟩ := kaplansky b hb x (V x) ε hε
  have herr : ‖commutator V b x - commutator V (σ a) x‖ ≤ ‖V‖ * ε + ε := by
    have heq : commutator V b x - commutator V (σ a) x =
        V (b x - σ a x) - (b (V x) - σ a (V x)) := by
      simp only [commutator, sub_apply, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖V (b x - σ a x)‖ + ‖b (V x) - σ a (V x)‖ := norm_sub_le _ _
      _ ≤ ‖V‖ * ‖b x - σ a x‖ + ‖b (V x) - σ a (V x)‖ :=
        add_le_add (V.le_opNorm _) le_rfl
      _ ≤ ‖V‖ * ε + ε := by
        rw [norm_sub_rev (b x), norm_sub_rev (b (V x))]
        exact add_le_add (mul_le_mul_of_nonneg_left hx (norm_nonneg V)) hVx
  have hmain : ‖commutator V (σ a) x‖ ≤ d * (‖b‖ + ε) * ‖x‖ := by
    calc
      _ ≤ ‖commutator V (σ a)‖ * ‖x‖ := (commutator V (σ a)).le_opNorm x
      _ ≤ (d * ‖a‖) * ‖x‖ := mul_le_mul_of_nonneg_right (hV a) (norm_nonneg x)
      _ ≤ d * (‖b‖ + ε) * ‖x‖ := by gcongr
  calc
    ‖commutator V b x‖ ≤ ‖commutator V (σ a) x‖ +
        ‖commutator V b x - commutator V (σ a) x‖ := by
      simpa only [add_sub_cancel] using norm_add_le
        (commutator V (σ a) x) (commutator V b x - commutator V (σ a) x)
    _ ≤ d * (‖b‖ + ε) * ‖x‖ + (‖V‖ * ε + ε) := add_le_add hmain herr
    _ = d * ‖b‖ * ‖x‖ + η := by
      have hcancel : ε * K = η := div_mul_cancel₀ η (ne_of_gt hK)
      dsimp [K] at hcancel
      nlinarith

end KadisonSimilarity

end

end OAI
