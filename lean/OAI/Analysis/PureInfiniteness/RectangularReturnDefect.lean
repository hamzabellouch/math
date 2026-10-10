import OAI.Analysis.PureInfiniteness.RectangularAlgebra

namespace OAI

/-! A multiplicative-defect bound for the concrete finite return map G* X G.
Only a contractive column and square roots in a finite matrix algebra are used. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype J]
local instance : Module ℝ (CStarMatrix J J A) := Module.complexToReal _

def columnReturn (G : CStarMatrix J (Fin 1) A) (X : CStarMatrix J J A) :
    CStarMatrix (Fin 1) (Fin 1) A := G.conjTranspose * X * G

lemma columnReturn_multiplicative_defect (G : CStarMatrix J (Fin 1) A) (hG : ‖G‖ ≤ 1)
    (X Y : CStarMatrix J J A) (hX : X.conjTranspose = X) :
    ‖columnReturn G (X * Y) - columnReturn G X * columnReturn G Y‖ ≤
      Real.sqrt ‖columnReturn G (X * X) - columnReturn G X * columnReturn G X‖ * ‖Y‖ := by
  classical
  let P : CStarMatrix J J A := G * G.conjTranspose
  have hP : 0 ≤ P := by
    simpa only [P, rectangular_conjTranspose_conjTranspose] using
      rectangular_initial_nonneg G.conjTranspose
  have hPn : ‖P‖ ≤ 1 := by
    change ‖G * G.conjTranspose‖ ≤ 1
    rw [rectangular_norm_range]
    nlinarith [norm_nonneg G]
  have hP1 : P ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg P hP).mp hPn
  let K : CStarMatrix J J A := CFC.sqrt (1 - P)
  have hKstar : K.conjTranspose = K := (CFC.sqrt_nonneg (1 - P)).star_eq
  have hKsq : K * K = 1 - P := CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hP1)
  have hKn : ‖K‖ ≤ 1 := by
    have hd : ‖1 - P‖ ≤ 1 := by
      exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hP1)).mpr
        (sub_le_self _ hP)
    have hk : ‖K‖ ^ 2 = ‖1 - P‖ := by
      calc
        _ = ‖K.conjTranspose * K‖ := (rectangular_norm_initial K).symm
        _ = ‖K * K‖ := by rw [hKstar]
        _ = _ := congrArg norm hKsq
    nlinarith [norm_nonneg K]
  let E : CStarMatrix (Fin 1) J A := G.conjTranspose * X * K
  let F : CStarMatrix J (Fin 1) A := K * (Y * G)
  have hEF : E * F = columnReturn G (X * Y) - columnReturn G X * columnReturn G Y := by
    calc
      _ = G.conjTranspose * X * (K * K) * Y * G := by
        simp only [E, F, rectangular_mul_assoc]
      _ = G.conjTranspose * X * (1 - G * G.conjTranspose) * Y * G := by rw [hKsq]
      _ = _ := by
        simp only [columnReturn, rectangular_mul_sub, rectangular_sub_mul,
          rectangular_mul_one, rectangular_mul_assoc]
  have hEE : E * E.conjTranspose =
      columnReturn G (X * X) - columnReturn G X * columnReturn G X := by
    calc
      _ = G.conjTranspose * X * (K * K) * X * G := by
        simp only [E, rectangular_conjTranspose_mul, hKstar, hX,
          rectangular_conjTranspose_conjTranspose, rectangular_mul_assoc]
      _ = G.conjTranspose * X * (1 - G * G.conjTranspose) * X * G := by rw [hKsq]
      _ = _ := by
        simp only [columnReturn, rectangular_mul_sub, rectangular_sub_mul,
          rectangular_mul_one, rectangular_mul_assoc]
  have hEn : ‖E‖ = Real.sqrt
      ‖columnReturn G (X * X) - columnReturn G X * columnReturn G X‖ := by
    rw [← hEE, rectangular_norm_range, Real.sqrt_sq (norm_nonneg E)]
  have hFn : ‖F‖ ≤ ‖Y‖ := by
    calc
      _ ≤ ‖K‖ * ‖Y * G‖ := rectangular_norm_mul_le _ _
      _ ≤ ‖K‖ * (‖Y‖ * ‖G‖) :=
        mul_le_mul_of_nonneg_left (rectangular_norm_mul_le _ _) (norm_nonneg K)
      _ ≤ 1 * (‖Y‖ * 1) := by gcongr
      _ = _ := by ring
  rw [← hEF]
  exact (rectangular_norm_mul_le E F).trans (by rw [hEn]; gcongr)

end WeakPureInfiniteness

end

end OAI
