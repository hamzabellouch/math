import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace OAI

namespace SharpPlanar

section Neumann
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


theorem neumann_exists_unique (T : E →L[ℝ] E) (hT : ‖T‖ < 1) (r : E) :
    ∃! x : E, x - T x = r := by
  have hb : Function.Bijective (1 - T : E →L[ℝ] E) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_of_norm_lt_one hT)
  obtain ⟨x, hx⟩ := hb.surjective r
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply hb.injective
  exact hy.trans hx.symm


omit [CompleteSpace E] in
theorem neumann_norm_bound (T : E →L[ℝ] E) {a : ℝ}
    (ha : a < 1) (hT : ‖T‖ ≤ a) {x r : E} (hx : x - T x = r) :
    ‖x‖ ≤ ‖r‖ / (1 - a) := by
  have heq : x = r + T x := by rw [← hx]; abel
  have hi : ‖x‖ ≤ ‖r‖ + a * ‖x‖ := calc
    ‖x‖ = ‖r + T x‖ := congrArg norm heq
    _ ≤ ‖r‖ + ‖T x‖ := norm_add_le _ _
    _ ≤ ‖r‖ + ‖T‖ * ‖x‖ := add_le_add le_rfl (T.le_opNorm x)
    _ ≤ ‖r‖ + a * ‖x‖ := by gcongr
  apply (le_div_iff₀ (by linarith : 0 < 1-a)).mpr
  nlinarith
end Neumann

section Schur
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


theorem schur_exists_unique
    (A V : E →L[ℝ] E) (U : F →L[ℝ] E) (L : E →L[ℝ] F) (D : F →L[ℝ] F)
    (hAV : A * V = 1) (hVA : V * A = 1)
    (hsmall : ‖D + L.comp (V.comp U)‖ < 1) (rE : E) (rF : F) :
    ∃! xy : E × F, A xy.1 - U xy.2 = rE ∧ xy.2 - L xy.1 - D xy.2 = rF := by
  let T : F →L[ℝ] F := D + L.comp (V.comp U)
  obtain ⟨y, hy, huy⟩ := neumann_exists_unique T hsmall (rF + L (V rE))
  have hAV' (x : E) : A (V x) = x := by
    simpa using congrArg (fun f : E →L[ℝ] E => f x) hAV
  have hVA' (x : E) : V (A x) = x := by
    simpa using congrArg (fun f : E →L[ℝ] E => f x) hVA
  refine ⟨(V (rE + U y), y), ⟨?_, ?_⟩, ?_⟩
  · simp [hAV']
  · dsimp [T] at hy
    simp only [add_apply, ContinuousLinearMap.comp_apply] at hy
    simp only [map_add]
    calc
      _ = (y - (D y + L (V (U y)))) - L (V rE) := by abel
      _ = rF := by rw [hy]; abel
  · rintro ⟨x', y'⟩ ⟨hx', hy'⟩
    have hxv : x' = V (rE + U y') := by
      rw [← hx', sub_add_cancel, hVA']
    have hyv : y' = y := by
      apply huy
      dsimp [T]
      simp only [add_apply, ContinuousLinearMap.comp_apply]
      rw [hxv, map_add, map_add] at hy'
      calc
        _ = (y' - (L (V rE) + L (V (U y'))) - D y') + L (V rE) := by abel
        _ = rF + L (V rE) := by rw [hy']
    exact Prod.ext (by simpa [hyv] using hxv) hyv


omit [CompleteSpace F] in
theorem finite_schur_small
    (V : E →L[ℝ] E) (U : F →L[ℝ] E) (L : E →L[ℝ] F) (D : F →L[ℝ] F)
    (hD : ‖D‖ ≤ 28/100) (hL : ‖L‖ ≤ 11/100) (hVU : ‖V.comp U‖ ≤ 37/10) :
    ‖D + L.comp (V.comp U)‖ < 1 := by
  calc
    ‖D + L.comp (V.comp U)‖ ≤ ‖D‖ + ‖L.comp (V.comp U)‖ := norm_add_le _ _
    _ ≤ ‖D‖ + ‖L‖ * ‖V.comp U‖ := add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le L (V.comp U))
    _ ≤ 28/100 + (11/100) * (37/10) := by gcongr
    _ < 1 := by norm_num


omit [CompleteSpace F] in
theorem finite_schur_bound
    (V : E →L[ℝ] E) (U : F →L[ℝ] E) (L : E →L[ℝ] F) (D : F →L[ℝ] F)
    (hV : ‖V‖ ≤ 32) (hD : ‖D‖ ≤ 28/100) (hL : ‖L‖ ≤ 11/100)
    (hVU : ‖V.comp U‖ ≤ 37/10)
    {x rE : E} {y rF : F} (hx : x = V (rE + U y))
    (hy : y - L x - D y = rF) :
    ‖x‖ + ‖y‖ ≤ 90 * (‖rE‖ + ‖rF‖) := by
  have hxnorm : ‖x‖ ≤ 32 * ‖rE‖ + (37/10) * ‖y‖ := calc
    ‖x‖ = ‖V rE + (V.comp U) y‖ := by rw [hx]; simp
    _ ≤ ‖V rE‖ + ‖(V.comp U) y‖ := norm_add_le _ _
    _ ≤ ‖V‖ * ‖rE‖ + ‖V.comp U‖ * ‖y‖ := add_le_add (V.le_opNorm _) ((V.comp U).le_opNorm _)
    _ ≤ 32 * ‖rE‖ + (37/10) * ‖y‖ := by gcongr
  have hyrepr : y = rF + L x + D y := by rw [← hy]; abel
  have hynorm : ‖y‖ ≤ ‖rF‖ + (11/100) * ‖x‖ + (28/100) * ‖y‖ := calc
    ‖y‖ = ‖rF + L x + D y‖ := congrArg norm hyrepr
    _ ≤ ‖rF‖ + ‖L x‖ + ‖D y‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖rF‖ + ‖L‖ * ‖x‖ + ‖D‖ * ‖y‖ := by
      gcongr
      exacts [L.le_opNorm _, D.le_opNorm _]
    _ ≤ ‖rF‖ + (11/100) * ‖x‖ + (28/100) * ‖y‖ := by gcongr
  nlinarith [norm_nonneg rE, norm_nonneg rF]


omit [CompleteSpace F] in
theorem tail_schur_small
    (V : E →L[ℝ] E) (U : F →L[ℝ] E) (L : E →L[ℝ] F) (D : F →L[ℝ] F)
    (hV : ‖V‖ ≤ 90) (hU : ‖U‖ ≤ 28)
    (hL : ‖L‖ ≤ 1/2000000000) (hD : ‖D‖ ≤ 1/2000000000) :
    ‖D + L.comp (V.comp U)‖ < 1 := by
  calc
    ‖D + L.comp (V.comp U)‖ ≤ ‖D‖ + ‖L.comp (V.comp U)‖ := norm_add_le _ _
    _ ≤ ‖D‖ + ‖L‖ * ‖V.comp U‖ := add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le L (V.comp U))
    _ ≤ ‖D‖ + ‖L‖ * (‖V‖ * ‖U‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le V U
    _ ≤ 1/2000000000 + (1/2000000000) * (90 * 28) := by gcongr
    _ < 1 := by norm_num


omit [CompleteSpace F] in
theorem tail_schur_bound
    (V : E →L[ℝ] E) (U : F →L[ℝ] E) (L : E →L[ℝ] F) (D : F →L[ℝ] F)
    (hV : ‖V‖ ≤ 90) (hU : ‖U‖ ≤ 28)
    (hL : ‖L‖ ≤ 1/2000000000) (hD : ‖D‖ ≤ 1/2000000000)
    {x rE : E} {y rF : F} (hx : x = V (rE + U y))
    (hy : y - L x - D y = rF) :
    ‖x‖ + ‖y‖ ≤ 91 * ‖rE‖ + 2540 * ‖rF‖ := by
  have hxnorm : ‖x‖ ≤ 90 * ‖rE‖ + 2520 * ‖y‖ := calc
    ‖x‖ = ‖V rE + V (U y)‖ := by rw [hx]; simp
    _ ≤ ‖V rE‖ + ‖V (U y)‖ := norm_add_le _ _
    _ ≤ ‖V‖ * ‖rE‖ + ‖V‖ * (‖U‖ * ‖y‖) := by
      gcongr
      · exact V.le_opNorm _
      · exact (V.le_opNorm _).trans (mul_le_mul_of_nonneg_left (U.le_opNorm _) (norm_nonneg _))
    _ ≤ 90 * ‖rE‖ + 2520 * ‖y‖ := by
      calc
        _ ≤ 90 * ‖rE‖ + 90 * (28 * ‖y‖) := by gcongr
        _ = _ := by ring
  have hyrepr : y = rF + L x + D y := by rw [← hy]; abel
  have hynorm : ‖y‖ ≤ ‖rF‖ + (1/2000000000) * ‖x‖ + (1/2000000000) * ‖y‖ := calc
    ‖y‖ = ‖rF + L x + D y‖ := congrArg norm hyrepr
    _ ≤ ‖rF‖ + ‖L x‖ + ‖D y‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖rF‖ + ‖L‖ * ‖x‖ + ‖D‖ * ‖y‖ := by
      gcongr
      exacts [L.le_opNorm _, D.le_opNorm _]
    _ ≤ ‖rF‖ + (1/2000000000) * ‖x‖ + (1/2000000000) * ‖y‖ := by gcongr
  nlinarith [norm_nonneg rE, norm_nonneg rF]
end Schur
end SharpPlanar

end OAI
