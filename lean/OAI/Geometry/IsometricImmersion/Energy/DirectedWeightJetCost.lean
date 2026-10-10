import OAI.Geometry.IsometricImmersion.Energy.DirectedFluxCost

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedWeightJetBudget (D M lambda : ℝ) : ℝ := 16 + 3*D + 2*D*(M+lambda)

theorem directedWeightJetBudget_bounds {D M lambda : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlambda : 0 ≤ lambda) :
    0 ≤ directedWeightJetBudget D M lambda ∧
    D ≤ directedWeightJetBudget D M lambda ∧
    2*D ≤ directedWeightJetBudget D M lambda ∧
    D*M ≤ directedWeightJetBudget D M lambda ∧
    8+D*(M+lambda) ≤ directedWeightJetBudget D M lambda ∧
    D+2*D*M ≤ directedWeightJetBudget D M lambda ∧
    16+2*D*(M+lambda) ≤ directedWeightJetBudget D M lambda := by
  have hDM := mul_nonneg hD hM
  have hDl := mul_nonneg hD hlambda
  unfold directedWeightJetBudget
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem directedWeight_value_and_partials_bound
    {I : Coord → ℝ} {p : Coord} {b lambda D S MI M : ℝ}
    (hId : DifferentiableAt ℝ I p) (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M) :
    |directedWeight b lambda I p| ≤ D*(Real.exp (lambda*S+MI)*edgeDistance b p^7) ∧
    |coordPartial 0 (directedWeight b lambda I) p| ≤
      (D*M)*(Real.exp (lambda*S+MI)*edgeDistance b p^7) ∧
    |coordPartial 1 (directedWeight b lambda I) p| ≤
      (8+D*(M+lambda))*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
  have hD : 0 ≤ D := hd.trans hdD
  have hW : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have hE : 0 ≤ Real.exp (lambda*S+MI)*edgeDistance b p^7 := by positivity
  have hw : |directedWeight b lambda I p| ≤ D*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
    rw [abs_of_nonneg hW]
    convert directedWeight_le_seven hlambda hd hdD hs hIv using 1
    ring
  have hphase : weightPhase lambda I p ≤ lambda*S+MI := by
    have hs' : -p 1 ≤ S := by linarith [(abs_le.mp hs).1]
    have hm := mul_le_mul_of_nonneg_left hs' hlambda
    unfold weightPhase
    linarith [(abs_le.mp hIv).2]
  refine ⟨hw, ?_, ?_⟩
  · rw [directedWeight_partial_t b lambda hId, abs_mul]
    have hh := mul_le_mul hw (hIi 0) (abs_nonneg _) (mul_nonneg hD hE)
    convert hh using 1
    ring
  · rw [directedWeight_partial_s b lambda hId]
    have hIs : |coordPartial 1 I p - lambda| ≤ M+lambda := by
      calc
        _ ≤ |coordPartial 1 I p| + |lambda| := abs_sub _ _
        _ ≤ M+lambda := by rw [abs_of_nonneg hlambda]; exact add_le_add (hIi 1) le_rfl
    have hlead : |-8*edgeDistance b p^7*Real.exp (weightPhase lambda I p)| ≤
        8*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
      have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase)
        (show 0 ≤ 8*edgeDistance b p^7 by positivity)
      calc
        _ = 8*edgeDistance b p^7*Real.exp (weightPhase lambda I p) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hd 7),
            abs_of_pos (Real.exp_pos _)]
          norm_num
        _ ≤ 8*edgeDistance b p^7*Real.exp (lambda*S+MI) := hh
        _ = _ := by ring
    have hrest : |directedWeight b lambda I p*(coordPartial 1 I p-lambda)| ≤
        (D*(M+lambda))*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
      rw [abs_mul]
      calc
        _ ≤ (D*(Real.exp (lambda*S+MI)*edgeDistance b p^7))*(M+lambda) :=
          (mul_le_mul_of_nonneg_left hIs (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_right hw (add_nonneg hM hlambda))
        _ = _ := by ring
    exact (abs_add_le _ _).trans (by
      have hh := add_le_add hlead hrest
      convert hh using 1
      ring)

theorem directedMultiplier_firstJet_abs_le_seven
    {I : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M : ℝ}
    (hId : DifferentiableAt ℝ I p) (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ 2)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M) :
    let V := directedWeightJetBudget D M lambda * Real.exp (lambda*S+MI)*edgeDistance b p^7
    |directedM b lambda I p| ≤ V ∧ |directedN b lambda epsilon I p| ≤ V ∧
      (∀ i : Fin 2, |coordPartial i (directedM b lambda I) p| ≤ V) ∧
      (∀ i : Fin 2, |coordPartial i (directedN b lambda epsilon I) p| ≤ V) := by
  let E := Real.exp (lambda*S+MI)*edgeDistance b p^7
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : 0 ≤ D := hd.trans hdD
  have het : |epsilon*p 0| ≤ (2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg heps]
    exact (mul_le_mul_of_nonneg_left ht heps).trans (by linarith)
  have heabs : |epsilon| ≤ 1 := by rwa [abs_of_nonneg heps]
  obtain ⟨hw, hwt, hws⟩ := directedWeight_value_and_partials_bound hId hlambda hM hd hdD hs hIv hIi
  obtain ⟨hN, hND, hN2D, hNDM, hNs, hNt, hNss⟩ := directedWeightJetBudget_bounds hD hM hlambda
  change |directedWeight b lambda I p| ≤ D*E at hw
  change |coordPartial 0 (directedWeight b lambda I) p| ≤ (D*M)*E at hwt
  change |coordPartial 1 (directedWeight b lambda I) p| ≤ (8+D*(M+lambda))*E at hws
  have hlift {a x : ℝ} (hx : |x| ≤ a*E) (ha : a ≤ directedWeightJetBudget D M lambda) :
      |x| ≤ directedWeightJetBudget D M lambda*Real.exp (lambda*S+MI)*edgeDistance b p^7 := by
    have hh := hx.trans (mul_le_mul_of_nonneg_right ha hE)
    convert hh using 1
    dsimp only [E]
    ring
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold directedM
    rw [abs_neg]
    exact hlift hw hND
  · have hh : |directedN b lambda epsilon I p| ≤ (2*D)*E := by
      unfold directedN
      rw [abs_mul]
      convert mul_le_mul het hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) using 1
      ring
    exact hlift hh hN2D
  · intro i
    rw [directedM_partial b lambda i, abs_neg]
    fin_cases i
    · simpa only [Fin.mk_zero] using hlift hwt hNDM
    · simpa only [Fin.mk_one] using hlift hws hNs
  · intro i
    rw [directedN_partial b lambda epsilon hId i]
    fin_cases i
    · simp only [Fin.mk_zero, Fin.isValue, ↓reduceIte, mul_one]
      have hfirst : |epsilon*directedWeight b lambda I p| ≤ D*E := by
        rw [abs_mul]
        have hh := mul_le_mul heabs hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [one_mul] using hh
      have hsecond : |epsilon*p 0*coordPartial 0 (directedWeight b lambda I) p| ≤ (2*D*M)*E := by
        rw [abs_mul]
        convert mul_le_mul het hwt (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) using 1
        ring
      have hh : |epsilon*directedWeight b lambda I p +
          epsilon*p 0*coordPartial 0 (directedWeight b lambda I) p| ≤ (D+2*D*M)*E := by
        exact (abs_add_le _ _).trans (by
          convert add_le_add hfirst hsecond using 1
          ring)
      exact hlift hh hNt
    · simp only [Fin.mk_one, Fin.isValue, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte,
        mul_zero, zero_mul, zero_add]
      have hh : |epsilon*p 0*coordPartial 1 (directedWeight b lambda I) p| ≤
          (16+2*D*(M+lambda))*E := by
        rw [abs_mul]
        convert mul_le_mul het hws (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) using 1
        ring
      exact hlift hh hNss

end SmoothLocal.Weighted

end

end OAI
