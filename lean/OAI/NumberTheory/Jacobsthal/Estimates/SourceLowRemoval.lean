import OAI.NumberTheory.Jacobsthal.Analysis.CorrectedCompactTransfer

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceLowRemoval

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures TransitionKernels FinitePathGeometry DerivativeWeights
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry
open ContinuousCompactHighError OriginalHarmonicOccupation AdmittedHarmonicPaths LowStateHorizon

noncomputable def scaleConstant : ℝ := (23/10:ℝ)^2/phiEven (23/10)

theorem scaleConstant_pos : 0 < scaleConstant := by
  unfold scaleConstant
  exact div_pos (by norm_num) (phiEven_pos (by norm_num))

theorem source_scale_upper {v B : ℝ} (hB : 0 < B) (s : EvenState) (hs : s.1 ≤ 23/10)
    (hcut : currentExponent v (.inl s,0) = B) :
    (Real.exp v)^2/stateWeight (.inl s) ≤ scaleConstant*B^2 ∧ gapValue v (.inl s,0) ≤ (23/10:ℝ)*B := by
  have hs0 : 0 < s.1 := by linarith [s.2]
  have he : Real.exp v = B*s.1 := by
    change Real.exp (v-0)/s.1 = B at hcut
    rw [sub_zero] at hcut
    exact (div_eq_iff hs0.ne').mp hcut
  have hupper : Real.exp v ≤ (23/10:ℝ)*B := by rw [he]; nlinarith
  have hsq : (Real.exp v)^2 ≤ (23/10:ℝ)^2*B^2 := by nlinarith [Real.exp_pos v]
  have hφ : 0 < phiEven s.1 := phiEven_pos (by linarith [s.2])
  have hφend : 0 < phiEven (23/10) := phiEven_pos (by norm_num)
  have hmono : phiEven (23/10) ≤ phiEven s.1 :=
    TwoStepDensityBounds.weight_antitone (i:=.even) s.2 (by norm_num [Valid]) hs
  have hinv := one_div_le_one_div_of_le hφend hmono
  refine ⟨?_,?_⟩
  · change (Real.exp v)^2/phiEven s.1 ≤ _
    calc
      _ = (Real.exp v)^2*(1/phiEven s.1) := by ring
      _ ≤ ((23/10:ℝ)^2*B^2)*(1/phiEven (23/10)) := mul_le_mul hsq hinv (by positivity) (by positivity)
      _ = _ := by unfold scaleConstant; ring
  · simpa only [gapValue,sub_zero] using hupper

theorem source_low_removal {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {K : ℝ} (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → H i (r,s)=0) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ B : ℝ in atTop,∀ v ell : ℝ,∀ s : EvenState,
      (199/100:ℝ) ≤ s.1 → s.1 ≤ 23/10 → 1 ≤ ell → ell ≤ B → currentExponent v (.inl s,0)=B →
      |(∫ z,inverseReward v H z ∂occupation (admittedTilted v ell) (.inl s,0))-
        (∫ z,inverseReward v H z ∂occupation (lowKernel costKernel v ell ((Real.log B)^2)) (.inl s,0))| ≤ C/B := by
  obtain ⟨A,hA,herror⟩ := compact_high_error_bound hH hcompact hsupport
  refine ⟨scaleConstant*A,mul_nonneg scaleConstant_pos.le hA,?_⟩
  filter_upwards [AdmittedHighRemoval.low_gap_high_removal K 3,
    eventually_ge_atTop (Real.exp 2)] with B hrem hBexp
  intro v ell s _hsL hsU hell hellB hcut
  have hB : 0 < B := (Real.exp_pos 2).trans_le hBexp
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hS : 0 < (Real.log B)^2 := by nlinarith
  have hsS : stateRatio (.inl s) ≤ (Real.log B)^2 := by change s.1 ≤ _; nlinarith
  have hscale := source_scale_upper hB s hsU hcut
  have herr := herror v ell ((Real.log B)^2) B hell hS hB (.inl s) hsS hscale.2
  have hhigh := hrem v ell (.inl s,0) hell hellB hcut
  have hsourceScale : ENNReal.ofReal ((Real.exp v)^2/stateWeight (.inl s)) ≤
      ENNReal.ofReal (scaleConstant*B^2) := ENNReal.ofReal_le_ofReal hscale.1
  have hscaled := mul_le_mul hsourceScale (le_refl (ENNReal.ofReal A)) zero_le zero_le
  have hbound := herr.trans (mul_le_mul hscaled hhigh zero_le zero_le)
  have hid : ENNReal.ofReal (scaleConstant*B^2)*ENNReal.ofReal A*ENNReal.ofReal (B^(-(3:ℝ))) =
      ENNReal.ofReal ((scaleConstant*A)/B) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg scaleConstant_pos.le (sq_nonneg B)),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg scaleConstant_pos.le (sq_nonneg B)) hA)]
    congr 1
    rw [Real.rpow_neg hB.le,Real.rpow_ofNat]
    field_simp
  rw [hid] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg (mul_nonneg scaleConstant_pos.le hA) hB.le)).mp hbound

end NumberTheoryLean.SourceLowRemoval

end

end Erdos970

end OAI
