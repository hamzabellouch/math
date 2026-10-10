import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailTwist
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionGeometry
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedActualRange

namespace OAI

/-! The original enveloped stopped height tail, including every window
and the entire product Mellin line, has arbitrary logarithmic saving. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem distinguishedStoppedEnvelopeTail_bound (i : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ ρ ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100) (n : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H T : ℝ) (h : ℕ) (early : Bool)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ) (j k : ℕ),
      (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X → 1 ≤ q.2.1 →
      ‖∑ s ∈ Finset.range (heightWindowCount H T),
        scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨r,hr⟩ := exists_nat_gt (1/ξ)
  have hξr : 1 < ξ*r := by
    have he := (div_lt_iff₀ hξ).mp hr
    simpa only [mul_comm] using he
  let M : ℝ := ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨K,Ct,hK,hbound⟩ := stopped_twisted_cutoff_tail hpnt hMV hC hHuxley hM n r 0
  let c := zeroLineMellinMass primeProductEnvelope
  have hc : 0 ≤ c := by
    dsimp [c,zeroLineMellinMass]
    exact mul_nonneg (by positivity) (integral_nonneg (fun _ => _root_.norm_nonneg _))
  refine ⟨(K*(1+c))*(16:ℝ)^(5/6:ℝ)*(20/7:ℝ)^n,Ct,by positivity,?_⟩
  filter_upwards [eventually_stopped_actual_range 0,
    eventually_scaleFirstTailStoppedDyad_geometry hρ hρ₂ hε hsmall hgap,
    eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 7/20)).eventually_ge_atTop
      ((65536:ℝ)^2)] with X hrange hgeom hX hlarge
  intro H T h early d q j k hT hH hHX hk
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
  by_cases hz : (∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k) = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨s,_hs,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨hBlo,hBhi,_hBX,hprodlo,hprodhi,_hq⟩ :=
    hgeom i 0 H (T*(3/2:ℝ)^s) h early d q j k hk hs
  let A := stoppedNormDyadLength j/2
  let B := stoppedNormDyadLength k
  have hAp : 0 < A := by dsimp [A]; positivity [stoppedNormDyadLength_pos j]
  have hBp : 0 < B := stoppedNormDyadLength_pos k
  have hB1 : 1 ≤ B :=
    (Real.one_le_rpow hX.le (by norm_num : (0:ℝ) ≤ 7/20)).trans hBlo
  have hBX : B ≤ X := hBhi.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (39/100:ℝ) ≤ 1))
  have hBlarge : (65536:ℝ)^2 ≤ B := hlarge.trans hBlo
  obtain ⟨hAlow,hAhigh⟩ := hrange A B hprodlo hprodhi hBlo hBhi
  have hA2 : A ≤ B^2 := by simpa only [pow_zero,div_one] using hAhigh
  have hA3 : A ≤ B^3 := hA2.trans (pow_le_pow_right₀ hB1 (by omega))
  have hXB3 : X ≤ B^3 := by
    have he := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le (7/20:ℝ)) hBlo 3
    rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le] at he
    norm_num only [show (7/20:ℝ)*(3:ℕ) = 21/20 by norm_num] at he
    apply le_trans _ he
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (1:ℝ) ≤ 21/20)
  have hsize : B < (X^ξ)^r := by
    calc
      B ≤ X := hBX
      _ < X^(ξ*r) := by
        simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hX hξr
      _ = (X^ξ)^r := by rw [←Real.rpow_mul_natCast hXp.le]
  have hT' : (1+Real.log B)^Ct ≤ T := by
    apply le_trans _ hT
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hB1])
      (by linarith [Real.log_le_log hBp hBX]) Ct
  have hP (a : Eisenstein) (ha : a ∈ stoppedNormDyad (distinguishedStoppedSide X) j) :
      primary a ∧ Squarefree a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2 := by
    have hp := distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1
    have hn := stoppedNormDyad_outer_bounds ha hp.1
    refine ⟨hp.1,hp.2.1,(one_le_div hAp).mpr hn.1,?_⟩
    apply (div_le_iff₀ hAp).mpr
    dsimp [A]
    nlinarith [hn.2]
  have hQ (b : Eisenstein) (hb : b ∈ stoppedNormDyad (distinguishedStoppedSide X) k) :
      primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B := by
    have hp := distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1
    have hn := stoppedNormDyad_outer_bounds hb hp.1
    exact ⟨hp.1,hp.2.1,hn.1,hn.2⟩
  have hb := hbound (distinguishedStoppedRoughSupport i ξ X d)
    (centralPrimaryFactors X) (centralPrimaryFactors X) (centralPrimaryFactors X)
    (stoppedNormDyad (distinguishedStoppedSide X) j)
    (stoppedNormDyad (distinguishedStoppedSide X) k)
    primeDetectorCutoff (X^ξ) B A X T H (distinguishedScaleCoefficient i ξ X d)
    (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.1 h
      (if early then X^(9/25:ℝ) else X^(38/100:ℝ)) (X^(9/25:ℝ)) early)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      q.1 q.2.2)
    (fun a ha => (distinguishedStoppedRoughSupport_spec i hX.le hξz d ha).1)
    (fun a ha => (mem_primaryElementBall.mp ha).1)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (Real.one_le_rpow hX.le hξ.le)
    (fun a ha => (distinguishedStoppedRoughSupport_spec i hX.le hξz d ha).2)
    (fun a _ => distinguishedScaleCoefficient_norm_le i ξ X d a)
    hsize hBlarge hAlow (by simpa only [mul_zero,pow_zero,mul_one] using hA2)
    hA3 hXp hT' hH (hHX.trans hXB3) hP hQ
  have hb' : ∀ u : ℝ, ‖cutoffBilinearTail
      (stoppedNormDyad (distinguishedStoppedSide X) j)
      (stoppedNormDyad (distinguishedStoppedSide X) k)
      (fun a => distinguishedStoppedAlpha ρ ξ X q a*normTwist u a)
      (fun b => distinguishedStoppedBeta i ρ ξ X h early d q b*normTwist u b) H T X‖ ≤
      K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^n := by
    rw [distinguishedStoppedBeta_rough_support]
    exact hb
  rw [scaleFirstTailStoppedDyads_envelope i ρ ξ H T hXp h early d q j k]
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  apply (envelopeCutoffBilinearTail_bound _ _ _ _
    (fun a ha => (hP a ha).1) (fun b hb => (hQ b hb).1)
    primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth H T hXp (by positivity) hb').trans
  have hlog : 1+Real.log X ≤ (20/7:ℝ)*(1+Real.log B) := by
    have he := Real.log_le_log (Real.rpow_pos_of_pos hXp (7/20:ℝ)) hBlo
    rw [Real.log_rpow hXp] at he
    nlinarith
  have hden : (1+Real.log X)^n ≤ (20/7:ℝ)^n*(1+Real.log B)^n := by
    simpa only [mul_pow] using pow_le_pow_left₀ hLX.le hlog n
  have hscale : A^(5/6:ℝ)*B^(5/6:ℝ) ≤ (16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ) := by
    rw [←Real.mul_rpow hAp.le hBp.le,←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hXp.le]
    exact Real.rpow_le_rpow (mul_nonneg hAp.le hBp.le) hprodhi (by norm_num)
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hLB n) (pow_pos hLX n)).mpr
  calc
    c*(K*A^(5/6:ℝ)*B^(5/6:ℝ))*(1+Real.log X)^n ≤
        (1+c)*(K*((16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ)))*
          ((20/7:ℝ)^n*(1+Real.log B)^n) := by
      apply mul_le_mul _ hden (pow_nonneg hLX.le n) (by positivity)
      calc
        c*(K*A^(5/6:ℝ)*B^(5/6:ℝ)) ≤ (1+c)*(K*A^(5/6:ℝ)*B^(5/6:ℝ)) := by
          apply mul_le_mul_of_nonneg_right (by linarith)
          positivity
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale hK.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
