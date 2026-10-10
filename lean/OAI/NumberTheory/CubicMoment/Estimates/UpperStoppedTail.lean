import OAI.NumberTheory.CubicMoment.Estimates.UniformHighStoppedTail
import OAI.NumberTheory.CubicMoment.Estimates.UpperTailGeometry
import OAI.NumberTheory.CubicMoment.Estimates.UpperStoppedRange
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionEnvelope

namespace OAI

/-! The literal upper stopped dyad has arbitrary logarithmic saving.
Its stopping exponent is fixed before arities and logarithmic losses. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma upperTailStoppedDyads_envelope (i : ℕ) (κ ρ ξ H T : ℝ)
    {X : ℝ} (hX : 0 < X)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (q : ℕ × ℕ × ℕ) (j k : ℕ) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      upperTailStoppedDyad i 0 κ ρ ξ H (T*(3/2:ℝ)^s) X d q j k) =
      envelopeCutoffBilinearTail (stoppedNormDyad (distinguishedStoppedSide X) j)
        (stoppedNormDyad (distinguishedStoppedSide X) k)
        (distinguishedStoppedAlpha ρ ξ X q) (upperStoppedBeta i κ ρ ξ X d q)
        primeProductEnvelope H T X := by
  unfold envelopeCutoffBilinearTail
  apply Finset.sum_congr rfl
  intro s _
  unfold upperTailStoppedDyad
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hpa := (distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1).1
  have hpb := (distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1).1
  rw [scaleFirstTailKernel_indicator 0 H _ hX (primary_mul hpa hpb)]
  simp only [scaleFirstTailKernel,theta_zero,one_mul]
  ring

theorem upperStoppedTail_bound (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1/12 ∧ ∀ (ρ ξ ε : ℝ),
      1 < ρ → ρ ≤ 2 → 0 ≤ ε → ρ ≤ (2:ℝ)^ε → ξ+ε < κ/2 →
      ∀ i n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
        ∀ (H T : ℝ)
          (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
          (q : ℕ × ℕ × ℕ) (j k : ℕ),
        X^(1/100:ℝ) ≤ T → 1 ≤ H → H ≤ X^(1/2:ℝ) → 1 ≤ q.2.1 →
        ‖∑ s ∈ Finset.range (heightWindowCount H T),
          upperTailStoppedDyad i 0 κ ρ ξ H (T*(3/2:ℝ)^s) X d q j k‖ ≤
          K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨γ,hγ,huniform⟩ := high_stopped_envelope_tail_uniform hpnt hMV hC hHuxley
  let κ := γ/(100*(3+γ))
  have hden : 0 < 100*(3+γ) := by positivity
  have hκ : 0 < κ := div_pos hγ hden
  have hκsmall : κ < 1/12 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hκeq : κ*(3+γ) = γ/100 := by dsimp [κ]; field_simp
  have hmargin : 1 < (1/3-κ)*(3+γ) := by nlinarith
  refine ⟨κ,hκ,hκsmall,?_⟩
  intro ρ ξ ε hρ hρ₂ hε hsmall hgap i n
  let M : ℝ := ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨K,Z₀,hK,hbound⟩ := huniform M hM n primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth
  refine ⟨K*(16:ℝ)^(5/6:ℝ)*4^n,by positivity,?_⟩
  filter_upwards [eventually_upperTailStoppedDyad_geometry hκ hρ hρ₂ hε hsmall hgap,
    eventually_upper_stopped_analytic_range hκ hκsmall hmargin,
    eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0 < 1/3-κ by linarith)).eventually_ge_atTop Z₀]
    with X hgeom hrange hX hlarge
  intro H T d q j k hT hH hHX hk
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
  by_cases hz : (∑ s ∈ Finset.range (heightWindowCount H T),
      upperTailStoppedDyad i 0 κ ρ ξ H (T*(3/2:ℝ)^s) X d q j k) = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨s,_hs,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨hBlo,hBhi,hprodlo,hprodhi⟩ := hgeom i 0 H (T*(3/2:ℝ)^s) d q j k hk hs
  let A := stoppedNormDyadLength j/2
  let B := stoppedNormDyadLength k
  have hAp : 0 < A := by dsimp [A]; positivity [stoppedNormDyadLength_pos j]
  have hBp : 0 < B := stoppedNormDyadLength_pos k
  have hB1 : 1 ≤ B :=
    (Real.one_le_rpow hX.le (show 0 ≤ 1/3-κ by linarith)).trans hBlo
  obtain ⟨hAlow,hAhigh,hA3,hBT,hHB3,hlog⟩ := hrange A B hprodlo hprodhi hBlo hBhi
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
  have hb := hbound (centralPrimaryFactors X) (centralPrimaryFactors X)
    (centralPrimaryFactors X) (centralPrimaryFactors X)
    (stoppedNormDyad (distinguishedStoppedSide X) j)
    (stoppedNormDyad (distinguishedStoppedSide X) k)
    primeDetectorCutoff (X^ξ) B A X T H (distinguishedScaleCoefficient i ξ X d)
    (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.1
      0 (X^(1/3-κ)) (X^(1/3-κ)) true)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.2)
    (fun _ hm => (mem_primaryElementBall.mp hm).1)
    (fun _ hm => (mem_primaryElementBall.mp hm).1)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (fun a _ => distinguishedScaleCoefficient_norm i ξ X d a)
    (hlarge.trans hBlo) hAlow hAhigh hA3 hXp (hBT.trans hT) hH (hHX.trans hHB3) hP hQ
  rw [upperTailStoppedDyads_envelope i κ ρ ξ H T hXp d q j k]
  apply hb.trans
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hdenom : (1+Real.log X)^n ≤ (4:ℝ)^n*(1+Real.log B)^n := by
    have hh : 1+Real.log X ≤ 4*(1+Real.log B) := by linarith
    simpa only [mul_pow] using pow_le_pow_left₀ hLX.le hh n
  have hscale : A^(5/6:ℝ)*B^(5/6:ℝ) ≤ (16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ) := by
    rw [←Real.mul_rpow hAp.le hBp.le,←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hXp.le]
    exact Real.rpow_le_rpow (mul_nonneg hAp.le hBp.le) hprodhi (by norm_num)
  apply (div_le_div_iff₀ (pow_pos hLB n) (pow_pos hLX n)).mpr
  calc
    (K*A^(5/6:ℝ)*B^(5/6:ℝ))*(1+Real.log X)^n ≤
        (K*((16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ)))*((4:ℝ)^n*(1+Real.log B)^n) := by
      apply mul_le_mul _ hdenom (pow_nonneg hLX.le n) (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale hK.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
