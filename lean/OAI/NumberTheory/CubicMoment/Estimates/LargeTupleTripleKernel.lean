import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleTripleTransition
import OAI.NumberTheory.CubicMoment.Estimates.TripleKernelScale

namespace OAI

/-! Integrate the actual exceptional-triple polynomial against the
sharp low-height weight. Its cost is logarithmic in the height cutoff. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem large_tuple_triple_low_kernel {i j : ℕ} (hij : i+j = 3)
    (a : Fin i ⊕ Fin j) (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hc : 0 < c)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (Ct : ℕ) :
    ∃ η K B₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ᶠ X : ℝ in atTop, ∀ (z : largeTupleBoxIndex i j) (H : ℝ),
      z.1.1 = X → 0 < H →
      let B := largeTupleNormScale z.1.2 a
      let A := largeTupleGroupLength (Finset.univ\{a}) z
      X^(1/4:ℝ) ≤ B → A*B ≤ 3*X → B₀ ≤ B → (2*B)^(1/2:ℝ) < B →
      B^(1-η/4) ≤ A → A ≤ B^2 →
      (∀ b : {b : Fin i ⊕ Fin j // b ∉ ({a} : Finset _)}, B^c ≤ largeTupleNormScale z.1.2 b) →
      ‖largeTupleRegroupedKernel i j 0 ξ Ct H X z.1.2 {a}‖ ≤
        K*X^(5/6:ℝ)*(1+Real.log (1+Real.log X))/(1+Real.log X)^(3/2:ℝ) := by
  obtain ⟨η,K₀,B₀,hη,hη1,hK₀,hbound⟩ := large_tuple_triple_transition_smoothed hij a
    hpnt hSW hpub hHuxley hperiod hMV hC hc hGI hGQ (Ct+2)
  let K₁ := K₀*3^(5/6:ℝ)/(1/4:ℝ)^(3/2:ℝ)
  refine ⟨η,8*K₁*((Ct:ℝ)+2),B₀,hη,hη1,by dsimp [K₁]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_triple_height_comparison (Ct+1)] with X hX hlog hheight
  intro z H hz hH
  dsimp only
  intro hBX hAB hB₀ hrough hAlow hAhigh hrest
  have hL : 0 < 1+Real.log X := by linarith
  have hLp : 2 ≤ 1+Real.log X := by linarith
  let V := K₁*X^(5/6:ℝ)/(1+Real.log X)^(3/2:ℝ)
  have hV : 0 ≤ V := by dsimp [V,K₁]; positivity
  have hnorm (t : ℝ) (ht : t ∈ Icc (-(4/3)*(1+Real.log X)^Ct) ((4/3)*(1+Real.log X)^Ct)) :
      ‖largeTupleSmoothedPolynomial 0 ξ z.1.1 z.1.2 {a} t‖ ≤ V := by
    have ht' : |t| ≤ (4/3)*(1+Real.log X)^Ct := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
    have hu : |t| ≤ (1+Real.log (largeTupleNormScale z.1.2 a))^(Ct+2) := by
      apply (ht'.trans _).trans (hheight _ hBX)
      rw [pow_succ]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        ((by norm_num : (4/3:ℝ) ≤ 2).trans hLp) (pow_nonneg hL.le Ct)
    exact (hbound z t hB₀ hrough hAlow hAhigh hu hrest).trans
      (triple_transition_scale hX (zero_le_one.trans (largeTupleGroupLength_one _ z)) hBX hK₀.le hAB)
  rw [largeTupleRegroupedKernel_low_integral 0 ξ X Ct hH]
  have he : (∫ t : ℝ, (lowHeightWeight H ((1+Real.log X)^Ct) t*
      Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*largeTupleSmoothedPolynomial 0 ξ X z.1.2 {a} t) =
      ∫ t : ℝ, lowHeightWeight H ((1+Real.log X)^Ct) t*
        (Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*largeTupleSmoothedPolynomial 0 ξ z.1.1 z.1.2 {a} t) := by
    rw [hz]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [he]
  have hh := lowHeightWeight_integral_log_bound H (pow_pos hL Ct) hV
    (fun t => Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*largeTupleSmoothedPolynomial 0 ξ z.1.1 z.1.2 {a} t) (by
      intro t ht
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
      exact hnorm t ht)
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left (lowHeight_log_power_bound (by linarith) Ct)
    (show 0 ≤ 8*V by positivity)).trans_eq
  dsimp [V]
  ring

end CubicFirstMoment

end

end OAI
