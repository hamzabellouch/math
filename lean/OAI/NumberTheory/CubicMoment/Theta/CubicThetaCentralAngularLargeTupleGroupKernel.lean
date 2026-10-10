import OAI.NumberTheory.CubicMoment.Angular.AngularLargeTupleGroupKernel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularLargeTupleRestrictedSmoothed

namespace OAI

/-! The complete low-height kernel of one fixed group. All Mellin
frequencies have already been restored before this height integration. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)


theorem angular_large_tuple_group_low_kernel_actual {i j : ℕ}
    (s : Finset (Fin i ⊕ Fin j)) (hs : s.Nonempty)
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k Ct : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ᶠ X : ℝ in atTop, ∀ (z : largeTupleBoxIndex i j) (H : ℝ), z.1.1 = X → 0 < H →
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      X^(1/3:ℝ) ≤ B → A*B ≤ 3*X → B₀ ≤ B →
      (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      B^(1-η/16) ≤ A → A ≤ B^2/(1+Real.log B)^G →
      ‖largeTupleRegroupedKernel i j ℓ ξ Ct H X z.1.2 s‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  obtain ⟨η,G,K₀,B₀,hη,hη1,hK₀,hbound⟩ := angular_large_tuple_restricted_smoothed_actual ℓ s hs hSW hℓ hpub
    hHuxley hperiod hMV hC hξ hξz hGI hGQ  hGamma (k+Ct) (Ct+2)
  let K₁ := K₀*3^(5/6:ℝ)/(1/3:ℝ)^(k+Ct)
  refine ⟨η,G,(8/3)*Real.log 2*K₁,B₀,hη,hη1,by dsimp [K₁]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_largeTuple_height_comparison (Ct+1)] with X hX hlog hheight
  intro z H hz hH
  dsimp only
  intro hBX hAB hB₀ hrough hAlow hAhigh
  have hL : 0 < 1+Real.log X := by linarith
  have hLp : 2 ≤ 1+Real.log X := by linarith
  have hnorm (t : ℝ) (ht : t ∈ Icc (-(4/3)*(1+Real.log X)^Ct) ((4/3)*(1+Real.log X)^Ct)) :
      ‖largeTupleSmoothedPolynomial ℓ ξ z.1.1 z.1.2 s t‖ ≤ K₁*X^(5/6:ℝ)/(1+Real.log X)^(k+Ct) := by
    have ht' : |t| ≤ (4/3)*(1+Real.log X)^Ct := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
    have hu : |t| ≤ (1+Real.log (largeTupleGroupLength s z))^(Ct+2) := by
      apply (ht'.trans _).trans (hheight _ hBX)
      rw [pow_succ]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        ((by norm_num : (4/3:ℝ) ≤ 2).trans hLp) (pow_nonneg hL.le Ct)
    have hb := hbound z t hB₀ hrough hAlow hAhigh hu
    exact hb.trans (largeTuple_bilinear_scale hX (zero_le_one.trans (largeTupleGroupLength_one _ z))
      hBX hK₀.le hAB (k+Ct))
  have he := largeTupleRegroupedKernel_low_integral ℓ ξ X Ct hH z.1.2 s
  have hsame (t : ℝ) : largeTupleSmoothedPolynomial ℓ ξ X z.1.2 s t =
      largeTupleSmoothedPolynomial ℓ ξ z.1.1 z.1.2 s t := by rw [hz]
  rw [he]
  simp_rw [hsame]
  have he' : (∫ t : ℝ, (lowHeightWeight H ((1+Real.log X)^Ct) t*
      Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*largeTupleSmoothedPolynomial ℓ ξ z.1.1 z.1.2 s t) =
      ∫ t : ℝ, lowHeightWeight H ((1+Real.log X)^Ct) t*
        (Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*largeTupleSmoothedPolynomial ℓ ξ z.1.1 z.1.2 s t) := by
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [he']
  have hh := lowHeightWeight_integral_bound H (pow_pos hL Ct)
    (by dsimp [K₁]; positivity : 0 ≤ K₁*X^(5/6:ℝ)/(1+Real.log X)^(k+Ct))
    (fun t => Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*
      largeTupleSmoothedPolynomial ℓ ξ z.1.1 z.1.2 s t) (by
        intro t ht
        rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
        exact hnorm t ht)
  apply hh.trans_eq
  rw [pow_add]
  field_simp [hL.ne']

end CubicFirstMoment

end

end OAI
