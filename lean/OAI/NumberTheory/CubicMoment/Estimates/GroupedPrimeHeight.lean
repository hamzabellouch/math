import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductBilinear
import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinearScale

namespace OAI

/-! The height mean for the two actual independent prime convolutions.
This supplies the complementary Mellin-frequency estimate after grouping. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem full_prime_product_height_bilinear
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
    (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
    (hBhi : ∀ r i x, R < x → WB r i x = 0) (k : ℕ) :
    ∃ (η σ : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (eA eB : Eisenstein) (u T : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/4) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      eB ≠ 0 → norm eB ≤ (LB r)^σ →
      (1+Real.log (LB r))^m ≤ T → T ≤ (LB r)^(7/20:ℝ) → |u| ≤ (LB r)^(7/20:ℝ) →
      dyadicHeightMean (fun t =>
        ‖∑ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
          ∑ y ∈ fullSquarefreePrimeSupport R (WB r) XB eB,
            fullPrimeCoefficient R (WA r) XA x*fullPrimeCoefficient R (WB r) XB y*
              gauss (x*y)*normTwist (u+t) (x*y)‖) T ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨CA,d,hCA,henergy⟩ := logarithmic_full_coefficient_energy hWA hR hAlo hAhi
  have hM : 0 ≤ CA*2^d := by positivity
  obtain ⟨η,σ,hη,hη1,hσ,hbound⟩ := rough_prime_height_bilinear
    (γ := γ) (ι := ι) (Q := R^Fintype.card κ)
    hpub hHuxley hperiod hMV hC hc hc1 hR hM hGI hGQ k d
  obtain ⟨G,K,B₀,m,hK,hbound⟩ := hbound LB WB hLB hWB hBlo hBhi
  refine ⟨η,σ,G,K,B₀,m,hη,hη1,hσ,hK,?_⟩
  intro r XA XB eA eB u T hT hprodA hprodB hXA hXB hAlow hAhigh he heN hTlow hThi hu
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hBp : 0 < LB r := zero_lt_one.trans_le (hLB r)
  have hlogB : 0 ≤ Real.log (LB r) := Real.log_nonneg (hLB r)
  have hpow : 1 ≤ (1+Real.log (LB r))^G := one_le_pow₀ (by linarith)
  have hAB : LA r ≤ (LB r)^2 := hAhigh.trans (div_le_self (sq_nonneg _) hpow)
  have hlogA : 1+Real.log (LA r) ≤ 2*(1+Real.log (LB r)) := by
    have hh := Real.log_le_log hAp hAB
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hα : (∑ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
      ‖fullPrimeCoefficient R (WA r) XA x‖^2) ≤
        (CA*2^d)*LA r*(1+Real.log (LB r))^d := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _))
    apply (henergy r XA (hLA r) hXA hprodA).trans
    calc
      _ ≤ CA*LA r*(2*(1+Real.log (LB r)))^d :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith [Real.log_nonneg (hLA r)]) hlogA d)
          (mul_nonneg hCA hAp.le)
      _ = _ := by rw [mul_pow]; ring
  apply hbound r XB (LA r) eB u T
    (fullSquarefreePrimeSupport R (WA r) XA eA) (fullPrimeCoefficient R (WA r) XA)
    hT hprodB hXB hAlow hAhigh he heN hTlow hThi hu _ hα
  intro x hx
  have hn := fullPrimeProduct_norm_bounds R (WA r) XA
    (fun i => zero_lt_one.trans_le (hXA i)) (hAlo r) (hAhi r) (Finset.mem_filter.mp hx).1
  rw [hprodA] at hn
  exact ⟨(fullSquarefreePrimeSupport_primary R (WA r) XA eA hx).1,
    (le_div_iff₀ hAp).mpr (by simpa only [one_mul] using hn.1),
    (div_le_iff₀ hAp).mpr hn.2⟩

end CubicFirstMoment

end

end OAI
