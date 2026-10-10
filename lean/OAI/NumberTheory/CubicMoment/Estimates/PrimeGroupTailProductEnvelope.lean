import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.GroupedPrimeHeight

namespace OAI

/-! The full retained-envelope high tail for the actual two independent prime
convolutions. Every Mellin frequency is retained; the energies are derived. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem primeGroupTail_full_prime_envelope_tail
    (hHuxley : HuxleyAdditiveLargeSieve)
    {C R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
    (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
    (hBhi : ∀ r i x, R < x → WB r i x = 0) (k : ℕ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ K B₀ : ℝ, 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (eA eB : Eisenstein) (H T X : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, 1 ≤ XB i) →
      (2*R^Fintype.card ι*LB r)^(27/25:ℝ) ≤ LA r → LA r ≤ (LB r)^(19/10:ℝ) →
      (2*R^Fintype.card ι*LB r)^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ (LB r)^3 → 0 < X →
      ‖envelopeCutoffBilinearTail
        (fullSquarefreePrimeSupport R (WA r) XA eA)
        (fullSquarefreePrimeSupport R (WB r) XB eB)
        (fullPrimeCoefficient R (WA r) XA) (fullPrimeCoefficient R (WB r) XB)
        W H T X‖ ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨CA,dA,hCA,henergyA⟩ := logarithmic_full_coefficient_energy hWA hR hAlo hAhi
  obtain ⟨CB,dB,hCB,henergyB⟩ := logarithmic_full_coefficient_energy hWB hR hBlo hBhi
  obtain ⟨K,B₀,hK,hbound⟩ := primeGroupTail_envelope_log_saving hMV hC hHuxley
    (Mα := CA*2^dA) (Mβ := CB) (by positivity) hCB
    (one_le_pow₀ hR (n := Fintype.card ι)) k dA dB (R^Fintype.card κ) W hW hpos hsm
  refine ⟨K,B₀,hK,?_⟩
  intro r XA XB eA eB H T X hT hprodA hprodB hXA hXB hAlow hAhigh hTlow hH hHB hX
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hAB : LA r ≤ (LB r)^2 := hAhigh.trans (by
    rw [←Real.rpow_natCast (LB r) 2]
    exact Real.rpow_le_rpow_of_exponent_le (hLB r) (by norm_num))
  have hlogA : 1+Real.log (LA r) ≤ 2*(1+Real.log (LB r)) := by
    have hh := Real.log_le_log hAp hAB
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hα : (∑ x ∈ fullSquarefreePrimeSupport R (WA r) XA eA,
      ‖fullPrimeCoefficient R (WA r) XA x‖^2) ≤
        (CA*2^dA)*LA r*(1+Real.log (LB r))^dA := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _))
    apply (henergyA r XA (hLA r) hXA hprodA).trans
    calc
      _ ≤ CA*LA r*(2*(1+Real.log (LB r)))^dA :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith [Real.log_nonneg (hLA r)]) hlogA dA)
          (mul_nonneg hCA hAp.le)
      _ = _ := by rw [mul_pow]; ring
  have hβ : (∑ y ∈ fullSquarefreePrimeSupport R (WB r) XB eB,
      ‖fullPrimeCoefficient R (WB r) XB y‖^2) ≤
        CB*LB r*(1+Real.log (LB r))^dB :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)).trans (henergyB r XB (hLB r) hXB hprodB)
  apply hbound _ _ _ _ (LB r) (LA r) T H X hT hAlow hAhigh hTlow hH hHB hX _ _ hα hβ
  · intro x hx
    have hn := fullPrimeProduct_norm_bounds R (WA r) XA
      (fun i => zero_lt_one.trans_le (hXA i)) (hAlo r) (hAhi r) (Finset.mem_filter.mp hx).1
    rw [hprodA] at hn
    exact ⟨(fullSquarefreePrimeSupport_primary R (WA r) XA eA hx).1,hn⟩
  · intro y hy
    have hn := fullPrimeProduct_norm_bounds R (WB r) XB
      (fun i => zero_lt_one.trans_le (hXB i)) (hBlo r) (hBhi r) (Finset.mem_filter.mp hy).1
    rw [hprodB] at hn
    exact ⟨(fullSquarefreePrimeSupport_primary R (WB r) XB eB hy).1,
      (fullSquarefreePrimeSupport_primary R (WB r) XB eB hy).2,hn⟩

end CubicFirstMoment

end

end OAI
