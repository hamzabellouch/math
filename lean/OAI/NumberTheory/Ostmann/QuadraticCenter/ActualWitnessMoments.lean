import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsApprox
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsBudgets
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsFamilies

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_actual_witness_moments (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z L : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ hL : Squarefree L, 2 ≤ L → L.primeFactors.card=auxiliaryK Z z →
      (L:ℝ) ≤ (Z:ℝ)^(1/50:ℝ) → (∀p∈L.primeFactors,z ≤ p) →
      ∀ P : Finset ℕ, (∀p∈P,p.Prime) → (∀p∈P,Odd p) →
      (∀p∈P,Z ≤ p ∧ p ≤ 2*Z) → c*(Z:ℝ)/Real.log Z ≤ P.card →
      ∀ (A : ∀p:ℕ,Finset (ZMod p)) (t : ℕ → ℤ),
      letI : NeZero L := ⟨hL.ne_zero⟩
      let X := parameterX T
      let k := evenMomentParameter X Z
      let l := gridMomentParameter T
      let K := (auxiliaryK Z z:ℝ)
      primeProductMean P k (fun q => ‖primeProductLargeSum L Z A (1/16) X t q‖) ≤ Real.exp ((7/1000:ℝ)*K) ∧
      primeProductMean P k (fun q => ‖primeProductNontrivialSum L Z A (1/16) X t q‖) ≤ 1 ∧
      primeProductMean P k (primeProductSmallOffEventNorm L A (1/16) X K t) ≤ 1 ∧
      primeProductMean P k (fun q => ‖primeProductSmallSum L A (1/16) X t q‖^(2*l)) ≤
        (Real.exp (3*K))^(2*l) := by
  classical
  filter_upwards [eventually_witness_family_bounds c hc,eventually_witness_moment_budgets,
    eventually_primeProduct_radius_bounds,eventually_primeProduct_probability_scale c hc,
    eventually_primeProduct_moment_orders] with T hfamilies hbudgets hradius hprob horders
  intro Z z L hZl hZu hz hzl hzu hL hL2 hLK hsize hprimes P hP ho hband hJ A t
  let : NeZero L := ⟨hL.ne_zero⟩
  dsimp only
  obtain ⟨hZbig,hKlo,hKZ,hcount⟩ := hbudgets Z z hZl hZu hz hzl hzu
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZbig
  have hZ : 1 ≤ Z := by omega
  have hZr : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  have hLZ : L ≤ Z := by
    have hh : (Z:ℝ)^(1/50:ℝ) ≤ (Z:ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZr (show (1/50:ℝ) ≤ 1 by norm_num)
    exact_mod_cast hsize.trans hh
  have hC := (adaptiveArrayFamily_polynomial hZbig hL hLZ (by norm_num : |(1/16:ℝ)| ≤ 1) A).2.2
  have hkJ : evenMomentParameter (parameterX T) Z ≤ P.card := by
    have hh := ((hprob Z hZl hZu).2.2.2.2.2 P.card hJ).2
    omega
  have hl := (horders Z hZl hZu).1
  have hPH : ∀p∈P,p ≤ 2*Z := fun p hp => (hband p hp).2
  have hdata (q : ℕ) (hq : q ∈ primeProductSamples P (evenMomentParameter (parameterX T) Z)) :=
    primeProductSamples_properties hP ho hPH hq
  have hrad (q : ℕ) (hq : q ∈ primeProductSamples P (evenMomentParameter (parameterX T) Z)) :=
    hradius Z hZl P hband q hq
  have hF := hfamilies Z z L hZbig hZl hZu hz hzl hzu hL hL2 hLK hsize hprimes P hP ho hJ hPH A
  have hroot (F : Finset (ℕ → ℂ)) (S : Finset ℕ) (M : ℝ) (hM : 0 ≤ M)
      (hm : primeProductMean P (evenMomentParameter (parameterX T) Z)
        (fun q => (witnessFamilyMax F S q)^(2*gridMomentParameter T)) ≤ M^(2*gridMomentParameter T)) :
      primeProductMean P (evenMomentParameter (parameterX T) Z) (witnessFamilyMax F S) ≤ M :=
    primeProductMean_le_of_even_moment hP hkJ (by omega) _ (fun q _ => witnessFamilyMax_nonneg F S q) hM hm
  have hlarge := hroot _ _ _ (Real.exp_pos _).le hF.1
  have hrest := hroot _ _ _ (Real.rpow_nonneg (Nat.cast_nonneg Z) _) hF.2.1
  have hoff := hroot _ _ _ (Real.exp_pos _).le hF.2.2.1
  have hsmallNear : ∀q∈primeProductSamples P (evenMomentParameter (parameterX T) Z),
      ‖primeProductSmallSum L A (1/16) (parameterX T) t q‖ ≤
        witnessFamilyMax (adaptiveSmallArrayFamily L Z (1/16) A) (adaptiveSmallSupport L) q+(Z:ℝ)^(-(66:ℝ)) := by
    intro q hq
    exact primeProductSmallSum_le_family hL hZ hLZ hC (hdata q hq).1 (hdata q hq).2.1 A _ t (hrad q hq).1 (hrad q hq).2
  refine ⟨?_,?_,?_,?_⟩
  · apply (witness_mean_le_of_near hP hkJ (fun q hq =>
      primeProductLargeSum_le_family hL hZ hLZ hC (hdata q hq).1 (hdata q hq).2.1 A _ t
        (hrad q hq).1 (hrad q hq).2) hlarge).trans
    exact witness_large_mesh_budget hZ2 hKlo
  · have hh' : primeProductMean P (evenMomentParameter (parameterX T) Z)
        (fun q => ‖primeProductNontrivialSum L Z A (1/16) (parameterX T) t q‖) ≤
      (2:ℝ)^(evenMomentParameter (parameterX T) Z)*
        (primeProductMean P (evenMomentParameter (parameterX T) Z)
          (witnessFamilyMax (witnessNontrivialFamily L Z A) (adaptiveArraySupport L Z))+(Z:ℝ)^(-(66:ℝ))) := by
      have hpoint := primeProductMean_mono P (evenMomentParameter (parameterX T) Z) (fun q hq => by
        simpa only [(hdata q hq).2.2.2] using
          primeProductNontrivialSum_le_family hL hZ hLZ hC (hdata q hq).1 (hdata q hq).2.1
            (fun p hp => (hband p (primeProductSamples_primeFactors_subset hP hq hp)).1) A _ t
              (hrad q hq).1 (hrad q hq).2)
      rw [primeProductMean_mul_const,primeProductMean_add,primeProductMean_const hP hkJ] at hpoint
      exact hpoint
    exact hh'.trans ((mul_le_mul_of_nonneg_left (add_le_add hrest (le_refl _)) (by positivity)).trans
      (witness_nontrivial_mesh_budget hZ2 (hKlo.trans hKZ) hcount))
  · apply (witness_mean_le_of_near hP hkJ (fun q hq =>
      primeProductSmallOffEventNorm_le_family hL hZ hLZ hC (hdata q hq).1 (hdata q hq).2.1 A _ _ t
        (hrad q hq).1 (hrad q hq).2 (by linarith) hKZ) hoff).trans
    exact witness_offevent_mesh_budget hZ2 hKlo
  · apply witness_shifted_moment hP hkJ hl (fun q _ => norm_nonneg _)
      (fun q _ => witnessFamilyMax_nonneg _ _ q) (by linarith : 4 ≤ (auxiliaryK Z z:ℝ))
      (fun q hq => (hsmallNear q hq).trans (add_le_add (le_refl _) ((witness_mesh_error_le_half hZ2).trans (by norm_num))))
    exact hF.2.2.2

end Ostmann.QuadraticCenter

end

end OAI
