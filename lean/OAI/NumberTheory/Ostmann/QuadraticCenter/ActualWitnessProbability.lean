import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualArrayMean
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMoments
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessAuxiliaryData
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessProbabilityFinite
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessProbabilityScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_actual_witness_probability (d : Decomposition)
    (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ F : Finset ℕ,F.card=auxiliaryK Z z →
      ∀ hbal : ∀p∈F,BalancedResiduePrime d p,
      (∀p∈F,z≤p) → (∀p∈F,p<Z) →
      ((∏p∈F,p:ℕ):ℝ)≤(Z:ℝ)^(1/50:ℝ) →
      ∀ P : Finset ℕ,(∀r∈P,r.Prime) → (∀r∈P,Odd r) →
      (∀r∈P,Z≤r ∧ r≤2*Z) → c*(Z:ℝ)/Real.log Z≤P.card →
      ∀ ε t : ℕ→ℤ,(∀r∈P,ε r = -1 ∨ ε r = 1) →
      (∀r∈P,δ/4≤(∑a∈positiveIntegerWindow d.A (parameterX T),
        ((ε r*jacobiSym (a-t r) r:ℤ):ℝ))/(positiveIntegerWindow d.A (parameterX T)).card) →
      letI : ∀p:F,NeZero p.val := fun p => ⟨(balancedResiduePrime_prime (hbal p p.property)).ne_zero⟩
      letI : NeZero (∏p:F,p.val) := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
      Real.exp (-6*(auxiliaryK Z z:ℝ)) ≤
        (quadraticWitnessProducts P (evenMomentParameter (parameterX T) Z)
          (∏p:F,p.val) (quadraticResidueFamily d) (parameterX T) (auxiliaryK Z z) t).card /
          (Nat.choose P.card (evenMomentParameter (parameterX T) Z):ℝ) := by
  classical
  filter_upwards [eventually_actual_array_mean_lower d c δ hc hδ,
    eventually_actual_witness_moments c hc,eventually_auxiliary_witness_expectation_margin,
    eventually_auxiliaryK_pos,eventually_primeProduct_probability_scale c hc,
    eventually_primeProduct_moment_orders] with T hfull hupper hmargin hKpos hprob horders
  intro Z z hZl hZu hz hzl hzu F hcard hbal hlow hhigh hprod P hP ho hband hJ ε t hε hbias
  let : ∀p:F,NeZero p.val := fun p => ⟨(balancedResiduePrime_prime (hbal p p.property)).ne_zero⟩
  let : NeZero (∏p:F,p.val) := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
  let L := ∏p:F,p.val
  have hLeq : L=∏p∈F,p := Finset.prod_coe_sort F (fun p:ℕ => p)
  have hF : ∀p∈F,p.Prime := fun p hp => balancedResiduePrime_prime (hbal p hp)
  have hp := hprob Z hZl hZu
  have hZ : 1≤Z := by exact_mod_cast (show (1:ℝ)≤Z by linarith [hp.2.2.2.1])
  have hk : evenMomentParameter (parameterX T) Z≤P.card := by
    have hh := (hp.2.2.2.2.2 P.card hJ).2
    omega
  have hl : 0<gridMomentParameter T := (horders Z hZl hZu).1
  have hd := witness_auxiliary_product_data hF hcard (hKpos Z z hZl hZu hz hzl hzu) hZ hprod hlow
  have hsf : Squarefree L := by simpa only [hLeq] using hd.1
  have hL2 : 2≤L := by simpa only [hLeq] using hd.2.1
  have hLK : L.primeFactors.card=auxiliaryK Z z := by simpa only [hLeq] using hd.2.2.1
  have hLZ : L≤Z := by simpa only [hLeq] using hd.2.2.2.1
  have hprimes : ∀p∈L.primeFactors,z≤p := by simpa only [hLeq] using hd.2.2.2.2
  have hsize : (L:ℝ)≤(Z:ℝ)^(1/50:ℝ) := by simpa only [hLeq] using hprod
  have hm := hupper Z z L hZl hZu hz hzl hzu hsf hL2 hLK hsize hprimes
    P hP ho hband hJ (quadraticResidueFamily d) t
  have hmean := hfull Z z hZl hZu hz hzl hzu F hcard hbal hhigh hprod
    P hP ho hband hJ ε t hε hbias
  have hfinite := quadraticWitnessProducts_probability_of_array_bounds hZ
    (show (∏p∈F,p)≤Z by simpa only [hLeq] using hLZ) hP hk hl
    (quadraticResidueFamily d) (parameterX T) (auxiliaryK Z z) 3 t
    (hmargin Z z hZl hZu hz hzl hzu) hmean hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  norm_num only [show (2:ℝ)*3=6 by norm_num] at hfinite
  exact hfinite

end Ostmann.QuadraticCenter

end

end OAI
