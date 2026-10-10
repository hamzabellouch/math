import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsNontrivialGrid
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsScalar
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsSmallEnergy

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_witness_family_bounds (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z L : ℕ,
      adaptiveArrayThreshold ≤ Z → T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      Squarefree L → 2 ≤ L → L.primeFactors.card=auxiliaryK Z z →
      (L:ℝ) ≤ (Z:ℝ)^(1/50:ℝ) → (∀p∈L.primeFactors,z ≤ p) →
      ∀ P : Finset ℕ, (∀p∈P,p.Prime) → (∀p∈P,Odd p) →
      c*(Z:ℝ)/Real.log Z ≤ P.card → (∀p∈P,p ≤ 2*Z) →
      ∀ A : ∀p:ℕ,Finset (ZMod p),
      let k := evenMomentParameter (parameterX T) Z
      let l := gridMomentParameter T
      let K := (auxiliaryK Z z:ℝ)
      primeProductMean P k (fun q => (witnessFamilyMax (witnessLargeFamily L Z A)
        (adaptiveArraySupport L Z \ adaptiveSmallSupport L) q)^(2*l)) ≤ (Real.exp ((13/2000:ℝ)*K))^(2*l) ∧
      primeProductMean P k (fun q => (witnessFamilyMax (witnessNontrivialFamily L Z A)
        (adaptiveArraySupport L Z) q)^(2*l)) ≤ ((Z:ℝ)^(-(1/4:ℝ)))^(2*l) ∧
      primeProductMean P k (fun q => (witnessFamilyMax (adaptiveOffEventArrayFamily L Z (1/16) A K)
        (adaptiveSmallSupport L) q)^(2*l)) ≤ (Real.exp (-K/4))^(2*l) ∧
      primeProductMean P k (fun q => (witnessFamilyMax (adaptiveSmallArrayFamily L Z (1/16) A)
        (adaptiveSmallSupport L) q)^(2*l)) ≤ (Real.exp K)^(2*l) := by
  classical
  filter_upwards [eventually_witnessFamilyMax_moment c (1/4000) hc (by norm_num),
    eventually_witnessLargeFamily_energy,eventually_witnessNontrivialFamily_energy,
    eventually_witness_small_family_energies,eventually_auxiliaryK_bounds,
    eventually_auxiliaryK_le_log 1 (by norm_num),eventually_primeProduct_moment_orders,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 4000]
    with T hmoment hlarge hnontriv hsmall hK hKlog horders hT
  intro Z z L hZbig hZl hZu hz hzl hzu hL hL2 hLK hsize hprimes P hP ho hJ hPH A
  dsimp only
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZbig
  have hZ : 1 ≤ Z := by omega
  have hZr : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  have hZpos : (0:ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hLZ : L ≤ Z := by
    have hh : (Z:ℝ)^(1/50:ℝ) ≤ (Z:ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZr (show (1/50:ℝ) ≤ 1 by norm_num)
    exact_mod_cast hsize.trans hh
  have hKlo : 4000 ≤ (auxiliaryK Z z:ℝ) := hT.trans (hK Z z hZl hZu hz hzl hzu).1
  have hKZ : (auxiliaryK Z z:ℝ) ≤ Real.log Z := by simpa only [one_mul] using hKlog Z z hZl hZu hz hzl hzu
  have hl : 1 ≤ gridMomentParameter T := (horders Z hZl hZu).1
  have hC : cutoffFourierBound ≤ (Z:ℝ) := by
    have hh : (⌈max cutoffFourierBound adaptiveArrayConstant⌉₊:ℝ) ≤ Z := by
      exact_mod_cast (le_max_right 2 ⌈max cutoffFourierBound adaptiveArrayConstant⌉₊).trans hZbig
    exact (le_max_left _ _).trans ((Nat.le_ceil _).trans hh)
  have hbaseSF : ∀s∈adaptiveArraySupport L Z,Squarefree s := fun s hs => (Finset.mem_filter.mp hs).2.1
  have hbaseB : ∀s∈adaptiveArraySupport L Z,s ≤ Z^14 := fun s hs => (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
  have hsmallsub := adaptiveSmallSupport_subset hZ hLZ
  have hmoment' (S : Finset ℕ) (hS : S ⊆ adaptiveArraySupport L Z)
      (F : Finset (ℕ → ℂ)) (hF : F.card ≤ Z^430)
      (hmass : ∀b∈F,∑s∈S,‖b s‖ ≤ (Z:ℝ)^430) (a : ℝ) (ha : -1 ≤ a)
      (hE : ∀b∈F,∑s∈S,((((2*gridMomentParameter T:ℕ):ℝ)^2)^s.primeFactors.card)*‖b s‖^2 ≤ Real.exp (a*auxiliaryK Z z)) :
      primeProductMean P (evenMomentParameter (parameterX T) Z)
        (fun q => (witnessFamilyMax F S q)^(2*gridMomentParameter T)) ≤
        (Real.exp ((a/2+1/2000)*auxiliaryK Z z))^(2*gridMomentParameter T) := by
    exact (hmoment Z z hZl hZu hz hzl hzu P hP ho hJ hPH S
      (fun s hs => hbaseSF s (hS hs)) (fun s hs => hbaseB s (hS hs))
      F hF _ (Real.exp_pos _).le hE hmass).trans
      (witness_family_exponential_moment (by omega) hKlo hKZ hl ha)
  have hLP := witnessSubfamily_polynomial hZbig hL hLZ A (witnessLargeFamily_subset L Z A) (S:=adaptiveArraySupport L Z \ adaptiveSmallSupport L) Finset.sdiff_subset
  have hNP := witnessSubfamily_polynomial hZbig hL hLZ A (witnessNontrivialFamily_subset L Z A) (le_refl _)
  have hSP := adaptiveSmallArrayFamily_polynomial hL hZ2 hLZ hC (by norm_num : |(1/16:ℝ)| ≤ 1) A
  have hOP := adaptiveOffEventArrayFamily_polynomial hL hZ2 hLZ hC (by norm_num : |(1/16:ℝ)| ≤ 1) A (auxiliaryK Z z)
  have hSE := hsmall Z z L hZ hZl hZu hz hzl hzu hL hLK hLZ hprimes A
  refine ⟨?_,?_,?_,?_⟩
  · have hh := hmoment' _ Finset.sdiff_subset _ hLP.1 hLP.2 (12/1000) (by norm_num)
      (hlarge Z z L hZ hZl hZu hz hzl hzu hL hL2 hLK hsize hprimes A)
    norm_num only at hh ⊢
    exact hh
  · have hm := hmoment Z z hZl hZu hz hzl hzu P hP ho hJ hPH (adaptiveArraySupport L Z)
      hbaseSF hbaseB (witnessNontrivialFamily L Z A) hNP.1 (1/(Z:ℝ)) (by positivity)
      (hnontriv Z z L hZ hZl hZu hz hzl hzu hL hLK hsize hprimes A) hNP.2
    have hfirst : Real.exp (2*(gridMomentParameter T:ℝ)*(1/4000:ℝ)*(auxiliaryK Z z:ℝ)) ≤
        Real.exp (2*(gridMomentParameter T:ℝ)*(1/4000:ℝ)*Real.log Z) := by gcongr
    have hU : (1:ℝ)/Z=Real.exp (-1*Real.log Z) := by rw [neg_one_mul,Real.exp_neg,Real.exp_log hZpos,one_div]
    apply hm.trans
    apply (add_le_add (mul_le_mul_of_nonneg_right hfirst (by positivity)) (le_refl _)).trans
    rw [hU]
    apply (witness_family_exponential_moment (by omega) (hKlo.trans hKZ) (le_refl _) hl (le_refl (-1))).trans
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    rw [Real.rpow_def_of_pos hZpos]
    apply Real.exp_le_exp.mpr
    have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZr
    nlinarith
  · have hh := hmoment' _ hsmallsub _ hOP.1 hOP.2 (-1) (le_refl _)
      (fun b hb => by simpa only [neg_one_mul] using hSE.2 b hb)
    apply hh.trans
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    linarith
  · have hh := hmoment' _ hsmallsub _ hSP.1 hSP.2 1 (by norm_num)
      (fun b hb => by simpa only [one_mul] using hSE.1 b hb)
    apply hh.trans
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    linarith

end Ostmann.QuadraticCenter

end

end OAI
