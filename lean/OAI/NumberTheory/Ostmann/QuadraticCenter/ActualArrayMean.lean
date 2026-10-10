import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualAmplifiedDistinct
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualArrayMeanScales
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualArrayResidues
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeBlockCenter
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductArrays

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_actual_array_mean_lower (d : Decomposition)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ F : Finset ℕ, F.card = auxiliaryK Z z →
      ∀ hbal : ∀ p ∈ F, BalancedResiduePrime d p,
      (∀ p ∈ F,p < Z) → ((∏ p ∈ F,p : ℕ):ℝ) ≤ (Z:ℝ)^(1/50:ℝ) →
      ∀ P : Finset ℕ, (∀ r ∈ P,r.Prime) → (∀ r ∈ P,Odd r) →
      (∀ r ∈ P,Z ≤ r ∧ r ≤ 2*Z) → c*(Z:ℝ)/Real.log Z ≤ P.card →
      ∀ ε t : ℕ → ℤ, (∀ r ∈ P,ε r = -1 ∨ ε r = 1) →
      (∀ r ∈ P,δ/4 ≤ (∑ a ∈ positiveIntegerWindow d.A (parameterX T),
        ((ε r*jacobiSym (a-t r) r:ℤ):ℝ)) /
          (positiveIntegerWindow d.A (parameterX T)).card) →
      letI : ∀ p : F,NeZero p.val := fun p => ⟨(balancedResiduePrime_prime (hbal p p.property)).ne_zero⟩
      letI : NeZero (∏ p : F,p.val) := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
      Real.exp ((3/200:ℝ)*auxiliaryK Z z) ≤
        primeProductMean P (evenMomentParameter (parameterX T) Z)
          (fun q => ‖primeProductArraySum F (quadraticResidueFamily d) (1/16)
            (parameterX T) t (Z^14) q‖) := by
  classical
  filter_upwards [eventually_actual_amplified_moment_lower d hδ,
    eventually_actual_amplified_distinct_lower c hc,
    eventually_primeProduct_probability_scale c hc,
    eventually_primeProduct_moment_orders,eventually_primeProduct_radius_bounds,
    eventually_actual_array_mean_exponential_loss,
    parameterX_tendsto.eventually_gt_atTop 0]
    with T hmoment hdistinct hprob horders hradius hloss hX
  intro Z z hZl hZu hz hzl hzu F hcard hbal hpZ hprod P hP ho hband hJ ε t hε hbias
  let : ∀ p : F,NeZero p.val := fun p => ⟨(balancedResiduePrime_prime (hbal p p.property)).ne_zero⟩
  let : NeZero (∏ p : F,p.val) := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
  have hF : ∀ p ∈ F,p.Prime := fun p hp => balancedResiduePrime_prime (hbal p hp)
  have hcop := primeBlock_pairwise_coprime F hF
  have hpr := hprob Z hZl hZu
  have hJpos := (hpr.2.2.2.2.2 P.card hJ).1
  have hkJ : evenMomentParameter (parameterX T) Z ≤ P.card := by
    have hh := (hpr.2.2.2.2.2 P.card hJ).2
    omega
  have hk : 0 < evenMomentParameter (parameterX T) Z := by
    have hh := horders Z hZl hZu
    omega
  have hXr : (0:ℝ) < parameterX T := by exact_mod_cast hX
  have hsqrt : 0 < Real.sqrt (parameterX T:ℝ) := Real.sqrt_pos.mpr hXr
  have hZ : 1 ≤ Z := by have hh := hpr.2.2.2.1; exact_mod_cast (by linarith : (1:ℝ) ≤ Z)
  have hcopP : ∀ r ∈ P,r.Coprime (∏ p : F,p.val) := by
    intro r hr
    apply Nat.Coprime.prod_right
    intro p _
    exact (Nat.coprime_primes (hP r hr) (hF p p.property)).mpr
      (by have hp := hpZ p p.property; have hh := (hband r hr).1; omega)
  have hI := hmoment Z z hZl hZu hz hzl hzu F (fun p : F => p.val) hcop
    (fun p => inferInstance) (by simpa using hcard) (fun p => hbal p p.property)
    (fun p => (hpZ p p.property).le) P hJpos ε t hε hbias
  have hII := hdistinct Z z hZl hZu hz hzl hzu F (fun p : F => p.val) hcop
    (fun p => inferInstance) (by simpa only [Finset.prod_coe_sort F (fun p : ℕ => p)] using hprod)
    (fun p => d.residueSupport p.val) P hJ ε t hε hI
  have hB : ∀ q ∈ primeProductSamples P (evenMomentParameter (parameterX T) Z),
      ((q:ℝ)/parameterX T)*(∏ p ∈ F,p) ≤ (Z^14:ℕ) := by
    intro q hq
    exact primeProduct_array_cutoff hZ (hradius Z hZl P hband q hq).2 hprod
  have hIII := amplified_distinct_le_array_mean hF hcop (quadraticResidueFamily d)
    (lam:=1/16) (by norm_num) (by norm_num) hXr P hP ho hcopP hJpos ε t hε hk hkJ (Z^14) hB
  simp only [quadraticResidueFamily_eq] at hIII
  have hnorm := (div_le_div_of_nonneg_right hII hsqrt.le).trans hIII
  have hcancel : (Real.sqrt (parameterX T:ℝ)*
      Real.exp ((2/125:ℝ)*auxiliaryK Z z)/2)/Real.sqrt (parameterX T:ℝ) =
      Real.exp ((2/125:ℝ)*auxiliaryK Z z)/2 := by
    field_simp
  rw [hcancel] at hnorm
  exact (hloss Z z hZl hZu hz hzl hzu).trans (by linarith)

end Ostmann.QuadraticCenter

end

end OAI
