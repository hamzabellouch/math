import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPriorBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template TemplateSupportRemoval
attribute [local instance] Classical.propDecidable

theorem integerPrimeWeight_nonneg {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (hE : 0 < primeShellMass E) (n : ℤ) : 0 ≤ integerPrimeWeight E n := by
  by_cases hn : n∈integerPrimeSupport E
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    rw [integerPrimeWeight_cast E hE]
    exact (primeShellPrior E hE).mass_nonneg _
  · simp only [integerPrimeWeight,hn,ite_false,le_refl]

theorem integerPrimeWeight_sum {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (hE : 0 < primeShellMass E) :
    (∑n∈integerPrimeSupport E,integerPrimeWeight E n)=1 := by
  rw [integerPrimeSupport,Finset.sum_image]
  · calc
      _ = ∑p∈E,(p.val:ℝ)⁻¹/primeShellMass E := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [integerPrimeWeight_cast E hE,primeShellPrior_mass,ite_eq_left hp]
      _ = 1 := by rw [←Finset.sum_div];exact div_self hE.ne'
  · intro p hp q hq he
    exact Subtype.ext (Int.ofNat_injective he)

def integerPrimeTest {I : Type*} {Q : ℕ} (F : (I → PrimeUpTo Q) → ℂ) : (I → ℤ) → ℂ :=
  Function.extend primeIntegerAssignment F (fun _=>0)

theorem integerPrimeTest_at_prime {I : Type*} {Q : ℕ}
    (F : (I → PrimeUpTo Q) → ℂ) (f : I → PrimeUpTo Q) :
    integerPrimeTest F (primeIntegerAssignment f)=F f :=
  primeIntegerAssignment_injective.extend_apply _ _ _

theorem primeProductPrior_cmean_eq_integer_extended {I : Type*}
    [Fintype I] [DecidableEq I] {Q : ℕ}
    (E : I → Finset (PrimeUpTo Q)) (hE : ∀i,0 < primeShellMass (E i))
    (F : (I → PrimeUpTo Q) → ℂ) :
    (productPrior (fun i=>primeShellPrior (E i) (hE i))).cmean F =
      fullProductMean (fun i=>integerPrimeSupport (E i)) (fun i=>integerPrimeWeight (E i))
        (integerPrimeTest F) := by
  simpa only [integerPrimeTest_at_prime] using
    primeProductPrior_cmean_eq_integer E hE (integerPrimeTest F)

theorem constituentPrimePrior_cmean_eq_integer (T : Layout) (width : Role → ℕ) {Q : ℕ}
    (E : T.Constituent width → Finset (PrimeUpTo Q)) (hE : ∀i,0 < primeShellMass (E i))
    (F : (T.Constituent width → PrimeUpTo Q) → ℂ) :
    (constituentPrimePrior T width E hE).cmean F =
      fullProductMean (fun i=>integerPrimeSupport (E i)) (fun i=>integerPrimeWeight (E i))
        (integerPrimeTest F) :=
  primeProductPrior_cmean_eq_integer_extended E hE F

end Ostmann.Characters.DiagonalEstimate

end

end OAI
