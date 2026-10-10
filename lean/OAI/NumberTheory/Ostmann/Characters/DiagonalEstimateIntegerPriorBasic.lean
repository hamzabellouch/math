import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSizeBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalPrior

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template TemplateSupportRemoval
attribute [local instance] Classical.propDecidable

def integerPrimeSupport {Q : ℕ} (E : Finset (PrimeUpTo Q)) : Finset ℤ :=
  E.image (fun p=>(p.val:ℤ))

def integerPrimeWeight {Q : ℕ} (E : Finset (PrimeUpTo Q)) (n : ℤ) : ℝ :=
  if n∈integerPrimeSupport E then (n:ℝ)⁻¹/primeShellMass E else 0

theorem integerPrimeSupport_cast_mem {Q : ℕ} (E : Finset (PrimeUpTo Q)) (p : PrimeUpTo Q) :
    (p.val:ℤ)∈integerPrimeSupport E ↔ p∈E := by
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp h
    have hqp : q=p := Subtype.ext (Int.ofNat_injective he)
    exact hqp ▸ hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩

theorem integerPrimeWeight_cast {Q : ℕ} (E : Finset (PrimeUpTo Q))
    (hE : 0 < primeShellMass E) (p : PrimeUpTo Q) :
    integerPrimeWeight E (p.val:ℤ)=(primeShellPrior E hE).mass p := by
  simp only [integerPrimeWeight,integerPrimeSupport_cast_mem,primeShellPrior_mass]
  by_cases hp : p∈E <;> simp only [hp,ite_true,ite_false,Int.cast_natCast,zero_div]

def primeIntegerAssignment {I : Type*} {Q : ℕ} (f : I → PrimeUpTo Q) : I → ℤ :=
  fun i=>(f i).val

theorem primeIntegerAssignment_injective {I : Type*} {Q : ℕ} :
    Function.Injective (primeIntegerAssignment (I:=I) (Q:=Q)) := by
  intro f g he
  funext i
  exact Subtype.ext (Int.ofNat_injective (congrFun he i))

theorem primeProductPrior_cmean_eq_integer {I : Type*} [Fintype I] [DecidableEq I] {Q : ℕ}
    (E : I → Finset (PrimeUpTo Q)) (hE : ∀i,0 < primeShellMass (E i))
    (G : (I → ℤ) → ℂ) :
    (productPrior (fun i=>primeShellPrior (E i) (hE i))).cmean
      (fun f=>G (primeIntegerAssignment f)) =
    fullProductMean (fun i=>integerPrimeSupport (E i)) (fun i=>integerPrimeWeight (E i)) G := by
  let μ := productPrior (fun i=>primeShellPrior (E i) (hE i))
  have hrestrict : μ.cmean (fun f=>G (primeIntegerAssignment f)) =
      ∑f∈Fintype.piFinset E,(μ.mass f:ℂ)*G (primeIntegerAssignment f) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro f hf hnot
    have hz : μ.mass f=0 := by
      by_contra hm
      exact hnot (Fintype.mem_piFinset.mpr
        (fun i=>primeProductPrior_mem_of_mass_ne_zero E hE f hm i))
    simp only [hz,Complex.ofReal_zero,zero_mul]
  change μ.cmean _ = _
  rw [hrestrict]
  unfold fullProductMean
  apply Finset.sum_bij (fun f _=>primeIntegerAssignment f)
  · intro f hf
    exact Fintype.mem_piFinset.mpr (fun i=>Finset.mem_image.mpr
      ⟨f i,Fintype.mem_piFinset.mp hf i,rfl⟩)
  · intro f hf g hg he
    exact primeIntegerAssignment_injective he
  · intro a ha
    have hh : ∀i,∃p : PrimeUpTo Q,p∈E i ∧ (p.val:ℤ)=a i := by
      intro i
      exact Finset.mem_image.mp (Fintype.mem_piFinset.mp ha i)
    choose f hf he using hh
    exact ⟨f,Fintype.mem_piFinset.mpr hf,funext he⟩
  · intro f hf
    congr 2
    change (∏i,(primeShellPrior (E i) (hE i)).mass (f i))=
      ∏i,integerPrimeWeight (E i) (primeIntegerAssignment f i)
    apply Finset.prod_congr rfl
    intro i hi
    exact (integerPrimeWeight_cast (E i) (hE i) (f i)).symm

end Ostmann.Characters.DiagonalEstimate

end

end OAI
