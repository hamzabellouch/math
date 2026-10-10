import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifierExpansion
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyDivisor
import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMomentReindex

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def canonicalAuxiliaryCenteredProduct (d : ℕ) (A : ∀ p : ℕ, Finset (ZMod p)) :
    ZMod (∏ p : d.primeFactors,p.val) → ℂ :=
  letI : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  centeredProduct (fun p : d.primeFactors => p.val) (divisor_coordinates_coprime d) (fun p => A p.val)

def canonicalPrimeIndicator (A : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) (p : ℕ) : ℂ :=
  if hp : p.Prime then
    letI : NeZero p := ⟨hp.ne_zero⟩
    (Supply.centeredIndicator (A p) (n : ZMod p):ℂ)
  else 0

lemma canonicalAuxiliaryCenteredProduct_intCast (d : ℕ)
    (A : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    canonicalAuxiliaryCenteredProduct d A (n : ZMod (∏ p : d.primeFactors,p.val)) =
      ∏ p ∈ d.primeFactors, canonicalPrimeIndicator A n p := by
  unfold canonicalAuxiliaryCenteredProduct
  rw [centeredProduct_intCast]
  calc
    _ = ∏ p : d.primeFactors, canonicalPrimeIndicator A n p.val := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [canonicalPrimeIndicator,divisor_coordinate_prime d p]
    _ = _ := Finset.prod_coe_sort d.primeFactors _

lemma canonicalAuxiliary_subset_modulus {F : Finset ℕ} (U : Finset F) :
    (∏ i : U,i.val.val) = primeSubsetProduct U := Finset.prod_coe_sort U _

lemma canonicalAuxiliary_period_eq {F : Finset ℕ} (hF : ∀ p ∈ F,Nat.Prime p)
    (U : Finset F) :
    (∏ i : U,i.val.val) = ∏ p : (primeSubsetProduct U).primeFactors,p.val := by
  rw [canonicalAuxiliary_subset_modulus,
    divisor_coordinates_product (primeSubsetProduct_squarefree hF U)]

theorem subsetCenteredProduct_eq_canonical_intCast {F : Finset ℕ}
    [∀ p : F, NeZero p.val] (hF : ∀ p ∈ F,Nat.Prime p)
    (hcop : Pairwise (fun p q : F => p.val.Coprime q.val))
    (A : ∀ p : ℕ, Finset (ZMod p)) (U : Finset F) (n : ℤ) :
    subsetCenteredProduct (fun p : F => p.val) hcop (fun p => A p.val) U
      (n : ZMod (∏ i : U,i.val.val)) =
    canonicalAuxiliaryCenteredProduct (primeSubsetProduct U) A
      (n : ZMod (∏ p : (primeSubsetProduct U).primeFactors,p.val)) := by
  rw [subsetCenteredProduct_intCast,canonicalAuxiliaryCenteredProduct_intCast,
    primeSubsetProduct_primeFactors hF]
  rw [Finset.prod_image (fun a _ b _ hab => Subtype.ext hab)]
  apply Finset.prod_congr rfl
  intro p hp
  simp [canonicalPrimeIndicator,hF p.val p.property]

theorem unitaryDFT_intCast_congr_modulus {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m=n) (f : ZMod m → ℂ) (g : ZMod n → ℂ)
    (hfg : ∀ a : ℤ,f (a:ZMod m)=g (a:ZMod n)) (u : ℤ) :
    Supply.unitaryDFT f (u:ZMod m) = Supply.unitaryDFT g (u:ZMod n) := by
  subst n
  have he : f=g := funext (fun x => by simpa only [ZMod.intCast_zmod_cast] using hfg (ZMod.cast x))
  rw [he]

end Ostmann.QuadraticCenter

end

end OAI
