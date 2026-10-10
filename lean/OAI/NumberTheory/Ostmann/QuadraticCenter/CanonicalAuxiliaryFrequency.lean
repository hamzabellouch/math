import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifierFrequency
import OAI.NumberTheory.Ostmann.QuadraticCenter.CanonicalAuxiliaryProduct
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyDivisorExpansion

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

lemma quadraticFourierFrequency_intInverse_congr_modulus {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m=n) (f : ZMod m → ℂ) (g : ZMod n → ℂ)
    (hfg : ∀ a : ℤ,f (a:ZMod m)=g (a:ZMod n))
    (q : ℕ) (mInv : ℤ) (a R : ℝ) (u : ℤ) :
    quadraticFourierFrequency q m f (mInv:ZMod m) a R u =
      quadraticFourierFrequency q n g (mInv:ZMod n) a R u := by
  subst n
  have he : f=g := funext (fun x => by simpa only [ZMod.intCast_zmod_cast] using hfg (ZMod.cast x))
  rw [he]

theorem subset_quadraticFourierFrequency_eq_divisor {F : Finset ℕ}
    [∀ p : F, NeZero p.val] (hF : ∀ p ∈ F,Nat.Prime p)
    (hcop : Pairwise (fun p q : F => p.val.Coprime q.val))
    (A : ∀ p : ℕ, Finset (ZMod p)) (U : Finset F)
    [NeZero (∏ i : U,i.val.val)] (q : ℕ) (mInv : ℤ) (a R : ℝ) (u : ℤ) :
    quadraticFourierFrequency q (∏ i : U,i.val.val)
      (subsetCenteredProduct (fun p : F => p.val) hcop (fun p => A p.val) U)
      (mInv:ZMod (∏ i : U,i.val.val)) a R u =
    divisorFourierFrequency q (primeSubsetProduct U) A mInv a R u := by
  let : NeZero (∏ p : (primeSubsetProduct U).primeFactors,p.val) :=
    ⟨divisor_coordinates_product_ne_zero _⟩
  exact quadraticFourierFrequency_intInverse_congr_modulus
    (canonicalAuxiliary_period_eq hF U) _ (canonicalAuxiliaryCenteredProduct _ A)
    (subsetCenteredProduct_eq_canonical_intCast hF hcop A U) q mInv a R u

theorem subset_quadraticFourierFrequency_inverse_eq_divisor {F : Finset ℕ}
    [∀ p : F, NeZero p.val] (hF : ∀ p ∈ F,Nat.Prime p)
    (hcop : Pairwise (fun p q : F => p.val.Coprime q.val))
    (A : ∀ p : ℕ, Finset (ZMod p)) (U : Finset F)
    [NeZero (∏ i : U,i.val.val)] (q : ℕ) (a R : ℝ) (u : ℤ) :
    quadraticFourierFrequency q (∏ i : U,i.val.val)
      (subsetCenteredProduct (fun p : F => p.val) hcop (fun p => A p.val) U)
      (q:ZMod (∏ i : U,i.val.val))⁻¹ a R u =
    divisorFourierFrequency q (primeSubsetProduct U) A
      (ZMod.cast ((q:ZMod (primeSubsetProduct U))⁻¹)) a R u := by
  have h := subset_quadraticFourierFrequency_eq_divisor hF hcop A U q
    (ZMod.cast ((q:ZMod (∏ i : U,i.val.val))⁻¹)) a R u
  rw [ZMod.intCast_zmod_cast] at h
  have he : (ZMod.cast ((q:ZMod (∏ i : U,i.val.val))⁻¹):ℤ) =
      ZMod.cast ((q:ZMod (primeSubsetProduct U))⁻¹) := by
    rw [canonicalAuxiliary_subset_modulus]
  rwa [he] at h

theorem subsetAmplifierFrequency_eq_canonical {F : Finset ℕ}
    [∀ p : F, NeZero p.val] (hF : ∀ p ∈ F,Nat.Prime p)
    (hcop : Pairwise (fun p q : F => p.val.Coprime q.val))
    (A : ∀ p : ℕ, Finset (ZMod p)) (U : Finset F)
    (lam : ℝ) (q : ℕ) (X a : ℝ) (u : ℤ) :
    subsetAmplifierFrequency (fun p : F => p.val) hcop (fun p => A p.val) U lam q X a u =
      ((lam:ℂ)^(primeSubsetProduct U).primeFactors.card *
        (jacobiSym (primeSubsetProduct U:ℤ) q:ℂ) /
        (Real.sqrt (((q:ℝ)/X)*(primeSubsetProduct U)) : ℂ)) *
      divisorFourierFrequency q (primeSubsetProduct U) A
        (ZMod.cast ((q:ZMod (primeSubsetProduct U))⁻¹)) a ((q:ℝ)/X) u := by
  let : NeZero (∏ i : U,i.val.val) := ⟨(subset_modulus_pos (fun p : F => p.val) U).ne'⟩
  dsimp only [subsetAmplifierFrequency]
  rw [subset_quadraticFourierFrequency_inverse_eq_divisor hF hcop A U q a ((q:ℝ)/X) u,
    canonicalAuxiliary_subset_modulus,primeSubsetProduct_primeFactors_card hF]

end Ostmann.QuadraticCenter

end

end OAI
