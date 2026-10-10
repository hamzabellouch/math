import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingSplitDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem character_apply_modulus_congr
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) {m n : ℕ} (hm : m = n) (z : ℕ) :
    χ m (z : ZMod m) = χ n (z : ZMod n) := by
  subst n
  rfl

theorem indexedFixedPhase_twoPrimeAssignment (D : I → I → ℤ) (p : I → ℕ)
    (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I) (q r : ℕ) :
    indexedFixedPhase D (twoPrimeAssignment p L S q r) χ ν L S = indexedFixedPhase D p χ ν L S := by
  unfold indexedFixedPhase
  apply Finset.prod_congr rfl
  intro i hi
  rw [twoPrimeAssignment_frozen p L S q r i hi]
  congr 1
  apply Finset.prod_congr rfl
  intro h hh
  rw [twoPrimeAssignment_frozen p L S q r h hh]

theorem indexedLongUnary_twoPrimeAssignment (D : I → I → ℤ) (p : I → ℕ)
    (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I) (q r z : ℕ) :
    indexedLongUnary D (twoPrimeAssignment p L S q r) χ ν L S z = indexedLongUnary D p χ ν L S z := by
  have hrow : (∏ h ∈ frozenVertices L S, χ L z (twoPrimeAssignment p L S q r h) ^ D L h) =
      ∏ h ∈ frozenVertices L S, χ L z (p h) ^ D L h := by
    apply Finset.prod_congr rfl
    intro h hh
    rw [twoPrimeAssignment_frozen p L S q r h hh]
  have hcol : (∏ i ∈ frozenVertices L S, χ i (twoPrimeAssignment p L S q r i) z ^ D i L) =
      ∏ i ∈ frozenVertices L S, χ i (p i) z ^ D i L := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [twoPrimeAssignment_frozen p L S q r i hi]
  simp only [indexedLongUnary,hrow,hcol,indexedFixedPhase_twoPrimeAssignment]

theorem indexedShortUnary_twoPrimeAssignment (D : I → I → ℤ) (p : I → ℕ)
    (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I) (q r z : ℕ) :
    indexedShortUnary D (twoPrimeAssignment p L S q r) χ ν L S z = indexedShortUnary D p χ ν L S z := by
  have hrow : (∏ h ∈ frozenVertices L S, χ S z (twoPrimeAssignment p L S q r h) ^ D S h) =
      ∏ h ∈ frozenVertices L S, χ S z (p h) ^ D S h := by
    apply Finset.prod_congr rfl
    intro h hh
    rw [twoPrimeAssignment_frozen p L S q r h hh]
  have hcol : (∏ i ∈ frozenVertices L S, χ i (twoPrimeAssignment p L S q r i) z ^ D i S) =
      ∏ i ∈ frozenVertices L S, χ i (p i) z ^ D i S := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [twoPrimeAssignment_frozen p L S q r i hi]
  simp only [indexedShortUnary,hrow,hcol]

theorem indexedPrimeGraphPhase_twoPrimeAssignment (D : I → I → ℤ) (p : I → ℕ)
    (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hLS : L ≠ S) (hLL : D L L = 0) (hSS : D S S = 0) (q r : ℕ) :
    primeGraphPhase D (twoPrimeAssignment p L S q r)
      (fun i => χ i (twoPrimeAssignment p L S q r i))
      (fun i => ν i (twoPrimeAssignment p L S q r i)) =
      indexedLongUnary D p χ ν L S q * indexedShortUnary D p χ ν L S r *
        χ L q r ^ D L S * χ S r q ^ D S L := by
  let a := twoPrimeAssignment p L S q r
  have haL : a L = q := twoPrimeAssignment_long p L S hLS q r
  have haS : a S = r := twoPrimeAssignment_short p L S q r
  calc
    _ = indexedLongUnary D a χ ν L S q * indexedShortUnary D a χ ν L S r *
        χ L q r ^ D L S * χ S r q ^ D S L := by
      simpa only [primeGraphPhase,indexedLongUnary,indexedShortUnary,indexedFixedPhase,
        character_apply_modulus_congr (χ L) haL,character_apply_modulus_congr (χ S) haS,haL,haS] using
        graph_product_split L S hLS (fun i => ν i (a i))
          (fun i h => χ i (a i) (a h) ^ D i h)
          (by rw [hLL,zpow_zero]) (by rw [hSS,zpow_zero])
    _ = _ := by
      rw [indexedLongUnary_twoPrimeAssignment,indexedShortUnary_twoPrimeAssignment]

theorem indexedPrimeGraphPhase_oneSided (D : I → I → ℤ) (p : I → ℕ)
    (χ : I → (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hLS : L ≠ S) (hLL : D L L = 0) (hSS : D S S = 0) (hrev : D L S = 0)
    (q r : ℕ) :
    primeGraphPhase D (twoPrimeAssignment p L S q r)
      (fun i => χ i (twoPrimeAssignment p L S q r i))
      (fun i => ν i (twoPrimeAssignment p L S q r i)) =
      indexedLongUnary D p χ ν L S q * indexedShortUnary D p χ ν L S r * χ S r q ^ D S L := by
  rw [indexedPrimeGraphPhase_twoPrimeAssignment D p χ ν L S hLS hLL hSS,hrev,zpow_zero,mul_one]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
