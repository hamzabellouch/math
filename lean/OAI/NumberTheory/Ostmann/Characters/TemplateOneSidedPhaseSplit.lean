import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSplitBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem character_apply_modulus_congr
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) {m n : ℕ} (hm : m = n) (z : ℕ) :
    χ m (z : ZMod m) = χ n (z : ZMod n) := by
  subst n
  rfl

theorem fixedPhase_twoPrimeAssignment (D : I → I → ℤ) (p : I → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I) (q r : ℕ) :
    fixedPhase D (twoPrimeAssignment p L S q r) χ ν L S = fixedPhase D p χ ν L S := by
  unfold fixedPhase
  apply Finset.prod_congr rfl
  intro i hi
  rw [twoPrimeAssignment_frozen p L S q r i hi]
  congr 1
  apply Finset.prod_congr rfl
  intro h hh
  rw [twoPrimeAssignment_frozen p L S q r h hh]

theorem longUnary_twoPrimeAssignment (D : I → I → ℤ) (p : I → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I) (q r z : ℕ) :
    longUnary D (twoPrimeAssignment p L S q r) χ ν L S z = longUnary D p χ ν L S z := by
  have hrow : (∏ h ∈ frozenVertices L S, χ z (twoPrimeAssignment p L S q r h) ^ D L h) =
      ∏ h ∈ frozenVertices L S, χ z (p h) ^ D L h := by
    apply Finset.prod_congr rfl
    intro h hh
    rw [twoPrimeAssignment_frozen p L S q r h hh]
  have hcol : (∏ i ∈ frozenVertices L S, χ (twoPrimeAssignment p L S q r i) z ^ D i L) =
      ∏ i ∈ frozenVertices L S, χ (p i) z ^ D i L := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [twoPrimeAssignment_frozen p L S q r i hi]
  simp only [longUnary,hrow,hcol,fixedPhase_twoPrimeAssignment]

theorem shortUnary_twoPrimeAssignment (D : I → I → ℤ) (p : I → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I) (q r z : ℕ) :
    shortUnary D (twoPrimeAssignment p L S q r) χ ν L S z = shortUnary D p χ ν L S z := by
  have hrow : (∏ h ∈ frozenVertices L S, χ z (twoPrimeAssignment p L S q r h) ^ D S h) =
      ∏ h ∈ frozenVertices L S, χ z (p h) ^ D S h := by
    apply Finset.prod_congr rfl
    intro h hh
    rw [twoPrimeAssignment_frozen p L S q r h hh]
  have hcol : (∏ i ∈ frozenVertices L S, χ (twoPrimeAssignment p L S q r i) z ^ D i S) =
      ∏ i ∈ frozenVertices L S, χ (p i) z ^ D i S := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [twoPrimeAssignment_frozen p L S q r i hi]
  simp only [shortUnary,hrow,hcol]

theorem primeGraphPhase_twoPrimeAssignment (D : I → I → ℤ) (p : I → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hLS : L ≠ S) (hLL : D L L = 0) (hSS : D S S = 0) (q r : ℕ) :
    primeGraphPhase D (twoPrimeAssignment p L S q r)
      (fun i => χ (twoPrimeAssignment p L S q r i))
      (fun i => ν i (twoPrimeAssignment p L S q r i)) =
      longUnary D p χ ν L S q * shortUnary D p χ ν L S r *
        χ q r ^ D L S * χ r q ^ D S L := by
  let a := twoPrimeAssignment p L S q r
  have haL : a L = q := twoPrimeAssignment_long p L S hLS q r
  have haS : a S = r := twoPrimeAssignment_short p L S q r
  calc
    _ = longUnary D a χ ν L S q * shortUnary D a χ ν L S r *
        χ q r ^ D L S * χ r q ^ D S L := by
      simpa only [primeGraphPhase,longUnary,shortUnary,fixedPhase,
        character_apply_modulus_congr χ haL,character_apply_modulus_congr χ haS,haL,haS] using
        graph_product_split L S hLS (fun i => ν i (a i))
          (fun i h => χ (a i) (a h) ^ D i h)
          (by rw [hLL,zpow_zero]) (by rw [hSS,zpow_zero])
    _ = _ := by
      rw [longUnary_twoPrimeAssignment,shortUnary_twoPrimeAssignment]

theorem primeGraphPhase_oneSided (D : I → I → ℤ) (p : I → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (ν : I → ℕ → ℂ) (L S : I)
    (hLS : L ≠ S) (hLL : D L L = 0) (hSS : D S S = 0) (hrev : D L S = 0)
    (q r : ℕ) :
    primeGraphPhase D (twoPrimeAssignment p L S q r)
      (fun i => χ (twoPrimeAssignment p L S q r i))
      (fun i => ν i (twoPrimeAssignment p L S q r i)) =
      longUnary D p χ ν L S q * shortUnary D p χ ν L S r * χ r q ^ D S L := by
  rw [primeGraphPhase_twoPrimeAssignment D p χ ν L S hLS hLL hSS,hrev,zpow_zero,mul_one]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
