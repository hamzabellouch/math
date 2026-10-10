import OAI.NumberTheory.Ostmann.Characters.TemplateInitialPhase

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
variable {I : Type*} [Fintype I] [DecidableEq I]

def frozenVertices (L S : I) : Finset I := (Finset.univ.erase L).erase S

@[simp] theorem mem_frozenVertices (L S i : I) :
    i ∈ frozenVertices L S ↔ i ≠ S ∧ i ≠ L := by
  simp [frozenVertices]

theorem prod_split_two {M : Type*} [CommMonoid M] (L S : I) (hLS : L ≠ S)
    (f : I → M) : (∏ i, f i) = f L * f S * ∏ i ∈ frozenVertices L S, f i := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ L)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase L) f
    (Finset.mem_erase.mpr ⟨hLS.symm,Finset.mem_univ S⟩)]
  exact (mul_assoc _ _ _).symm

theorem graph_product_split (L S : I) (hLS : L ≠ S) (a : I → ℂ) (b : I → I → ℂ)
    (hLL : b L L = 1) (hSS : b S S = 1) :
    (∏ i, a i * ∏ h, b i h) =
      (a L * (∏ h ∈ frozenVertices L S, b L h) *
        (∏ i ∈ frozenVertices L S, b i L) *
        (∏ i ∈ frozenVertices L S, a i * ∏ h ∈ frozenVertices L S, b i h)) *
      (a S * (∏ h ∈ frozenVertices L S, b S h) *
        (∏ i ∈ frozenVertices L S, b i S)) * b L S * b S L := by
  simp_rw [prod_split_two L S hLS]
  simp only [hLL,hSS,one_mul,mul_one]
  simp_rw [Finset.prod_mul_distrib]
  ring

def twoPrimeAssignment (p : I → ℕ) (L S : I) (q r : ℕ) : I → ℕ :=
  Function.update (Function.update p L q) S r

omit [Fintype I] in
@[simp] theorem twoPrimeAssignment_long [Fintype I] (p : I → ℕ) (L S : I) (hLS : L ≠ S) (q r : ℕ) :
    twoPrimeAssignment p L S q r L = q := by
  simp [twoPrimeAssignment,hLS]

omit [Fintype I] in
@[simp] theorem twoPrimeAssignment_short [Fintype I] (p : I → ℕ) (L S : I) (q r : ℕ) :
    twoPrimeAssignment p L S q r S = r := by
  simp [twoPrimeAssignment]

@[simp] theorem twoPrimeAssignment_frozen (p : I → ℕ) (L S : I) (q r : ℕ)
    (i : I) (hi : i ∈ frozenVertices L S) : twoPrimeAssignment p L S q r i = p i := by
  obtain ⟨hiS,hiL⟩ := (mem_frozenVertices L S i).mp hi
  simp [twoPrimeAssignment,hiS,hiL]

def fixedPhase (D : I → I → ℤ) (p : I → ℕ) (χ : (q : ℕ) → MulChar (ZMod q) ℂ)
    (ν : I → ℕ → ℂ) (L S : I) : ℂ :=
  ∏ i ∈ frozenVertices L S, ν i (p i) *
    ∏ h ∈ frozenVertices L S, χ (p i) (p h) ^ D i h

def longUnary (D : I → I → ℤ) (p : I → ℕ) (χ : (q : ℕ) → MulChar (ZMod q) ℂ)
    (ν : I → ℕ → ℂ) (L S : I) (q : ℕ) : ℂ :=
  ν L q * (∏ h ∈ frozenVertices L S, χ q (p h) ^ D L h) *
    (∏ i ∈ frozenVertices L S, χ (p i) q ^ D i L) * fixedPhase D p χ ν L S

def shortUnary (D : I → I → ℤ) (p : I → ℕ) (χ : (q : ℕ) → MulChar (ZMod q) ℂ)
    (ν : I → ℕ → ℂ) (L S : I) (r : ℕ) : ℂ :=
  ν S r * (∏ h ∈ frozenVertices L S, χ r (p h) ^ D S h) *
    (∏ i ∈ frozenVertices L S, χ (p i) r ^ D i S)

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
