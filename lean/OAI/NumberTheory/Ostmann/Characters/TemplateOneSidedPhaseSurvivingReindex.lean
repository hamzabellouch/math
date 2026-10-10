import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseQuotient
import OAI.NumberTheory.Ostmann.Characters.TemplatePivotCollapse

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
variable {I : Type*} [Fintype I] [DecidableEq I]

def survivingTranslationProduct (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (a : ∀ i, ZMod (p i)) (P : ℕ) (s : ℤ) : ℂ :=
  ∏ i, translatedAdditivePhase (a i) (s : ZMod (p i))
    ((P : ZMod (p i)) * Construction.otherProduct p i)

theorem norm_survivingTranslationProduct (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (a : ∀ i, ZMod (p i)) (P : ℕ) (s : ℤ) :
    ‖survivingTranslationProduct p a P s‖ = 1 := by
  rw [survivingTranslationProduct, norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [translatedAdditivePhase, (ZMod.stdAddChar : AddChar (ZMod (p i)) ℂ).norm_apply]

theorem survivingTranslationProduct_mul_conj (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (a : ∀ i, ZMod (p i)) (P : ℕ) (s : ℤ) :
    survivingTranslationProduct p a P s * conj (survivingTranslationProduct p a P s) = 1 := by
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_survivingTranslationProduct,
    one_pow, Complex.ofReal_one]

theorem survivingTranslationProduct_permutation (σ : Equiv.Perm I)
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (a : ∀ i, ZMod (p i)) (P : ℕ) (s : ℤ) :
    survivingTranslationProduct (fun i => p (σ.symm i)) (fun i => a (σ.symm i)) P s =
      survivingTranslationProduct p a P s := by
  have hd (i : I) := otherProduct_reindex σ.symm p i
    (Fact.out : (p (σ.symm i)).Prime).ne_zero
  unfold survivingTranslationProduct
  simp_rw [hd]
  exact σ.symm.prod_comp (fun i => translatedAdditivePhase (a i) (s : ZMod (p i))
    ((P : ZMod (p i)) * Construction.otherProduct p i))

theorem survivingPrimeRows_eq_translation_mul_graph
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (a : ∀ i, ZMod (p i))
    (ν : I → ℂ) (B : I → I → ℤ) (bP : I → ℤ) (P : ℕ) (s : ℤ) :
    (∏ i, survivingPrimeRow p i (χ i) (a i) (ν i) (B i) (bP i) P s) =
      survivingTranslationProduct p a P s *
        primeGraphPhase B p χ (fun i => ν i * χ i (P : ZMod (p i)) ^ bP i) := by
  simp only [survivingPrimeRow, survivingTranslationProduct, primeGraphPhase,
    Finset.prod_mul_distrib]

theorem survivingPrimeRows_permutation (σ : Equiv.Perm I)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (a : ∀ i, ZMod (p i))
    (ν : I → ℂ) (B : I → I → ℤ) (bP : I → ℤ) (P : ℕ) (s : ℤ) :
    (∏ i, survivingPrimeRow (fun i => p (σ.symm i)) i (χ (σ.symm i)) (a (σ.symm i))
      (ν i) (B i) (bP i) P s) =
      survivingTranslationProduct p a P s *
        primeGraphPhase (permutedGraph B σ) p χ
          (fun i => ν (σ i) * χ i (P : ZMod (p i)) ^ bP (σ i)) := by
  rw [survivingPrimeRows_eq_translation_mul_graph, survivingTranslationProduct_permutation]
  congr 1
  simpa only [permutedGraph, Equiv.apply_symm_apply] using
    primeGraphPhase_reindex σ.symm (permutedGraph B σ) p χ
      (fun i => ν (σ i) * χ i (P : ZMod (p i)) ^ bP (σ i))

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
