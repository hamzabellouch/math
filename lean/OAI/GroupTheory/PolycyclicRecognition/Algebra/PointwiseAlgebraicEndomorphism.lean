import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialOrbitExterior
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.Algebraic.Integral

namespace OAI

/-! # Local polynomial relations on a finite module give an integral operator -/

noncomputable section
namespace PolycyclicRecognition
open scoped Polynomial
variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

theorem polynomialOrbit_exists_annihilator (T : Module.End K M) (v : M)
    (h : ¬LinearIndependent K (fun i : ℕ => (T ^ i) v)) :
    ∃ p : K[X], p ≠ 0 ∧ Polynomial.aeval T p v = 0 := by
  by_contra! hn
  have hi : Function.Injective (polynomialOrbitMap T v) := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro p hp
    change polynomialOrbitMap T v p = 0 at hp
    change Polynomial.aeval T p v = 0 at hp
    change p = 0
    by_contra hp0
    exact hn p hp0 hp
  have hl := (Polynomial.basisMonomials K).linearIndependent.map'
    (polynomialOrbitMap T v) (LinearMap.ker_eq_bot.mpr hi)
  apply h
  convert hl using 1
  funext i
  change (T ^ i) v = Polynomial.aeval T ((Polynomial.monomial i) 1) v
  rw [Polynomial.aeval_monomial, map_one, one_mul]

section FiniteModule
variable {R N : Type} [CommRing R] [Algebra K R] [AddCommGroup N]
  [Module K N] [Module R N] [IsScalarTower K R N] [Module.Finite R N]

/-- The product of annihilators of a finite module generating set annihilates
all vectors, because the operator commutes with the coefficient ring. -/
theorem integral_endomorphism_of_pointwise_relation (T : Module.End R N)
    (h : ∀ v : N, ∃ p : K[X], p ≠ 0 ∧ Polynomial.aeval T p v = 0) :
    IsIntegral K T := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R N).FG)
  choose p hp hzero using fun i : s => h i.val
  let P : K[X] := ∏ i : s, p i
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hz (i : s) : Polynomial.aeval T P i.val = 0 := by
    have hd : p i ∣ P := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨q, hq⟩ := hd
    rw [hq, mul_comm, map_mul, Module.End.mul_apply, hzero, map_zero]
  have he : Polynomial.aeval T P = 0 := by
    apply LinearMap.ext
    intro x
    have hx : x ∈ Submodule.span R (s : Set N) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact hz ⟨y, hy⟩
    | zero => exact map_zero _
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul r x _ hx => simp only [map_smul, hx]
  exact IsAlgebraic.isIntegral ⟨P, hP, he⟩
end FiniteModule
end PolycyclicRecognition

end

end OAI
