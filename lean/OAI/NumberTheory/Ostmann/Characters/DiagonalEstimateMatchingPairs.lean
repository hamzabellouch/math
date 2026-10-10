import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateRootPairs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Ostmann.Construction Ostmann.Preliminaries TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable

theorem harmonic_root_pairs_eq_matching
    {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] {N : ℕ}
    (E : I→Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (F : (I→PrimeUpTo N)→K→ℂ)
    (hinj : ∀f,(productPrior (fun i=>primeShellPrior (E i) (hE i))).mass f≠0 →
      ∀s,F f s≠0 → Function.Injective (fun i=>(f i).val)) :
    let μ := productPrior (fun i=>primeShellPrior (E i) (hE i))
    (∑f,∑g,((μ.mass f*μ.mass g:ℝ):ℂ)*
      (if (∏i,(g i).val)=(∏i,(f i).val) then ∑s,F f s*conj (F g s) else 0)) =
      matchedRootContribution E hE Finset.univ F := by
  let μ := productPrior (fun i=>primeShellPrior (E i) (hE i))
  have hz (f : I→PrimeUpTo N) (hf : ¬ Function.Injective (fun i=>(f i).val)) :
      μ.mass f=0 ∨ ∀s,F f s=0 := by
    by_cases hm : μ.mass f=0
    · exact Or.inl hm
    exact Or.inr (fun s => by
      by_contra hs
      exact hf (hinj f hm s hs))
  change (∑f,∑g,((μ.mass f*μ.mass g:ℝ):ℂ)*
      (if (∏i,(g i).val)=(∏i,(f i).val) then ∑s,F f s*conj (F g s) else 0)) = _
  calc
    _ = ∑f,∑g,if Function.Injective (fun i=>(f i).val) ∧
        Function.Injective (fun i=>(g i).val) ∧ (∏i,(g i).val)=(∏i,(f i).val) then
          (μ.mass f:ℂ)*(μ.mass g:ℂ)*(∑s,F f s*conj (F g s)) else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      apply Finset.sum_congr rfl
      intro g hg
      by_cases hfi : Function.Injective (fun i=>(f i).val)
      · by_cases hgi : Function.Injective (fun i=>(g i).val)
        · simp only [hfi,hgi,true_and,Complex.ofReal_mul]
          split_ifs <;> simp
        · rcases hz g hgi with hm | hw
          · simp [hm,hgi]
          · simp [hw,hgi]
      · rcases hz f hfi with hm | hw
        · simp [hm,hfi]
        · simp [hw,hfi]
    _ = ∑f,if Function.Injective (fun i=>(f i).val) then
        ∑e:Equiv.Perm I,(μ.mass f:ℂ)*(μ.mass (f ∘ e):ℂ)*
          (∑s,F f s*conj (F (f ∘ e) s)) else 0 :=
      diagonal_prior_sum_eq_permutations E E hE hE (fun f g=>∑s,F f s*conj (F g s))
    _ = ∑f,∑e:Equiv.Perm I,((μ.mass f*μ.mass (f ∘ e):ℝ):ℂ)*
        (∑s,F f s*conj (F (f ∘ e) s)) := by
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hfi : Function.Injective (fun i=>(f i).val)
      · simp only [hfi,ite_true,Complex.ofReal_mul]
      · rcases hz f hfi with hm | hw
        · simp [hm,hfi]
        · simp [hw,hfi]
    _ = matchedRootContribution E hE Finset.univ F := by
      unfold matchedRootContribution
      simp only [Finset.mul_sum,mul_assoc]
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_comm

end Ostmann.Characters.DiagonalEstimate

end

end OAI
