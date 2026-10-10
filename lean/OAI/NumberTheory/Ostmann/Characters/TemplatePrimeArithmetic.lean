import OAI.NumberTheory.Ostmann.Characters.TemplateArithmeticSupport
import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeExposure
import OAI.NumberTheory.Ostmann.Characters.TemplateWordMaps

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
open Construction Preliminaries BinaryExposure FrequencyExposure BinaryPriorExposure
attribute [local instance] Classical.propDecidable

def chosenPrimeWords {N:ℕ} (k j:ℕ) (x:BinaryHaar.Leaves (PrimeUpTo N) j) :
    WordSlot k j→ℤ := fun i=>((wordTreeEquiv (G:=PrimeUpTo N) k j).symm x i).val

theorem actual_prime_arithmetic_bound (ε:ℝ) (hε:0<ε) :
    ∃ A:NNReal,0<A ∧ ∀ k K R N:ℕ,∀ [NeZero R],∀ J:Type*,∀ [Fintype J],
      ∀ E:List Bool→Finset (PrimeUpTo N),∀ hE:∀p,0<primeShellMass (E p),
      ∀ L:List Bool→J→ℕ,(∀p j,R^(K+2)≤L p j)→
      (∀p q,q∈E p→∃j,L p j≤q.val ∧ q.val≤2*L p j)→
      (∀p q,q∈E p→q.val.Coprime (R^(K+2)))→
      ∀ d:List Bool→Data R,∀ j:ℕ,j≤K→∀ p (h:PairedKnownStates k R),
      ∀ C C':(schedule k j).Slot→ℤ,
      ContextMatches k R j h.1 C→ ContextMatches k R j h.2 C'→
      BinaryPriorExposure.mean (fun p=>primeShellPrior (E p) (hE p)) j p
        (fun x=>if ArithmeticSupport k R d j p C C' (chosenPrimeWords k j x) then 1 else 0) ≤
      (BinaryPriorExposure.cost
        (fun p=>primeResidueCost (Q:=R^(K+2)) (J:=J) (E p) (hE p)) j p:ℝ)*
        ((budget A ε (fun p=>ambientData K R (d p)) j p).value:ℝ) := by
  obtain ⟨A,hA,hbound⟩ := actual_prime_leaf_bound ε hε
  refine ⟨A,hA,?_⟩
  intro k K R N _ J _ E hE L hL hcover hcop d j hj p h C C' hc hc'
  refine le_trans ?_ (hbound k K R N J E hE L hL hcover hcop d j p h)
  apply mean_mono_on_support (fun p=>primeShellPrior (E p) (hE p))
    (fun p q=>q∈E p)
    (by intro p q hq; simp only [primeShellPrior_mass,ite_eq_right hq,zero_div])
  intro x hx
  by_cases hs:ArithmeticSupport k R d j p C C' (chosenPrimeWords k j x)
  · have hcopx : AllLeaves (fun (_:List Bool) (q:PrimeUpTo N)=>q.val.Coprime (R^(K+2))) j p x :=
      allLeaves_mono _ _ (fun p q hq=>hcop p q hq) j p x hx
    let w := (wordTreeEquiv (G:=PrimeUpTo N) k j).symm x
    have hw (i:WordSlot k j) : (w i).val.Coprime (R^(K+2)) := by
      have he := (wordTreeEquiv_allLeaves (fun q:PrimeUpTo N=>q.val.Coprime (R^(K+2))) k j p w).mp
      apply he
      simpa only [w,Equiv.apply_symm_apply] using hcopx
    let ξ : WordSlot k j→(ZMod (R^(K+2)))ˣ := fun i=>primeUnitResidue (R^(K+2)) (w i)
    have hξ (i:WordSlot k j) : (chosenPrimeWords k j x i:ZMod (R^(K+2)))=ξ i := by
      simp only [chosenPrimeWords,Int.cast_natCast,ξ,coe_primeUnitResidue _ _ (hw i)]
      rfl
    have he := arithmeticSupport_implies_leafAdmissible k K R d j hj p h C C'
      (chosenPrimeWords k j x) ξ hξ hc hc' hs
    have hmap : wordTreeEquiv (G:=(ZMod (R^(K+2)))ˣ) k j ξ=
        BinaryPriorExposure.map (fun _=>primeUnitResidue (R^(K+2))) j p x := by
      simpa only [w,Equiv.apply_symm_apply] using
        wordTreeEquiv_map (primeUnitResidue (R^(K+2))) k j p w
    rw [hmap] at he
    simp only [ite_eq_left hs,ite_eq_left he,le_refl]
  · simp only [ite_eq_right hs]
    split_ifs <;> norm_num

end Ostmann.Characters.Template

end

end OAI
