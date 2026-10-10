import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupportPropagationBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem CurrentAtomSupport.paired_of_reversal {k j : ℕ} (hj:j<k)
    {P s v w : ℤ} {hL hR : CopiedState k j} {y : OutsideState k j}
    (hl : CurrentAtomSupport k j v (sourceState k j P hL y))
    (hr : CurrentAtomSupport k j w (sourceState k j P hR y)) (hs : s≠0)
    (he : v*(∏i,hR i)-w*(∏i,hL i)=s*P)
    (hroot : ∀i,IsCoprime s (pairedState k j hL hR y i)) :
    CurrentAtomSupport k (j+1) s (pairedState k j hL hR y) := by
  have hcross (i t : {i:(schedule k j).Slot // (schedule k j).IsCopied j i}) :
      IsCoprime (hL i) (hR t) := by
    apply coprime_cross_of_reversal (Finset.dvd_prod_of_mem hL (Finset.mem_univ i))
      (Finset.dvd_prod_of_mem hR (Finset.mem_univ t)) _ (hl.copied_pivot_coprime hj i) he
    exact (hroot (.inl (i,true))).symm
  refine ⟨hs,?_,?_,hroot⟩
  · rintro (⟨i,b⟩|i)
    · cases b
      · exact hr.copied_pos i
      · exact hl.copied_pos i
    · exact hl.outside_pos i
  · intro a b hne
    rcases a with ⟨i,bi⟩|i <;> rcases b with ⟨t,bt⟩|t
    · cases bi <;> cases bt
      · exact hr.copied_pairwise (fun heq => hne (by cases heq; rfl))
      · exact (hcross t i).symm
      · exact hcross i t
      · exact hl.copied_pairwise (fun heq => hne (by cases heq; rfl))
    · cases bi
      · exact hr.copied_outside_coprime i t
      · exact hl.copied_outside_coprime i t
    · cases bt
      · exact (hr.copied_outside_coprime t i).symm
      · exact (hl.copied_outside_coprime t i).symm
    · exact hl.outside_pairwise (fun heq => hne (by cases heq; rfl))

theorem CurrentAtomSupport.paired_of_reversal_prime_factors {k j : ℕ} (hj:j<k)
    {P s v w : ℤ} {hL hR : CopiedState k j} {y : OutsideState k j}
    (hl : CurrentAtomSupport k j v (sourceState k j P hL y))
    (hr : CurrentAtomSupport k j w (sourceState k j P hR y)) (hs : s≠0)
    (he : v*(∏i,hR i)-w*(∏i,hL i)=s*P)
    (hlarge : ∀i,∀q:ℕ,Nat.Prime q → q∣(pairedState k j hL hR y i).natAbs → s.natAbs<q) :
    CurrentAtomSupport k (j+1) s (pairedState k j hL hR y) :=
  hl.paired_of_reversal hj hr hs he (fun i => isCoprime_of_prime_factors_large hs (hlarge i))

end Ostmann.Characters.Template

end

end OAI
