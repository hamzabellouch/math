import OAI.Analysis.LipschitzHilbert.Trees.SourceRestrictedGram

namespace OAI

/-! The exact finite split of a symmetric Gram matrix into comparable
scales and the two orientations of distant scales. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

private theorem scale_dichotomy (a b gap : ℕ) :
    |(a:ℤ)-(b:ℤ)|≤(gap:ℤ) ∨ a+gap+1≤b ∨ b+gap+1≤a := by
  by_cases hab : a≤b
  · have hh : (a:ℤ)-(b:ℤ)≤0 := by omega
    rw [abs_of_nonpos hh]
    omega
  · have hh : 0≤(a:ℤ)-(b:ℤ) := by omega
    rw [abs_of_nonneg hh]
    omega

private theorem scale_entry_split (a b gap : ℕ) (v : ℝ) :
    v=(if |(a:ℤ)-(b:ℤ)|≤(gap:ℤ) then v else 0)+
      (if a+gap+1≤b then v else 0)+(if b+gap+1≤a then v else 0) := by
  by_cases hn : |(a:ℤ)-(b:ℤ)|≤(gap:ℤ)
  · have habs := abs_le.mp hn
    have h1 : ¬a+gap+1≤b := by omega
    have h2 : ¬b+gap+1≤a := by omega
    simp only [hn,h1,h2,ite_true,ite_false,add_zero]
  · rcases (scale_dichotomy a b gap).resolve_left hn with hab | hba
    · have hnot : ¬b+gap+1≤a := by omega
      simp only [hn,hab,hnot,ite_false,ite_true,zero_add,add_zero]
    · have hnot : ¬a+gap+1≤b := by omega
      simp only [hn,hba,hnot,ite_false,ite_true,zero_add]

theorem scale_gram_split {ι : Type*} (S : Finset ι) (level : ι → ℕ)
    (G : ι → ι → ℝ) (hsym : ∀ i j, G i j=G j i) (gap : ℕ) :
    (∑ i∈S, ∑ j∈S, G i j)=
      (∑ i∈S, ∑ j∈S, if |(level i:ℤ)-(level j:ℤ)|≤(gap:ℤ) then G i j else 0)+
        2*(∑ i∈S, ∑ j∈S, if level j+gap+1≤level i then G i j else 0) := by
  have he : (∑ i∈S, ∑ j∈S, G i j)=
      (∑ i∈S, ∑ j∈S, if |(level i:ℤ)-(level j:ℤ)|≤(gap:ℤ) then G i j else 0)+
      (∑ i∈S, ∑ j∈S, if level i+gap+1≤level j then G i j else 0)+
      (∑ i∈S, ∑ j∈S, if level j+gap+1≤level i then G i j else 0) := by
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact scale_entry_split (level i) (level j) gap (G i j)
  have hswap : (∑ i∈S, ∑ j∈S, if level i+gap+1≤level j then G i j else 0)=
      ∑ i∈S, ∑ j∈S, if level j+gap+1≤level i then G i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym]
  rw [he,hswap]
  ring

end LipschitzHilbert

end

end OAI
