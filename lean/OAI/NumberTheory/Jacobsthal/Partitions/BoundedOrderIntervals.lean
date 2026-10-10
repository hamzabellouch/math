import Mathlib

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace ErdosMonotoneQuadrature

theorem bounded_orderConnected_interval {S : Set ℝ} {u v : ℝ}
    (hS : S.OrdConnected) (hne : S.Nonempty) (hsub : S ⊆ Icc u v) :
    ∃ a b : ℝ, u ≤ a ∧ a ≤ b ∧ b ≤ v ∧
      (S = Icc a b ∨ S = Ico a b ∨ S = Ioc a b ∨ S = Ioo a b) := by
  have hb : BddBelow S := ⟨u,fun x hx => (hsub hx).1⟩
  have ha : BddAbove S := ⟨v,fun x hx => (hsub hx).2⟩
  have hu : u ≤ sInf S := le_csInf hne (fun x hx => (hsub hx).1)
  have hv : sSup S ≤ v := csSup_le hne (fun x hx => (hsub hx).2)
  obtain ⟨x,hx⟩ := hne
  have hab : sInf S ≤ sSup S := (csInf_le hb hx).trans (le_csSup ha hx)
  have hc : IsConnected S := ⟨⟨x,hx⟩,hS.isPreconnected⟩
  have hi := mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
    (hc.Ioo_csInf_csSup_subset hb ha) (subset_Icc_csInf_csSup hb ha)
  exact ⟨sInf S,sSup S,hu,hab,hv,hi⟩

theorem orderConnected_measure_discrepancy (μ ν : Measure ℝ) (u v E : ℝ)
    (hE : 0 ≤ E)
    (hinterval : ∀ a b : ℝ, u ≤ a → a ≤ b → b ≤ v →
      |μ.real (Icc a b)-ν.real (Icc a b)| ≤ E ∧
      |μ.real (Ico a b)-ν.real (Ico a b)| ≤ E ∧
      |μ.real (Ioc a b)-ν.real (Ioc a b)| ≤ E ∧
      |μ.real (Ioo a b)-ν.real (Ioo a b)| ≤ E)
    {S : Set ℝ} (hS : S.OrdConnected) (hsub : S ⊆ Icc u v) :
    |μ.real S-ν.real S| ≤ E := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hE
  obtain ⟨a,b,hu,hab,hv,he⟩ := bounded_orderConnected_interval hS hne hsub
  obtain ⟨hcc,hco,hoc,hoo⟩ := hinterval a b hu hab hv
  rcases he with rfl | rfl | rfl | rfl
  · exact hcc
  · exact hco
  · exact hoc
  · exact hoo

end ErdosMonotoneQuadrature

end

end Erdos970

end OAI
