import OAI.NumberTheory.Jacobsthal.Paths.MovingStopMargins

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FrozenPrimeGroup
open _root_.Finset _root_.Erdos970.Finset FiniteFirstTag ActualSourceTags ActualBinOwners
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.PrimePrefixMass
open StoppedVertexHistory
attribute [local instance] Classical.propDecidable

noncomputable def frozenGroup (R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) (pre tail : List ℕ) :
    Finset (List ℕ) := ((primeBin R xi).filter (aligns a q)).image (fun p => pre++p::tail)

theorem replacement_injective (pre tail : List ℕ) : Function.Injective (fun p : ℕ => pre++p::tail) := by
  intro p q hpq
  exact (List.cons.inj (List.append_cancel_left hpq)).1

theorem mem_frozenGroup (R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) (pre tail ps : List ℕ) :
    ps ∈ frozenGroup R xi a q pre tail ↔
      ∃ p ∈ primeBin R xi,aligns a q p ∧ ps=pre++p::tail := by
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
    obtain ⟨hb,ha⟩ := Finset.mem_filter.mp hp
    exact ⟨p,hb,ha,he.symm⟩
  · rintro ⟨p,hp,ha,rfl⟩
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,ha⟩,rfl⟩

theorem frozenGroup_card (R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) (pre tail : List ℕ) :
    (frozenGroup R xi a q pre tail).card=((primeBin R xi).filter (aligns a q)).card := by
  exact Finset.card_image_of_injective _ (replacement_injective pre tail)

theorem frozenGroup_original_mass (R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) (pre tail : List ℕ) :
    (∑ ps ∈ frozenGroup R xi a q pre tail,prefixWeight ps)=
      ((pre.prod*tail.prod:ℕ):ℝ)⁻¹ * ∑ p ∈ (primeBin R xi).filter (aligns a q),(p:ℝ)⁻¹ := by
  rw [frozenGroup,Finset.sum_image,Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro p _hp
    rw [prefixWeight_product,TagBelowStopWindow.replacement_product,Nat.cast_mul,mul_inv_rev]
  · intro p _ q _ hpq
    exact replacement_injective pre tail hpq

theorem frozenGroup_owner_card (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) (pre tail : List ℕ)
    (hY : 0 ≤ Y) (hw : 1 < w) (ho : owner Y w Cs eta R xi a = some q) :
    (1-eta)*((primeBin R xi).card:ℝ) ≤ (frozenGroup R xi a q pre tail).card := by
  rw [frozenGroup_card]
  exact (actual_owner_witness hY hw a ho).2

theorem frozenGroup_product_sum (R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) (pre tail : List ℕ)
    (F : ℕ → ℝ) :
    (∑ ps ∈ frozenGroup R xi a q pre tail,F ps.prod)=
      ∑ p ∈ (primeBin R xi).filter (aligns a q),F (p*(pre.prod*tail.prod)) := by
  rw [frozenGroup,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p _hp
    rw [TagBelowStopWindow.replacement_product]
  · intro p _ q _ hpq
    exact replacement_injective pre tail hpq
end NumberTheoryLean.FrozenPrimeGroup

end

end Erdos970

end OAI
