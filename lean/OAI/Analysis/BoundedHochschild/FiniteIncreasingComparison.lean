import OAI.Analysis.BoundedHochschild.FiniteProjectionExtension

namespace OAI

/-!
# Increasing limits of subequivalent projections

Ringrose, *Lectures on the trace in a finite von Neumann algebra*, Lemma 5.1:
an increasing supremum of projections subequivalent to a fixed finite
projection is still subequivalent to it. The proof aligns successive partial
isometries inside the finite corner and then takes their chain supremum.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Increasing limits preserve subequivalence to a finite projection. -/
theorem finite_increasing_subequivalence (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (p : ℕ → M) (hmono : Monotone p)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q) :
    ∃ v : PartialIso M, v.final ≤ q ∧ (∀ n, p n ≤ v.initial) ∧
      ∀ r : M, IsStarProjection r → (∀ n, p n ≤ r) → v.initial ≤ r := by
  classical
  choose b hb using hembed
  let S (n : ℕ) := {v : PartialIso M // v.initial = p n ∧ v.final ≤ q}
  have hnext (n : ℕ) (v : S n) : ∃ w : S (n + 1), v.val ≤ w.val := by
    have hle : v.val.initial ≤ (b (n + 1)).initial := by
      rw [v.property.1, (hb (n + 1)).1]
      exact hmono (Nat.le_succ n)
    obtain ⟨w, hvw, hwi, hwf⟩ := finite_partialIso_extension e hq hfinite
      v.val (b (n + 1)) hle v.property.2 (hb (n + 1)).2
    exact ⟨⟨w, hwi.trans (hb (n + 1)).1, hwf⟩, hvw⟩
  choose step hstep using hnext
  let a : (n : ℕ) → S n := fun n => Nat.rec ⟨b 0, hb 0⟩ (fun n v => step n v) n
  let f : ℕ → PartialIso M := fun n => (a n).val
  have hfmono : Monotone f := monotone_nat_of_le_succ fun n => hstep n (a n)
  have hfi (n : ℕ) : (f n).initial = p n := (a n).property.1
  have hff (n : ℕ) : (f n).final ≤ q := (a n).property.2
  obtain ⟨v, hupper, _, hi, hf⟩ := exists_partialIso_chain_supremum e (Set.range f)
    hfmono.isChain_range (Set.range_nonempty f)
  refine ⟨v, hf q hq (by rintro _ ⟨n, rfl⟩; exact hff n), ?_, ?_⟩
  · intro n
    rw [← hfi n]
    exact (hupper _ ⟨n, rfl⟩).1
  · intro r hr hb
    apply hi r hr
    rintro _ ⟨n, rfl⟩
    rw [hfi n]
    exact hb n

/-- Ringrose's Lemma 5.1 with the supremum specified in advance. -/
theorem finite_subequivalence_at_supremum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q s : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (hs : IsStarProjection s) (p : ℕ → M) (hmono : Monotone p)
    (hembed : ∀ n, ∃ v : PartialIso M, v.initial = p n ∧ v.final ≤ q)
    (hupper : ∀ n, p n ≤ s)
    (hleast : ∀ r : M, IsStarProjection r → (∀ n, p n ≤ r) → s ≤ r) :
    ∃ v : PartialIso M, v.initial = s ∧ v.final ≤ q := by
  obtain ⟨v, hvq, hvupper, hvleast⟩ := finite_increasing_subequivalence e hq hfinite
    p hmono hembed
  exact ⟨v, le_antisymm (hvleast s hs hupper)
    (hleast v.initial v.initial_proj hvupper), hvq⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
