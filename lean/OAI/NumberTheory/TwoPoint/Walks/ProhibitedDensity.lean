import OAI.NumberTheory.TwoPoint.Walks.ProhibitedCatalogEncoding

namespace OAI

/-! Density of the actual deleted event, with all finite catalog costs included. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- The arithmetic data used by the prohibited-word argument. -/
structure ProhibitedPrimeFamily (h J M : ℕ) where
  P : Finset ℕ
  Q : Finset ℕ
  pairs : Finset (ℕ × ℕ)
  primeP : ∀ p ∈ P, p.Prime
  primeQ : ∀ p ∈ Q, p.Prime
  disjoint : Disjoint P Q
  excluded : ∀ p ∈ P, ¬p ∣ h
  tuple_squarefree : ∀ dq ∈ pairs, Squarefree dq.1
  padding_squarefree : ∀ dq ∈ pairs, Squarefree dq.2
  tuple_card : ∀ dq ∈ pairs, dq.1.primeFactors.card = J
  padding_card : ∀ dq ∈ pairs, dq.2.primeFactors.card ≤ M
  tuple_pool : ∀ dq ∈ pairs, dq.1.primeFactors ⊆ P
  padding_pool : ∀ dq ∈ pairs, dq.2.primeFactors ⊆ Q

namespace ProhibitedPrimeFamily

variable {h J M : ℕ} (F : ProhibitedPrimeFamily h J M)

lemma prime (p : ↥(F.P ∪ F.Q)) : p.val.Prime := by
  rcases mem_union.mp p.property with hp | hp
  · exact F.primeP _ hp
  · exact F.primeQ _ hp

lemma whole_squarefree (dq : ℕ × ℕ) (hdq : dq ∈ F.pairs) : Squarefree (dq.2 * dq.1) := by
  apply (Nat.squarefree_mul ?_).mpr
  · exact ⟨F.padding_squarefree _ hdq, F.tuple_squarefree _ hdq⟩
  · apply (Nat.disjoint_primeFactors (F.padding_squarefree _ hdq).ne_zero
      (F.tuple_squarefree _ hdq).ne_zero).mp
    exact F.disjoint.symm.mono (F.padding_pool _ hdq) (F.tuple_pool _ hdq)

lemma support_subset (s : ℕ) (c : ProhibitedCatalog F.pairs h s) :
    wordDivisorPrimeSupport (decodeStepWord c.val) ⊆ F.P ∪ F.Q := by
  intro p hp
  obtain ⟨a, ha, hpa⟩ := mem_biUnion.mp hp
  have hdq := c.property.1.2.2.1 a (List.mem_toFinset.mp ha)
  rw [Nat.primeFactors_mul (F.padding_squarefree _ hdq).ne_zero
    (F.tuple_squarefree _ hdq).ne_zero, mem_union] at hpa
  rcases hpa with hpa | hpa
  · exact mem_union_right _ (F.padding_pool _ hdq hpa)
  · exact mem_union_left _ (F.tuple_pool _ hdq hpa)

noncomputable def residueLaw (B : ℕ) (hB : ∀ p ∈ F.P ∪ F.Q, p ≤ B) :
    FiniteLaw (↥(F.P ∪ F.Q) → Fin B) :=
  FiniteLaw.independent (fun p => uniformResidueLaw B p.val (F.prime p).pos (hB _ p.property))

def deletedEvent (s B : ℕ) (x : ↥(F.P ∪ F.Q) → Fin B) : Prop :=
  ∃ c : ProhibitedCatalog F.pairs h s,
    ResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h (decodeStepWord c.val)
      (fun p => ((x p).val : ZMod p.val))

/-- The finite-residue event is precisely the manuscript's prohibited-site
predicate at any common integer lift of those same coordinates. -/
lemma deletedEvent_iff (s B : ℕ) (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    F.deletedEvent s B x ↔ ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs) n := by
  apply prohibited_residue_catalog_iff (fun p : ↥(F.P ∪ F.Q) => p.val) F.pairs h s _ n hn
    F.whole_squarefree
  intro c q hq
  exact ⟨⟨q, F.support_subset s c hq⟩, rfl⟩

/-- No code count or numerical assignment sum is left implicit here. -/
theorem probability_bound (s B H : ℕ)
    (hB : ∀ p ∈ F.P ∪ F.Q, p ≤ B)
    (hVP : 1 ≤ primeHarmonicMass F.P) (hH : 0 < H) (hBone : 1 ≤ B)
    (hlo : ∀ p ∈ F.P, H ≤ p) :
    (F.residueLaw B hB).probability (F.deletedEvent s B) ≤
      badCatalogCost s (s * (J + M)) (primeHarmonicMass F.P) (primeHarmonicMass F.Q) *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  have hc : ∀ c : ProhibitedCatalog F.pairs h s,
      ∀ q ∈ wordDivisorPrimeSupport (decodeStepWord c.val),
      ∃ p : ↥(F.P ∪ F.Q), p.val = q := by
    intro c q hq
    exact ⟨⟨q, F.support_subset s c hq⟩, rfl⟩
  exact (prohibited_residue_probability_le_catalog B (fun p : ↥(F.P ∪ F.Q) => p.val)
    Subtype.val_injective (fun p => (F.prime p).pos) (fun p => hB _ p.property)
    F.pairs h s hc).trans
      (prohibitedCatalog_reciprocal_bound F.pairs F.P F.Q h s J M
        F.tuple_squarefree F.padding_squarefree F.tuple_card F.padding_card
        F.tuple_pool F.padding_pool F.disjoint F.excluded F.primeP hVP
        H B hH hBone hlo (fun p hp => hB p (mem_union_left _ hp)))

end ProhibitedPrimeFamily

open Filter

/-- The density assertion of `q:bad`, proved from the actual pair family
and independent uniform residues, with the published prime estimates isolated
as their numerical mass and scale consequences. -/
theorem eventually_prohibited_density (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h s J M B H : ℕ) (F : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ F.P ∪ F.Q, p ≤ B),
      1 ≤ s → (s : ℝ) ≤ L ^ (1 / 10 : ℝ) →
      ((s * (J + M) : ℕ) : ℝ) ≤ C * s * Real.log L →
      1 ≤ primeHarmonicMass F.P →
      primeHarmonicMass F.P ≤ L ^ (2 : ℕ) → primeHarmonicMass F.Q ≤ L ^ (2 : ℕ) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → 1 ≤ B → (B : ℝ) ≤ Real.exp L →
      (∀ p ∈ F.P, H ≤ p) →
      (F.residueLaw B hB).probability (F.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  filter_upwards [eventually_badCatalog_decay C hC] with L hdecay
  intro h s J M B H F hB hs hsupper hslots hVP hPupper hQupper hH hBone hBupper hlo
  have hHpos : 0 < H := by
    exact_mod_cast (Real.exp_pos _).trans_le hH
  exact hdecay s (s * (J + M)) (primeHarmonicMass F.P) (primeHarmonicMass F.Q)
    H B ((F.residueLaw B hB).probability (F.deletedEvent s B)) hs hsupper hslots
    (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity)
    hPupper hQupper hH (by exact_mod_cast hBone) hBupper
    (F.probability_bound s B H hB hVP hHpos hBone hlo)

end TwoPointCorrelations

end OAI
