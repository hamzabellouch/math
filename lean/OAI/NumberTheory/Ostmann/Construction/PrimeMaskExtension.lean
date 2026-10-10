import OAI.NumberTheory.Ostmann.Construction.TailSieveMasks
import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueFamily

namespace OAI

/-! # Completing the regular mask family without changing sampled primes -/
namespace Ostmann
open scoped Classical

noncomputable def primeMaskExtension (P : Finset ℕ)
    (sets : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) : Finset (ZMod p) :=
  if p ∈ P then sets p else {0}

theorem primeMaskExtension_eq (P : Finset ℕ) (sets : ∀ p : ℕ, Finset (ZMod p))
    (p : ℕ) (hp : p ∈ P) : primeMaskExtension P sets p = sets p := by
  simp only [primeMaskExtension, ite_eq_left hp]

theorem primeMaskExtension_data (P : Finset ℕ) (sets : ∀ p : ℕ, Finset (ZMod p))
    (hsets : ∀ p ∈ P, (sets p).Nonempty ∧ (sets p).card < p)
    (p : ℕ) (hp : p.Prime) :
    (primeMaskExtension P sets p).Nonempty ∧ (primeMaskExtension P sets p).card < p := by
  by_cases hmem : p ∈ P
  · rw [primeMaskExtension_eq P sets p hmem]
    exact hsets p hmem
  · simp only [primeMaskExtension, ite_eq_right hmem, Finset.singleton_nonempty,
      Finset.card_singleton, true_and]
    exact hp.one_lt

theorem tailPrimeMaskExtension_data {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hdis : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    ∀ p, p.Prime →
      (primeMaskExtension P (tailDensityMask A N) p).Nonempty ∧
      (primeMaskExtension P (tailDensityMask A N) p).card < p := by
  apply primeMaskExtension_data P (tailDensityMask A N)
  intro p hp
  let : NeZero p := ⟨(hP p hp).ne_zero⟩
  exact ⟨tailDensityMask_nonempty hA N p (hP p hp).pos,
    tailDensityMask_card_lt hB N p (hP p hp).pos (hdis p hp)⟩

theorem normalizedResidueFamily_primeMaskExtension (P : Finset ℕ)
    (sets : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) (hp : p ∈ P) :
    normalizedResidueFamily (primeMaskExtension P sets) p = normalizedResidueFamily sets p := by
  unfold normalizedResidueFamily
  split
  · rfl
  · rw [primeMaskExtension_eq P sets p hp]

end Ostmann

end OAI
