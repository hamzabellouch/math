import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.TypeTags.Finite
import OAI.NumberTheory.Ostmann.Preliminaries.UniformHomAverage

namespace OAI

/-! # Removing redundant prime powers from uniform giant residue averages -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def externalResidueReduction {m n : ℕ} (h : m ∣ n)
    (z : ZMod n × (ZMod n)ˣ) : ZMod m × (ZMod m)ˣ :=
  ((ZMod.castHom h (ZMod m)) z.1, ZMod.unitsMap h z.2)

noncomputable def primePairResidueReduction {m n : ℕ} (h : m ∣ n)
    (z : (ZMod n)ˣ × (ZMod n)ˣ) : (ZMod m)ˣ × (ZMod m)ˣ :=
  (ZMod.unitsMap h z.1, ZMod.unitsMap h z.2)

private noncomputable def externalReductionHom {m n : ℕ} (h : m ∣ n) :
    (Multiplicative (ZMod n) × (ZMod n)ˣ) →* (Multiplicative (ZMod m) × (ZMod m)ˣ) :=
  (ZMod.castHom h (ZMod m)).toAddMonoidHom.toMultiplicative.prodMap (ZMod.unitsMap h)

private theorem externalReductionHom_surjective {m n : ℕ} [NeZero n] (h : m ∣ n) :
    Function.Surjective (externalReductionHom h) := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective h (Multiplicative.toAdd a)
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective h b
  refine ⟨(Multiplicative.ofAdd x, u), ?_⟩
  exact Prod.ext hx hu

/-- Applies also to a prime-power modulus: all lifts have the same mass.
The integrand may be signed or complex. -/
theorem uniform_external_residue_reduction {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (F : ZMod m × (ZMod m)ˣ → ℂ) :
    (Fintype.card (ZMod n × (ZMod n)ˣ) : ℂ)⁻¹ *
      (∑ z, F (externalResidueReduction h z)) =
    (Fintype.card (ZMod m × (ZMod m)ˣ) : ℂ)⁻¹ * ∑ z, F z := by
  have hh := uniform_hom_average (externalReductionHom h) (externalReductionHom_surjective h)
    (fun z => F (Multiplicative.toAdd z.1, z.2))
  let en : (Multiplicative (ZMod n) × (ZMod n)ˣ) ≃ (ZMod n × (ZMod n)ˣ) :=
    Multiplicative.toAdd.prodCongr (Equiv.refl _)
  let em : (Multiplicative (ZMod m) × (ZMod m)ˣ) ≃ (ZMod m × (ZMod m)ˣ) :=
    Multiplicative.toAdd.prodCongr (Equiv.refl _)
  rw [Fintype.card_congr en, Fintype.card_congr em] at hh
  change (Fintype.card (ZMod n × (ZMod n)ˣ) : ℂ)⁻¹ *
      (∑ z, F (externalResidueReduction h (en z))) =
    (Fintype.card (ZMod m × (ZMod m)ˣ) : ℂ)⁻¹ * ∑ z, F (em z) at hh
  rw [en.sum_comp (fun z => F (externalResidueReduction h z)), em.sum_comp F] at hh
  exact hh

theorem uniform_prime_pair_residue_reduction {m n : ℕ} [NeZero m] [NeZero n]
    (h : m ∣ n) (F : (ZMod m)ˣ × (ZMod m)ˣ → ℂ) :
    (Fintype.card ((ZMod n)ˣ × (ZMod n)ˣ) : ℂ)⁻¹ *
      (∑ z, F (primePairResidueReduction h z)) =
    (Fintype.card ((ZMod m)ˣ × (ZMod m)ˣ) : ℂ)⁻¹ * ∑ z, F z := by
  exact uniform_hom_average ((ZMod.unitsMap h).prodMap (ZMod.unitsMap h))
    (by
      rintro ⟨a, b⟩
      obtain ⟨x, hx⟩ := ZMod.unitsMap_surjective h a
      obtain ⟨y, hy⟩ := ZMod.unitsMap_surjective h b
      exact ⟨(x, y), Prod.ext hx hy⟩) F

end Ostmann

end OAI
