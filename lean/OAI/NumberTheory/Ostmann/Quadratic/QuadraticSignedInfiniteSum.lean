import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSignedFrequencyBijection

namespace OAI

/-! # Exact infinite signed-frequency coordinates for the first transform -/

namespace Ostmann

open scoped Classical BigOperators

abbrev QuadraticOddKernel := {b : ℕ+ // Odd (b : ℕ) ∧ Squarefree (b : ℕ)}
abbrev QuadraticFrequencyIndex := ({1, -1, 2, -2} : Finset ℤ) × (QuadraticOddKernel × ℕ+)

def quadraticFrequencyValue (z : QuadraticFrequencyIndex) : ℤ :=
  (z.1 : ℤ) * (z.2.2 : ℕ) ^ 2 * (z.2.1.val : ℕ)

theorem quadraticFrequencyValue_injective : Function.Injective quadraticFrequencyValue := by
  intro z w h
  obtain ⟨ha, hc, hb⟩ := quadratic_signed_coordinates_injective z.1.property w.1.property
    z.2.2.property w.2.2.property z.2.1.property.1 w.2.1.property.1
    z.2.1.property.2 w.2.1.property.2 h
  apply Prod.ext (Subtype.ext ha)
  apply Prod.ext
  · exact Subtype.ext (Subtype.ext hb)
  · exact Subtype.ext hc

theorem quadraticFrequencyValue_range :
    Set.range quadraticFrequencyValue = {h : ℤ | h ≠ 0} := by
  ext h
  constructor
  · rintro ⟨z, rfl⟩
    have ha : (z.1 : ℤ) ≠ 0 := by
      have hm := z.1.property
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm | hm <;> rw [hm] <;> norm_num
    have hc : ((z.2.2 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast z.2.2.property.ne'
    have hb : ((z.2.1.val : ℕ) : ℤ) ≠ 0 := by exact_mod_cast z.2.1.val.property.ne'
    exact mul_ne_zero (mul_ne_zero ha (pow_ne_zero 2 hc)) hb
  · intro hh
    obtain ⟨a, ha, c, hc, b, hb, he⟩ := quadratic_signed_frequency_coordinates hh (le_refl h.natAbs)
    have hc₀ : 0 < c := (Finset.mem_Icc.mp hc).1
    obtain ⟨hr, hbo, hbs⟩ := Finset.mem_filter.mp hb
    have hb₀ : 0 < b := (Finset.mem_Icc.mp hr).1
    refine ⟨(⟨a, ha⟩, (⟨⟨b, hb₀⟩, hbo, hbs⟩, ⟨c, hc₀⟩)), ?_⟩
    exact he.symm

theorem quadratic_signed_tsum (F : ℤ → ℂ) (hzero : F 0 = 0) :
    (∑' h : ℤ, F h) = ∑' z : QuadraticFrequencyIndex, F (quadraticFrequencyValue z) := by
  symm
  apply quadraticFrequencyValue_injective.tsum_eq
  intro h hh
  rw [quadraticFrequencyValue_range]
  intro hz
  exact hh (hz ▸ hzero)

theorem quadratic_signed_summable (F : ℤ → ℂ) (hF : Summable F) :
    Summable (fun z : QuadraticFrequencyIndex => F (quadraticFrequencyValue z)) :=
  hF.comp_injective quadraticFrequencyValue_injective

theorem quadratic_signed_tsum_iterated (F : ℤ → ℂ) (hzero : F 0 = 0) (hF : Summable F) :
    (∑' h : ℤ, F h) =
      ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑' b : QuadraticOddKernel, ∑' c : ℕ+,
        F (a * (c : ℕ) ^ 2 * (b.val : ℕ)) := by
  rw [quadratic_signed_tsum F hzero]
  have hs := quadratic_signed_summable F hF
  rw [hs.tsum_prod]
  have he (a : ({1, -1, 2, -2} : Finset ℤ)) :
      (∑' bc : QuadraticOddKernel × ℕ+, F (quadraticFrequencyValue (a, bc))) =
        ∑' b : QuadraticOddKernel, ∑' c : ℕ+,
          F ((a : ℤ) * (c : ℕ) ^ 2 * (b.val : ℕ)) :=
    (hs.prod_factor a).tsum_prod
  simp_rw [he]
  exact Finset.tsum_subtype ({1, -1, 2, -2} : Finset ℤ)
    (fun a : ℤ => ∑' b : QuadraticOddKernel, ∑' c : ℕ+,
      F (a * (c : ℕ) ^ 2 * (b.val : ℕ)))

end Ostmann

end OAI
