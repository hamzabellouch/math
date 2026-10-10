import OAI.Analysis.CircleDomains.Rigidity.LipschitzTracePairs
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! Changing one coordinate inside countably many sets where the other
coordinate is constant preserves the null-area trace-pair condition. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem pair_null_of_countable_constant_cover
    {X : Type*} {T : Set X} (S : ℕ → Set X) (u v w : X → ℝ)
    (hold : volume ((fun x => (u x, v x)) '' T) = 0)
    (hsame : ∀ x ∈ T, x ∉ ⋃ n, S n → w x = v x)
    (hconstant : ∀ n, ∃ a : ℝ, ∀ x ∈ T ∩ S n, u x = a) :
    volume ((fun x => (u x, w x)) '' T) = 0 := by
  choose a ha using hconstant
  have hline (n : ℕ) : volume (({a n} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    change (volume.prod volume) _ = 0
    rw [Measure.prod_prod, measure_singleton, zero_mul]
  have hunion : volume (⋃ n, ({a n} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 :=
    measure_iUnion_null hline
  apply measure_mono_null (t := ((fun x => (u x, v x)) '' T) ∪
    ⋃ n, ({a n} : Set ℝ) ×ˢ (univ : Set ℝ)) ?_ (measure_union_null hold hunion)
  rintro _ ⟨x, hx, rfl⟩
  by_cases hs : x ∈ ⋃ n, S n
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hs
    exact Or.inr (mem_iUnion.mpr ⟨n, by simp only [mem_prod, mem_singleton_iff, mem_univ, and_true]; exact ha n x ⟨hx, hn⟩⟩)
  · exact Or.inl ⟨x, hx, by simp only [hsame x hx hs]⟩

end CircleDomainRigidity

end

end OAI
