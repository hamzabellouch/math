import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexBands
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexBijection

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

theorem remainingValues_nodup_of_actualCoefficient_ne_zero
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (g : ∀q : ℕ,ZMod q→ℂ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v : ℤ)
    (hx : actualCoefficient sources seed V X G g bins outside l
      (remainingState sources (Template.current seed l) (l+1) giant p u x v)≠0) :
    (remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant x).Nodup := by
  have hs := (actualCoefficient_root_support sources seed V X G g bins outside l _ hx).2.2.2.1
  have hh := remaining_half_pairwise _ _ _ outside
    (Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _)) hs
  have hp := (List.pairwise_append.mp hh).1
  have hprime := remainingValues_prime sources (Template.remainder (l+1) (Template.current seed l)) giant x
  change (remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant x).Pairwise Nat.Coprime at hp
  exact hp.imp_of_mem (fun {a b} ha hb hab he => by
    subst b
    exact (hprime a ha).ne_one (by simpa only [Nat.Coprime,Nat.gcd_self] using hab))

theorem weighted_remainingProduct_eq_band_counterparts (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (hsep : RemainingBandsSeparated sources T giant)
    (x : RemainingSample sources T giant) (hx : (remainingValues sources T giant x).Nodup)
    (hmx : (remainingPrior sources T giant).mass x≠0) (F : RemainingSample sources T giant→ℂ) :
    (∑y,if remainingProduct sources T giant y=remainingProduct sources T giant x then
      ((remainingPrior sources T giant).mass y:ℂ)*F y else 0) =
      ∑e : CounterpartPermutation sources T giant x,
        if PreservesRemainingBands T e.val then
          ((remainingPrior sources T giant).mass
            (reconstructCounterpart sources T giant x e.val e.property):ℂ)*
          F (reconstructCounterpart sources T giant x e.val e.property) else 0 := by
  rw [weighted_remainingProduct_eq_counterparts sources T giant x hx]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hb : PreservesRemainingBands T e.val
  · simp only [hb,ite_true]
  · have hz : (remainingPrior sources T giant).mass
        (reconstructCounterpart sources T giant x e.val e.property)=0 := by
      by_contra hm
      exact hb (reconstructCounterpart_preserves_bands sources T giant hsep x hmx e.val e.property hm)
    simp only [hz,Complex.ofReal_zero,zero_mul,hb,ite_false]

end Ostmann.Construction

end

end OAI
