import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfigurationDefs
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateShells

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template Construction Preliminaries HigherBiasSourceRoleBounds
attribute [local instance] Classical.propDecidable

theorem scheduledPrimeShells_pivot {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (i : (schedule k j).Slot) (l : Fin k)
    (hi : (schedule k j).role i = .pivot l.val)
    (a : Fin (sourceWidth cfg m ((schedule k j).role i))) :
    scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j ⟨i,a⟩ =
      boundedRawLogCell E ((cfg.2 l.castSucc).get
        ⟨a.val,by simpa only [hi,sourceWidth_pivot] using a.isLt⟩) := by
  rw [scheduledPrimeShells_eq_origin]
  have hr := scheduledConstituentOrigin_role k (sourceWidth cfg m) j ⟨i,a⟩
  have hp := scheduledConstituentOrigin_position k (sourceWidth cfg m) j ⟨i,a⟩
  rw [hi] at hr
  generalize he : scheduledConstituentOrigin k (sourceWidth cfg m) j ⟨i,a⟩ = x at hr hp ⊢
  rcases x with ⟨⟨r,b⟩,v⟩
  have hw : r = .pivot l := by
    change r.role = .pivot l.val at hr
    cases r with
    | word => contradiction
    | filler => contradiction
    | anchor n c => contradiction
    | pivot n => exact congrArg InitialRole.pivot (Fin.ext (Role.pivot.inj hr))
  subst r
  have hh := configurationPrimeShells_pivot cfg m bulk top E l b
    (Fin.cast (sourceWidth_pivot cfg m l) v)
  apply hh.trans
  congr 2
  apply Fin.ext
  exact hp

theorem scheduledPrimeShells_anchor {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (bulk top E : Finset (PrimeUpTo Q)) (i : (schedule k j).Slot) (l : Fin k) (big : Bool)
    (hi : (schedule k j).role i = .anchor l.val big)
    (a : Fin (sourceWidth cfg m ((schedule k j).role i))) :
    scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j ⟨i,a⟩ =
      boundedRawLogCell E (cfg.1 (anchorCoordinate l big)) := by
  rw [scheduledPrimeShells_eq_origin]
  have hr := scheduledConstituentOrigin_role k (sourceWidth cfg m) j ⟨i,a⟩
  rw [hi] at hr
  generalize he : scheduledConstituentOrigin k (sourceWidth cfg m) j ⟨i,a⟩ = x at hr ⊢
  rcases x with ⟨⟨r,b⟩,v⟩
  have hw : r = .anchor l big := by
    change r.role = .anchor l.val big at hr
    cases r with
    | word => contradiction
    | filler => contradiction
    | pivot n => contradiction
    | anchor n c =>
      obtain ⟨hn,hc⟩ := Role.anchor.inj hr
      subst c
      exact congrArg (fun n => InitialRole.anchor n big) (Fin.ext hn)
  subst r
  exact configurationPrimeShells_anchor cfg m bulk top E l big b v

theorem log_tuple_of_cells {Q : ℕ} (is : List ℤ) (E : Finset (PrimeUpTo Q))
    (q : Fin is.length → PrimeUpTo Q)
    (hq : ∀ a, q a ∈ boundedRawLogCell E (is.get a)) :
    (is.sum : ℝ) ≤ Real.log (characterTupleProduct q : ℝ) ∧
    Real.log (characterTupleProduct q : ℝ) ≤ (is.sum : ℝ) + is.length := by
  rw [log_characterTupleProduct]
  have hs : (∑ a : Fin is.length, (is.get a : ℝ)) = (is.sum : ℝ) := by
    rw [← Int.cast_sum, ← List.sum_ofFn, List.ofFn_get]
  have hc (a : Fin is.length) := (Finset.mem_filter.mp (hq a)).2
  constructor
  · rw [← hs]
    exact Finset.sum_le_sum (fun a _ => (hc a).1)
  · rw [← hs]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => (hc a).2.le)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using hh

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
