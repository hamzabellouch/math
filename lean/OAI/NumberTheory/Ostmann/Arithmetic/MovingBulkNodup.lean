import OAI.NumberTheory.Ostmann.Arithmetic.FrozenRegularSupport
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotPolynomials

namespace OAI

/-! # Bulk labels remain distinct throughout the actual coherent sampled tree -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.regularLists_bulk_nodup {σ : Type*} (bulk : σ → Bool)
    {n : ℕ} (T : MovingSlotData σ n) :
    T.RegularCoherent →
    (∀ i, bulk i = true → T.CompensationAbsent i) →
    (T.regularSlots.filter bulk).Nodup →
    ∀ L ∈ T.regularLists, (L.filter bulk).Nodup := by
  induction T with
  | leaf s regular =>
    intro _ _ hn L hL
    simpa only [MovingSlotData.regularLists, MovingSlotData.regularSlots,
      List.mem_singleton.mp hL] using hn
  | node s CL CR U left right ihL ihR =>
    intro hc ha hn
    have hu : U.filter bulk = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro i hi
      cases hb : bulk i with
      | false => simp
      | true => exact False.elim ((ha i hb).1 hi)
    have hn' : (CL.filter bulk ++ CR.filter bulk).Nodup := by
      simpa only [MovingSlotData.regularSlots, List.filter_append] using hn
    have hleft : (left.regularSlots.filter bulk).Nodup := by
      have hp := hc.1.filter bulk
      rw [List.filter_append, hu, List.nil_append] at hp
      exact hp.nodup_iff.mpr (List.nodup_append.mp hn').1
    have hright : (right.regularSlots.filter bulk).Nodup := by
      have hp := hc.2.1.filter bulk
      rw [List.filter_append, hu, List.nil_append] at hp
      exact hp.nodup_iff.mpr (List.nodup_append.mp hn').2.1
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hn
    · rcases List.mem_append.mp hL with hL | hL
      · exact ihL hc.2.2.1 (fun i hi => (ha i hi).2.1) hleft L hL
      · exact ihR hc.2.2.2 (fun i hi => (ha i hi).2.2) hright L hL

end Ostmann

end OAI
