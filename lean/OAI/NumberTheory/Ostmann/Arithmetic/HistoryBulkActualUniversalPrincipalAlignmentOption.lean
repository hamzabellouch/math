import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorPresent

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

theorem mapped_option_present_eq_elim {α β : Type*} (s : Option α) (f : α→β)
    (F : (s.map f).isSome=true → ℂ) (G : α→ℂ)
    (h : ∀hs,F hs=G (s.get (by simpa only [Option.isSome_map] using hs))) :
    (if hs : (s.map f).isSome=true then F hs else 0)=s.elim 0 G := by
  cases s with
  | none => simp only [Option.map_none,Option.isSome_none,Bool.false_eq_true,dite_false,Option.elim_none]
  | some a =>
    have hh := h (by simp only [Option.map_some,Option.isSome_some])
    simpa only [Option.map_some,Option.isSome_some,dite_true,Option.get_some,Option.elim_some] using hh

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
