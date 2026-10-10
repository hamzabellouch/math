import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction

theorem spectatorList_length_le {n : ℕ} (spectator : PrimeSource)
    (ds : Fin (2*(n/2))→spectator.Sample) :
    (spectatorList spectator ds).length≤n := by
  rw [spectatorList,List.length_ofFn]
  omega

theorem spectatorList_source_mass {n : ℕ} (spectator : PrimeSource)
    (ds : Fin n → spectator.Sample) (hds : ∀i,spectator.law.mass (ds i)≠0) :
    ∀q∈spectatorList spectator ds,∃p:spectator.Sample,p.val=q ∧ spectator.law.mass p≠0 := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact ⟨ds i,rfl,hds i⟩

theorem error_bounds_of_eq {a b a' b' : ℂ} {x y : ℝ}
    (ha : a=a') (hb : b=b') (h : ‖a'-b'‖≤x ∧ ‖a'-b'‖≤y) :
    ‖a-b‖≤x ∧ ‖a-b‖≤y := by
  rw [ha,hb]
  exact h

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
