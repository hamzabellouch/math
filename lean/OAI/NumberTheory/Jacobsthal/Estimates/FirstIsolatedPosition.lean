import OAI.NumberTheory.Jacobsthal.Paths.GeometricRegularWords

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FirstIsolatedPosition
open PrimeHistories GeometricRegularWords IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinLabels


theorem first_matching_position {α : Type*} (P : α → Prop) (ps : List α)
    (hex : ∃ p ∈ ps,P p) : ∃ pre p tail,ps=pre++p::tail ∧ P p ∧ ∀ q ∈ pre,¬P q := by
  classical
  induction ps with
  | nil => simp at hex
  | cons p ps ih =>
    by_cases hp : P p
    · exact ⟨[],p,ps,rfl,hp,by simp⟩
    · have ht : ∃ q ∈ ps,P q := by
        obtain ⟨q,hq,hP⟩ := hex
        rcases List.mem_cons.mp hq with rfl | hq
        · exact False.elim (hp hP)
        · exact ⟨q,hq,hP⟩
      obtain ⟨pre,q,tail,he,hq,hpre⟩ := ih ht
      exact ⟨p::pre,q,tail,by rw [List.cons_append,he],hq,by simpa using And.intro hp hpre⟩

theorem geometric_first_isolated {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z) :
    ∃ pre p tail,ps=pre++p::tail ∧
      isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi p) ∧
      ∀ q ∈ pre,¬isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi q) :=
  first_matching_position _ ps (geometric_isolated_prime hw htop hxi z ps hp)
end NumberTheoryLean.FirstIsolatedPosition


end Erdos970

end OAI
