import Mathlib
import OAI.Geometry.HyperbolicGroups.MacroCycle
import OAI.Geometry.HyperbolicGroups.CycleDecomposition

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.MacroGraph

def graph : SimpleGraph Vertex where
  Adj := Adjacent
  symm := ⟨fun _ _ => adjacent_symm⟩
  loopless := ⟨fun _ adjacent => adjacent_ne adjacent rfl⟩

/-- The actual vertex-simple macro polygon obtained from a library cycle. -/
def ofCycle {u : Vertex} (p : graph.Walk u u) (hp : p.IsCycle) : Polygon where
  n := p.length
  vertex i := p.getVert i.val
  next := finRotate p.length
  injective := by
    intro i j h
    apply Fin.ext
    exact hp.getVert_injOn' (by simpa using Nat.le_sub_one_of_lt i.isLt)
      (by simpa using Nat.le_sub_one_of_lt j.isLt) h
  adjacent := by
    intro i
    have : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
    have hone : ((1 : Fin p.length) : ℕ) = 1 := by
      change 1 % p.length = 1
      exact Nat.mod_eq_of_lt (by have := hp.three_le_length; omega)
    have h := p.adj_getVert_succ i.isLt
    change Adjacent (p.getVert i.val) (p.getVert (i.val + 1)) at h
    change Adjacent (p.getVert i.val) (p.getVert (finRotate p.length i).val)
    rw [finRotate_apply,Fin.val_add]
    by_cases hi : i.val + 1 < p.length
    · simpa only [hone,
        Nat.mod_eq_of_lt hi] using h
    · have he : i.val + 1 = p.length := by omega
      simpa only [hone,
        he,Nat.mod_self,SimpleGraph.Walk.getVert_length,SimpleGraph.Walk.getVert_zero] using h
  no_backtrack := by
    intro i he
    have : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
    simp only [finRotate_apply] at he
    have hval := congrArg Fin.val he
    have h3 := hp.three_le_length
    have hone : ((1 : Fin p.length) : ℕ) = 1 := by
      change 1 % p.length = 1
      exact Nat.mod_eq_of_lt (by omega)
    simp only [Fin.val_add,hone] at hval
    by_cases h1 : i.val + 1 < p.length
    · rw [Nat.mod_eq_of_lt h1] at hval
      by_cases h2 : i.val + 2 < p.length
      · rw [show i.val + 1 + 1 = i.val + 2 by omega, Nat.mod_eq_of_lt h2] at hval
        omega
      · rw [show i.val + 1 + 1 = p.length by omega, Nat.mod_self] at hval
        omega
    · rw [show i.val + 1 = p.length by omega, Nat.mod_self] at hval
      simp only [Nat.zero_add, Nat.mod_eq_of_lt (show 1 < p.length by omega)] at hval
      omega

theorem cycle_perimeter {u : Vertex} (p : graph.Walk u u) (hp : p.IsCycle) :
    p.length ≤ 15 := (ofCycle p hp).perimeter_le

theorem cycle_points {u : Vertex} (p : graph.Walk u u) (hp : p.IsCycle) :
    3 ≤ (ofCycle p hp).points.card :=
  (ofCycle p hp).points_ge (by have := hp.three_le_length; exact lt_of_lt_of_le (by decide) this)

/-- Literal top-cone walks, including all repeats, have a finite simple-cycle
normalization preserving any specified antisymmetric lifted triangle chain.
No minimum diagram or abstract polygon hypothesis is used here. -/
theorem normalize_walk {A : Type*} [AddCommGroup A]
    (c : graph.Dart → A) (hc : ∀ d, c d.symm = -c d)
    {u : Vertex} (p : graph.Walk u u) :
    ∃ cs : List (ConeWalks.Circuit graph),
      ConeWalks.chain c p = ConeWalks.total c cs ∧
      ConeWalks.perimeter cs ≤ p.length ∧
      ∀ q ∈ cs, q.2.val.length ≤ 15 ∧ 3 ≤ (ofCycle q.2.val q.2.property).points.card := by
  obtain ⟨cs,he,hl⟩ := ConeWalks.decompose_closed c hc p
  exact ⟨cs,he,hl,fun q _ => ⟨cycle_perimeter q.2.val q.2.property,cycle_points q.2.val q.2.property⟩⟩

end HyperbolicObstruction.MacroGraph
end
end

section

end
end

end OAI
