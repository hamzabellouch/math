import OAI.Combinatorics.Ramsey.CycleClique.Construction.ClosedIndexed

namespace OAI

/-! Longest paths and the elementary fact that a closed longest path spans a connected graph. -/

namespace CycleClique.Construction
theorem exists_longest_path {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧
      ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → q ≤ r := by
  classical
  let x : V := Classical.choice inferInstance
  let b := Fintype.card V - 1
  have hex : ∃ d, ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ r + d = b := by
    refine ⟨b, 0, fun _ => x, ⟨?_, ?_⟩, by omega⟩
    · intro i j _
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
    · exact fun i => Fin.elim0 i
  obtain ⟨r, f, hf, hd⟩ := Nat.find_spec hex
  refine ⟨r, f, hf, ?_⟩
  intro q g hg
  have hcard := Fintype.card_le_of_injective g hg.1
  simp only [Fintype.card_fin] at hcard
  have hqb : q ≤ b := by dsimp [b]; omega
  have hmin := Nat.find_min' hex
    (show ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ r + (b - q) = b from
      ⟨q, g, hg, Nat.add_sub_of_le hqb⟩)
  omega

theorem indexedPath_reverse {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f) :
    IsIndexedPath G (f ∘ Fin.rev) := by
  refine ⟨hf.1.comp Fin.rev_injective, ?_⟩
  intro i
  simpa only [Function.comp_apply, Fin.rev_castSucc, Fin.rev_succ] using (hf.2 i.rev).symm

theorem connected_edge_leaving {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    {W : Set V} {u v : V} (hu : u ∈ W) (hv : v ∉ W) :
    ∃ a ∈ W, ∃ b ∉ W, G.Adj a b := by
  classical
  obtain ⟨p⟩ := hconn.preconnected u v
  have hcut : ∀ {x y : V}, G.Walk x y → x ∈ W → y ∉ W →
      ∃ a ∈ W, ∃ b ∉ W, G.Adj a b := by
    intro x y q
    induction q with
    | nil => intro hx hy; exact False.elim (hy hx)
    | @cons x z y hxz q ih =>
      intro hx hy
      by_cases hz : z ∈ W
      · exact ih hz hy
      · exact ⟨x, hx, z, hz, hxz⟩
  exact hcut p hu hv

theorem closed_longest_path_surjective {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (hconn : G.Connected) {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → q ≤ r)
    (hclose : G.Adj (f (Fin.last r)) (f 0)) : Function.Surjective f := by
  intro v
  by_contra hv
  have hv' : v ∉ Set.range f := hv
  obtain ⟨a, ⟨j, rfl⟩, b, hb, hab⟩ := connected_edge_leaving hconn
    (show f 0 ∈ Set.range f from ⟨0, rfl⟩) hv'
  obtain ⟨g, hg, hlast, hrange⟩ := indexedPath_closed_ending hf hclose j
  have hb' : b ∉ Set.range g := by rwa [hrange]
  have hadj : G.Adj (g (Fin.last r)) b := by rwa [hlast]
  have hp := indexedPath_snoc hg hb' hadj
  have h := hmax (r + 1) (Fin.snoc g b) hp
  omega

end CycleClique.Construction

end OAI
