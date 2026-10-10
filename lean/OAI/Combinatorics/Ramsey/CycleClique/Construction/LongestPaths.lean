import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathEndpoints
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! Maximum-order paths starting at a prescribed vertex. -/

namespace CycleClique.Construction
def IsIndexedPath {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (f : Fin (r + 1) → V) : Prop :=
  Function.Injective f ∧ ∀ i : Fin r, G.Adj (f i.castSucc) (f i.succ)

theorem indexedPath_snoc {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f) {v : V}
    (hv : v ∉ Set.range f) (hadj : G.Adj (f (Fin.last r)) v) :
    IsIndexedPath G (Fin.snoc f v) := by
  refine ⟨Fin.snoc_injective_iff.mpr ⟨hf.1, hv⟩, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hadj
  · have heq : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
    rw [heq]
    simpa only [Fin.snoc_castSucc] using hf.2 j

/-- Finite cardinality bounds path order, so maximizing it uses only
well-ordering of natural numbers. -/
theorem exists_longest_path_from {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) :
    ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ f 0 = x ∧
      ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → g 0 = x → q ≤ r := by
  classical
  let b := Fintype.card V - 1
  have hex : ∃ d, ∃ r, ∃ f : Fin (r + 1) → V,
      IsIndexedPath G f ∧ f 0 = x ∧ r + d = b := by
    refine ⟨b, 0, fun _ => x, ⟨?_, ?_⟩, rfl, by omega⟩
    · intro i j _
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
    · exact fun i => Fin.elim0 i
  obtain ⟨r, f, hf, hstart, hd⟩ := Nat.find_spec hex
  refine ⟨r, f, hf, hstart, ?_⟩
  intro q g hg hgs
  have hqcard := Fintype.card_le_of_injective g hg.1
  simp only [Fintype.card_fin] at hqcard
  have hqb : q ≤ b := by dsimp [b]; omega
  have hmin := Nat.find_min' hex
    (show ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ f 0 = x ∧
      r + (b - q) = b from ⟨q, g, hg, hgs, Nat.add_sub_of_le hqb⟩)
  omega

/-- Every neighbour of the last vertex of a longest fixed-start path
lies on that path. -/
theorem longest_path_endpoint_neighbors {V : Type*} {G : SimpleGraph V}
    {x : V} {r : ℕ} {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hstart : f 0 = x)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → g 0 = x → q ≤ r) :
    ∀ v, G.Adj (f (Fin.last r)) v → v ∈ Set.range f := by
  intro v hv
  by_contra hn
  have hp := indexedPath_snoc hf hn hv
  have h := hmax (r + 1) (Fin.snoc f v) hp (by simpa using hstart)
  omega

/-- The endpoint neighbourhood alone gives the elementary lower bound
on the order of a longest fixed-start path. -/
theorem longest_path_degree_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {x : V} {r : ℕ} {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hstart : f 0 = x)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → g 0 = x → q ≤ r) :
    (G.neighborSet (f (Fin.last r))).ncard ≤ r := by
  classical
  let e := f (Fin.last r)
  have hneigh := longest_path_endpoint_neighbors hf hstart hmax
  have hex : ∀ v : G.neighborFinset e, ∃ i : Fin r, f i.castSucc = v.val := by
    intro v
    have hadj := (G.mem_neighborFinset e v.val).mp v.property
    obtain ⟨j, hj⟩ := hneigh v.val hadj
    have hjlt : j.val < r := by
      have hneq : j ≠ Fin.last r := by
        intro h
        subst j
        exact hadj.ne hj
      have hval : j.val ≠ r := fun h => hneq (Fin.ext h)
      omega
    exact ⟨⟨j.val, hjlt⟩, by simpa using hj⟩
  let index : G.neighborFinset e → Fin r := fun v => Classical.choose (hex v)
  have hindex : ∀ v : G.neighborFinset e, f (index v).castSucc = v.val :=
    fun v => Classical.choose_spec (hex v)
  have hinj : Function.Injective index := by
    intro a b hab
    apply Subtype.ext
    rw [← hindex a, ← hindex b, hab]
  have hcard := Fintype.card_le_of_injective index hinj
  simpa only [Fintype.card_coe, Fintype.card_fin,
    SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.ncard_neighborSet] using hcard

end CycleClique.Construction

end OAI
