import Mathlib
import OAI.Probability.CriticalPercolation.GraphTopology.GraphAutomorphismTopology

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def reachBall (o : X) (r : ℕ) : Set X :=
  {x | ∃ p : Γ.Walk o x, p.length≤r}

lemma reachBall_self (o : X) (r : ℕ) : o∈reachBall Γ o r :=
  ⟨SimpleGraph.Walk.nil,Nat.zero_le _⟩

lemma reachBall_symm {o x : X} {r : ℕ} (h : x∈reachBall Γ o r) :
    o∈reachBall Γ x r := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.reverse,by simpa using hp⟩

lemma reachBall_add {o x y : X} {r s : ℕ} (hx : x∈reachBall Γ o r)
    (hy : y∈reachBall Γ x s) : y∈reachBall Γ o (r+s) := by
  obtain ⟨p,hp⟩ := hx
  obtain ⟨q,hq⟩ := hy
  exact ⟨p.append q,by simpa using Nat.add_le_add hp hq⟩

lemma reachBall_finite (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) (r : ℕ) :
    (reachBall Γ o r).Finite := by
  induction r generalizing o with
  | zero =>
    apply (Set.finite_singleton o).subset
    rintro x ⟨p,hp⟩
    cases p with
    | nil => exact Set.mem_singleton o
    | cons h p => simp at hp
  | succ r ih =>
    apply ((Set.finite_singleton o).union ((hl o).biUnion fun x _ => ih x)).subset
    rintro x ⟨p,hp⟩
    cases p with
    | nil => exact Or.inl rfl
    | @cons a b c h p =>
      right
      exact Set.mem_iUnion₂.mpr ⟨b,h,p,by simpa using hp⟩

lemma iso_reachBall (g : Γ ≃g Γ) {o x : X} {r : ℕ}
    (h : x∈reachBall Γ o r) : g x∈reachBall Γ (g o) r := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.map g.toHom,by simpa using hp⟩

lemma inverse_displacement {o : X} {r : ℕ} (g : Γ ≃g Γ)
    (h : g o∈reachBall Γ o r) : g.symm o∈reachBall Γ o r := by
  have hh := reachBall_symm Γ (iso_reachBall Γ g.symm h)
  simpa using hh

variable [TopologicalSpace X] [DiscreteTopology X]
local instance : TopologicalSpace (Γ ≃g Γ) := autTopology Γ

lemma compact_displacement (hc : Γ.Connected)
    (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) (r : ℕ) :
    IsCompact {g : Γ ≃g Γ | g o∈reachBall Γ o r} := by
  have hp : ∀ x, ∃ p : Γ.Walk o x, True := fun x => by
    obtain ⟨p⟩ := hc o x
    exact ⟨p,trivial⟩
  choose p _ using hp
  let F : X → Set X := fun x => reachBall Γ o (r+(p x).length)
  have hfb : ∀ (g : Γ ≃g Γ), g o∈reachBall Γ o r → ∀ x, g x∈F x := by
    intro g hg x
    exact reachBall_add Γ hg (iso_reachBall Γ g ⟨p x,le_rfl⟩)
  apply (compact_coordinate_bounds Γ F (fun x => reachBall_finite Γ hl o _)).of_isClosed_subset
    (isClosed_eval_mem Γ o _)
  intro g hg
  exact ⟨hfb g hg,hfb g.symm (inverse_displacement Γ g hg)⟩

lemma compact_stabilizer (hc : Γ.Connected)
    (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) :
    IsCompact {g : Γ ≃g Γ | g o=o} := by
  apply (compact_displacement Γ hc hl o 0).of_isClosed_subset
    (isClosed_eq (continuous_eval Γ o) continuous_const)
  intro g hg
  change g o∈reachBall Γ o 0
  rw [hg]
  exact reachBall_self Γ o 0

lemma open_displacement (o : X) (r : ℕ) :
    IsOpen {g : Γ ≃g Γ | g o∈reachBall Γ o r} := isOpen_eval_mem Γ o _

lemma open_stabilizer (o : X) : IsOpen {g : Γ ≃g Γ | g o=o} :=
  isOpen_eval_mem Γ o {o}

lemma locallyCompact_aut (hc : Γ.Connected)
    (hl : ∀ x, (Γ.neighborSet x).Finite) (o : X) :
    LocallyCompactSpace (Γ ≃g Γ) :=
  (compact_stabilizer Γ hc hl o).locallyCompactSpace_of_mem_nhds_of_group
    ((open_stabilizer Γ o).mem_nhds (show (1 : Γ ≃g Γ) o=o from rfl))

instance aut_totallyDisconnected : TotallyDisconnectedSpace (Γ ≃g Γ) :=
  (coordinates_embedding Γ).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

lemma compact_finite_vertex_images (K : Set (Γ ≃g Γ)) (hK : IsCompact K) (o : X) :
    ((fun g : Γ ≃g Γ => g o) '' K).Finite :=
  isCompact_iff_finite.mp (hK.image (continuous_eval Γ o))

end CriticalPercolation.GraphTopology
end
end

end OAI
