import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteConstraints

namespace OAI

/-! A required-path certificate is simply a finite simple path. Its
complementary outside parameter is forbidden by the exact cycle length. -/

namespace CycleClique.Construction
structure RequiredPathData (W : Type*) where
  x : W
  y : W
  middle : List W
  deriving DecidableEq, Repr

namespace RequiredPathData

variable {W : Type*}

def support (p : RequiredPathData W) : List W := p.x :: (p.middle ++ [p.y])

def parameter (k : ℕ) (p : RequiredPathData W) : ℕ := k - (p.middle.length + 1)

def Check (H : SimpleGraph W) (k : ℕ) (p : RequiredPathData W) : Prop :=
  p.support.Nodup ∧ p.support.IsChain H.Adj ∧ p.middle.length + 1 ≤ k

instance [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (k : ℕ) (p : RequiredPathData W) : Decidable (p.Check H k) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {V : Type*} {n : ℕ} {G : SimpleGraph V} {H : SimpleGraph (Fin n)}

theorem forbids {k : ℕ} (hk : 3 ≤ k) (hcycle : ¬ HasCycle G (k + 1))
    (f : H →g G) (hf : Function.Injective f) {X : Finset V}
    (hfX : ∀ i, f i ∈ X) (p : RequiredPathData (Fin n)) (hc : p.Check H k) :
    ¬ OutsidePath G (X : Set V) (f p.x) (f p.y) (p.parameter k) := by
  have hne : p.support ≠ [] := List.cons_ne_nil _ _
  let w := SimpleGraph.Walk.ofSupport p.support hne hc.2.1
  have hw : w.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    exact (SimpleGraph.Walk.support_ofSupport _ _).symm ▸ hc.1
  have hlen₀ : w.length = p.support.length - 1 :=
    SimpleGraph.Walk.length_ofSupport hne hc.2.1
  have hlen : w.length = p.middle.length + 1 := by rw [hlen₀]; simp [support]
  have hh := required_indexed_path_forbids f hf hfX hk hcycle w hw (by omega)
    (by rw [hlen]; exact hc.2.2)
  rw [hlen] at hh
  simpa [w, support, parameter, List.getLast_cons] using hh

end RequiredPathData

variable {n : ℕ}

def requiredEntryMatrix (k : ℕ) (p : RequiredPathData (Fin n)) : ForbiddenMatrix n := fun i j =>
  if (i = p.x ∧ j = p.y) ∨ (i = p.y ∧ j = p.x) then {p.parameter k} else ∅

def requiredMatrix (k : ℕ) : List (RequiredPathData (Fin n)) → ForbiddenMatrix n
  | [] => fun _ _ => ∅
  | p :: E => fun i j => requiredEntryMatrix k p i j ∪ requiredMatrix k E i j

variable {V : Type*} {G : SimpleGraph V} {H : SimpleGraph (Fin n)}

theorem requiredMatrix_sound {k : ℕ} (hk : 3 ≤ k) (hcycle : ¬ HasCycle G (k + 1))
    (f : H →g G) (hf : Function.Injective f) {X : Finset V} (hfX : ∀ i, f i ∈ X)
    (E : List (RequiredPathData (Fin n))) (hE : ∀ p ∈ E, p.Check H k) :
    (requiredMatrix k E).Sound G X f := by
  induction E with
  | nil => intro i j d hd; simp only [requiredMatrix, Finset.notMem_empty] at hd
  | cons p E ih =>
    apply ForbiddenMatrix.Sound.union
    · intro i j d hd
      have hpair : (i = p.x ∧ j = p.y) ∨ (i = p.y ∧ j = p.x) := by
        by_contra hn
        simp only [requiredEntryMatrix, hn, ↓reduceIte, Finset.notMem_empty] at hd
      have heq : d = p.parameter k := by
        simpa only [requiredEntryMatrix, hpair, ↓reduceIte, Finset.mem_singleton] using hd
      subst d
      have hb := p.forbids hk hcycle f hf hfX (hE p (by simp))
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hb
      · exact fun h => hb h.reverse
    · exact ih (fun q hq => hE q (by simp [hq]))

end CycleClique.Construction

end OAI
