import OAI.Geometry.PeriodicTiling.CycleTests
import OAI.Geometry.PeriodicTiling.SeedSymbols
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.FinCases

namespace OAI

noncomputable section

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p]

def ordinaryCycle (p : ℕ) [NeZero p] : ZMod (p ^ 2) ↪ Channel p where
  toFun j := .inl ((ZMod.finEquiv (p ^ 2)).symm j)
  inj' _ _ h := (ZMod.finEquiv (p ^ 2)).symm.injective (Sum.inl.inj h)

def ordinaryCycleLabels (w : Word p) (j : ZMod (p ^ 2)) :
    Label p (ordinaryCycle p j) :=
  w ((ZMod.finEquiv (p ^ 2)).symm j)

def seedCycle (t : Fin 2) (n : Column p) : ZMod 2 ↪ Channel p where
  toFun j := Fin.cases (.inr t) (fun _ => .inl n) j
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · change Sum.inr t = Sum.inl n at h
      cases h
    · change Sum.inl n = Sum.inr t at h
      cases h
    · rfl

@[simp] theorem seedCycle_zero
    {p : ℕ} [NeZero p]
    (t : Fin 2) (n : Column p) :
    seedCycle t n 0 = .inr t := rfl

@[simp] theorem seedCycle_one
    {p : ℕ} [NeZero p]
    (t : Fin 2) (n : Column p) :
    seedCycle t n 1 = .inl n := rfl

def seedCycleLabels (t : Fin 2) (n : Column p) (j : Symbol p) (z : ZMod 2) :
    Label p (seedCycle t n z) :=
  Fin.cases (motive := fun z : Fin 2 => Label p (seedCycle t n z))
    () (fun _ => j) z

@[simp] theorem seedCycleLabels_zero
    {p : ℕ} [NeZero p]
    (t : Fin 2) (n : Column p) (j : Symbol p) :
    seedCycleLabels t n j 0 = () := rfl

@[simp] theorem seedCycleLabels_one
    {p : ℕ} [NeZero p]
    (t : Fin 2) (n : Column p) (j : Symbol p) :
    seedCycleLabels t n j 1 = j := rfl

variable (E : EncodingParameters p)

theorem ordinaryCycle_exclusion_iff (w : Word p) (o : GraphOutputs E)
    (hdep : HasDependence E o) :
    (∀ F ∈ cycleTiles E (ordinaryCycle p) (ordinaryCycleLabels w),
      Tiles F (graph o)) ↔
      ∀ x, ¬ (∀ n : Column p, Active E o (.inl n) x (w n)) := by
  classical
  rw [cycle_exclusion_iff E (ordinaryCycle p) (ordinaryCycleLabels w) o hdep]
  constructor
  · intro h x hall
    obtain ⟨z, hz⟩ := h x
    exact hz (hall ((ZMod.finEquiv (p ^ 2)).symm z))
  · intro h x
    obtain ⟨n, hn⟩ := not_forall.mp (h x)
    refine ⟨(ZMod.finEquiv (p ^ 2)) n, ?_⟩
    exact Eq.mpr
      (congrArg (fun m : Column p => ¬ Active E o (.inl m) x (w m))
        ((ZMod.finEquiv (p ^ 2)).symm_apply_apply n)) hn

theorem seedCycle_exclusion_iff (t : Fin 2) (n : Column p) (j : Symbol p)
    (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ cycleTiles E (seedCycle t n) (seedCycleLabels t n j),
      Tiles F (graph o)) ↔
      ∀ x, ¬ (Active E o (.inr t) x () ∧ Active E o (.inl n) x j) := by
  classical
  rw [cycle_exclusion_iff E (seedCycle t n) (seedCycleLabels t n j) o hdep]
  constructor
  · intro h x hx
    obtain ⟨z, hz⟩ := h x
    fin_cases z
    · exact hz hx.1
    · exact hz hx.2
  · intro h x
    by_cases hs : Active E o (.inr t) x ()
    · refine ⟨1, ?_⟩
      change ¬ Active E o (.inl n) x j
      intro hj
      exact h x ⟨hs, hj⟩
    · exact ⟨0, hs⟩

def wordConstraintTiles : Finset (Finset (Ambient E)) := by
  classical
  exact (Finset.univ.filter (fun w : Word p => w ∉ allowedWords p)).biUnion
    (fun w => cycleTiles E (ordinaryCycle p) (ordinaryCycleLabels w))

def seedConstraintTiles : Finset (Finset (Ambient E)) := by
  classical
  exact (Finset.univ.filter (fun q : Fin 2 × Column p × Symbol p =>
      q.2.2 ≠ seedSymbol E q.1)).biUnion
    (fun q => cycleTiles E (seedCycle q.1 q.2.1) (seedCycleLabels q.1 q.2.1 q.2.2))

theorem nonempty_of_mem_wordConstraintTiles {F : Finset (Ambient E)}
    (hF : F ∈ wordConstraintTiles E) : F.Nonempty := by
  classical
  obtain ⟨w, _, hF⟩ := Finset.mem_biUnion.mp hF
  exact nonempty_of_mem_cycleTiles E (ordinaryCycle p) (ordinaryCycleLabels w) hF

theorem nonempty_of_mem_seedConstraintTiles {F : Finset (Ambient E)}
    (hF : F ∈ seedConstraintTiles E) : F.Nonempty := by
  classical
  obtain ⟨q, _, hF⟩ := Finset.mem_biUnion.mp hF
  exact nonempty_of_mem_cycleTiles E (seedCycle q.1 q.2.1)
    (seedCycleLabels q.1 q.2.1 q.2.2) hF

theorem wordConstraintTiles_iff (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ wordConstraintTiles E, Tiles F (graph o)) ↔
      ∀ x w, (∀ n : Column p, Active E o (.inl n) x (w n)) → Allowed p w := by
  classical
  constructor
  · intro h x w hw
    by_contra hnot
    have hcycle : ∀ F ∈ cycleTiles E (ordinaryCycle p) (ordinaryCycleLabels w),
        Tiles F (graph o) := by
      intro F hF
      apply h F
      apply Finset.mem_biUnion.mpr
      exact ⟨w, by simp [hnot], hF⟩
    exact (ordinaryCycle_exclusion_iff E w o hdep).mp hcycle x hw
  · intro h F hF
    obtain ⟨w, hw, hF⟩ := Finset.mem_biUnion.mp hF
    have hnot : ¬ Allowed p w := by simpa using (Finset.mem_filter.mp hw).2
    apply (ordinaryCycle_exclusion_iff E w o hdep).mpr ?_ F hF
    intro x hx
    exact hnot (h x w hx)

theorem seedConstraintTiles_iff (o : GraphOutputs E) (hdep : HasDependence E o) :
    (∀ F ∈ seedConstraintTiles E, Tiles F (graph o)) ↔
      ∀ t n x j, Active E o (.inr t) x () → Active E o (.inl n) x j →
        j = seedSymbol E t := by
  classical
  constructor
  · intro h t n x j hseed hord
    by_contra hj
    have hcycle : ∀ F ∈ cycleTiles E (seedCycle t n) (seedCycleLabels t n j),
        Tiles F (graph o) := by
      intro F hF
      apply h F
      apply Finset.mem_biUnion.mpr
      exact ⟨(t, n, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hF⟩
    exact (seedCycle_exclusion_iff E t n j o hdep).mp hcycle x ⟨hseed, hord⟩
  · intro h F hF
    obtain ⟨⟨t, n, j⟩, hq, hF⟩ := Finset.mem_biUnion.mp hF
    have hj : j ≠ seedSymbol E t := (Finset.mem_filter.mp hq).2
    apply (seedCycle_exclusion_iff E t n j o hdep).mpr ?_ F hF
    intro x hx
    exact hj (h t n x j hx.1 hx.2)

end PeriodicTilingThree

end

end OAI
