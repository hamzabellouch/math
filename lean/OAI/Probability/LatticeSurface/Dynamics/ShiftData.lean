import Mathlib

namespace OAI

open Set MeasureTheory intervalIntegral

universe u v

namespace FeasibleShift

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def component (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Reachable x)

noncomputable def contactGraph (G : SimpleGraph V) (h : V → ℝ) (s : ℝ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ 1 - |h x - h y| ≤ s
  symm := ⟨by intro x y hxy; simpa only [abs_sub_comm] using And.intro hxy.1.symm hxy.2⟩
  loopless := ⟨by intro x hx; exact G.irrefl hx.1⟩

noncomputable def prescription (G : SimpleGraph V) (ground : Finset V)
    (f : V → ℝ) (x : V) : ℝ :=
  if Disjoint (component G x) ground then
    (∑ y ∈ component G x, f y) / (component G x).card else 0

noncomputable def averagedShift (G : SimpleGraph V) (ground : Finset V)
    (f h : V → ℝ) (s₀ s₁ : ℝ) (x : V) : ℝ :=
  (s₁ - s₀)⁻¹ * ∫ s in s₀..s₁, prescription (contactGraph G h s) ground f x

abbrev FreeSites (pins : Finset V) := {x : V // x ∉ pins}

noncomputable def extendHeight (pins : Finset V) (β : V → ℝ)
    (h : FreeSites pins → ℝ) (x : V) : ℝ :=
  if hx : x ∈ pins then β x else h ⟨x, hx⟩

noncomputable def freeShift (G : SimpleGraph V) (ground pins : Finset V)
    (β f : V → ℝ) (s₀ s₁ : ℝ) (h : FreeSites pins → ℝ) (x : FreeSites pins) : ℝ :=
  averagedShift G ground f (extendHeight pins β h) s₀ s₁ x

noncomputable def heightPolytope (G : SimpleGraph V) (pins walls : Finset V)
    (β : V → ℝ) (I : V → Set ℝ) : Set (FreeSites pins → ℝ) :=
  {h | (∀ x y, G.Adj x y → |extendHeight pins β h x - extendHeight pins β h y| ≤ 1) ∧
    ∀ x ∈ walls, extendHeight pins β h x ∈ I x}

noncomputable def neighbors (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj x)

noncomputable def shiftGraph (G : SimpleGraph V) (ground : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬ (x ∈ ground ∧ y ∈ ground)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, fun hh => h.2 ⟨hh.2, hh.1⟩⟩⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩

noncomputable def localSites (G : SimpleGraph V) (ground : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun x => x ∉ ground ∨ ∃ y, y ∉ ground ∧ G.Adj x y

structure ShiftData (W : Type v) [Fintype W] [DecidableEq W]
    (n D Db B : ℕ) (ρ : ENNReal) (sstar L M N : ℝ) where
  graph : SimpleGraph V
  ground : Finset V
  pins : Finset V
  walls : Finset V
  pins_ground : pins ⊆ ground
  walls_ground : walls ⊆ ground
  boundary : V → ℝ
  intervals : V → Set ℝ
  prescribed : V → ℝ
  prescribed_ground : ∀ x ∈ ground, prescribed x = 0
  prescribed_bound : ∀ x, |prescribed x| ≤ M
  prescribed_gradient : ∀ x y, graph.Adj x y → |prescribed x - prescribed y| ≤ L / n
  vertex_count : ((localSites graph ground).card : ℝ) ≤ N * (n : ℝ)^2
  degree : ∀ x, (neighbors graph x).card ≤ D
  polytope_measurable : MeasurableSet (heightPolytope graph pins walls boundary intervals)
  polytope_positive : volume (heightPolytope graph pins walls boundary intervals) ≠ 0
  polytope_finite : volume (heightPolytope graph pins walls boundary intervals) ≠ ⊤
  boxGraph : SimpleGraph W
  box_degree : ∀ w, (neighbors boxGraph w).card ≤ Db
  boxMap : V → W
  box_fiber : ∀ w, (Finset.univ.filter fun x => boxMap x = w).card ≤ B
  box_adjacent : ∀ x y, graph.Adj x y → boxMap x = boxMap y ∨ boxGraph.Adj (boxMap x) (boxMap y)
  badBoxes : (FreeSites pins → ℝ) → Set W
  contact_bad : ∀ h x y, (contactGraph (shiftGraph graph ground)
    (extendHeight pins boundary h) sstar).Adj x y → boxMap x ∈ badBoxes h ∧ boxMap y ∈ badBoxes h
  sparse : ∀ A : Finset W, (ProbabilityTheory.cond volume
    (heightPolytope graph pins walls boundary intervals)) {h | ∀ w ∈ A, w ∈ badBoxes h} ≤ ρ^A.card

namespace ShiftData

variable {W : Type v} [Fintype W] [DecidableEq W]

variable {n D Db B : ℕ} {ρ : ENNReal} {sstar L M N : ℝ}

variable (S : ShiftData (V := V) W n D Db B ρ sstar L M N)

noncomputable def polytope := heightPolytope S.graph S.pins S.walls S.boundary S.intervals

noncomputable def law := ProbabilityTheory.cond volume S.polytope

noncomputable def shift (s₀ s₁ : ℝ) :=
  freeShift (shiftGraph S.graph S.ground) S.ground S.pins S.boundary S.prescribed s₀ s₁

noncomputable def map (s₀ s₁ : ℝ) (h : FreeSites S.pins → ℝ) := h + S.shift s₀ s₁ h

end ShiftData

end FeasibleShift

end OAI
