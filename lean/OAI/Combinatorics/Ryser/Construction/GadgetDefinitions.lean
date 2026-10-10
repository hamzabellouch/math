import OAI.Combinatorics.Ryser.Construction.GadgetAlgebra

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

abbrev NonzeroSlope (k : Type*) [Zero k] := {d : k // d ≠ 0}

abbrev GadgetOutcome (k : Type*) [Zero k] := NonzeroSlope k → k

def omittedLine (a : GadgetOutcome k) (d : NonzeroSlope k) : AffineLine k :=
  (some d.val, a d)

def retainedPoints (a : GadgetOutcome k) : Finset (Point k) :=
  Finset.univ \ Finset.univ.biUnion (fun d => linePoints (omittedLine a d))

def transformedRetained (a : GadgetOutcome k) : Finset (Point k) :=
  (retainedPoints a).image cubeMap

def cubicDeletionUnion (a : GadgetOutcome k) : Finset (Point k) :=
  Finset.univ.biUnion fun d : NonzeroSlope k => cubicShape d.val (a d)

@[simp] theorem mem_retainedPoints (a : GadgetOutcome k) (w : Point k) :
    w ∈ retainedPoints a ↔ ∀ d, ¬Incidence w (omittedLine a d) := by
  simp [retainedPoints]

theorem not_incidence_omittedLine (a : GadgetOutcome k) {w : Point k}
    (hw : w ∈ retainedPoints a) (d : NonzeroSlope k) :
    ¬Incidence w (omittedLine a d) := (mem_retainedPoints a w).mp hw d

theorem cubeMap_mem_cubicShape_iff
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (w : Point k) (d z : k) :
    cubeMap w ∈ cubicShape d z ↔ Incidence w (some d, z) := by
  rw [cubicShape_eq_image_linePoints]
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    have hsame : v = w := (cubeMap_bijective hcop).injective hvw
    subst v
    exact (mem_linePoints _ _).mp hv
  · intro hw
    exact Finset.mem_image.mpr ⟨w, (mem_linePoints _ _).mpr hw, rfl⟩

theorem cubeMap_mem_transformedRetained_iff
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (a : GadgetOutcome k) (w : Point k) :
    cubeMap w ∈ transformedRetained a ↔ w ∈ retainedPoints a := by
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    exact (cubeMap_bijective hcop).injective hvw ▸ hv
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

theorem transformedRetained_eq_survivors
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (a : GadgetOutcome k) :
    transformedRetained a = Finset.univ \ cubicDeletionUnion a := by
  ext p
  obtain ⟨w, rfl⟩ := (cubeMap_bijective hcop).surjective p
  rw [cubeMap_mem_transformedRetained_iff hcop]
  simp [mem_retainedPoints, cubicDeletionUnion, cubeMap_mem_cubicShape_iff hcop,
    omittedLine]

theorem transformedRetained_card
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (a : GadgetOutcome k) :
    (transformedRetained a).card = (retainedPoints a).card := by
  exact Finset.card_image_of_injective _ (cubeMap_bijective hcop).injective

theorem omitted_line_disjoint_retained (a : GadgetOutcome k) (d : NonzeroSlope k) :
    Disjoint (linePoints (omittedLine a d)) (retainedPoints a) := by
  apply Finset.disjoint_left.mpr
  intro w hwline hwretained
  exact not_incidence_omittedLine a hwretained d ((mem_linePoints _ _).mp hwline)

end RyserCoveringCounterexample.Construction

end

end OAI
