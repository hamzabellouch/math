import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Destinations
import OAI.Combinatorics.KMedianRecovery.Branching.Blue

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [DecidableEq V] {a : ℕ}

def destinationFacility (center : Fin a → V) : Destination V a → V
  | .proxy v => v | .covered i => center i | .uncovered v => v

omit [DecidableEq V] in
lemma blue_destination_eq (d : Destination V a) (h : d.isBlue = true) (center : Fin a → V) :
    d = .uncovered (destinationFacility center d) := by
  cases d <;> simp_all [Destination.isBlue,destinationFacility]

end MetricKMedianRecovery.Completion

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

@[simp] lemma destinations_proxy (C : Comparison D S O) (s : State V) (v : V) :
    Destination.proxy v ∈ C.destinations s ↔ v ∈ C.good.image C.proxy := by
  simp [destinations]

@[simp] lemma destinations_uncovered (C : Comparison D S O) (s : State V) (v : V) :
    Destination.uncovered v ∈ C.destinations s ↔ v ∈ C.bad \ C.covered s := by
  simp [destinations]

noncomputable def designatedDestination (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (v : V) : Destination V s.leaves.length :=
  selectedDestination theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
    (C.destinations s) (C.destinations_nonempty hD s) v

lemma designatedDestination_mem (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (v : V) :
    C.designatedDestination hD s theta v ∈ C.destinations s :=
  selectedDestination_mem theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
    (C.destinations s) (C.destinations_nonempty hD s) v

lemma designation_disjoint (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) :
    Disjoint (C.nonproxy \ s.deleted)
      (designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) := by
  apply proxy_requirements_consistent (C.nonproxy \ s.deleted) (C.good.image C.proxy)
  · apply Finset.disjoint_left.mpr
    intro v hv hp
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hp
  · intro u _ v he
    have hh := C.designatedDestination_mem hD s theta u
    rw [he] at hh
    exact (C.destinations_proxy s v).mp hh

noncomputable def colorClass (H : Finset V) (colors : V → Fin 3) (c : Fin 3) : Finset V :=
  H.filter (fun v => colors v = c)

lemma favorable_destination_green (C : Comparison D S O) (hD : D.Nonempty)
    (kappa theta : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta),
      colors u = requiredColors (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) u)
    (u : V) (hu : u ∈ C.nonproxy \ s.deleted) (v : V)
    (hdest : C.designatedDestination hD s theta u = .proxy v) :
    v ∈ colorClass (S \ s.deleted) colors 0 := by
  have hh := favorable_color_consequences (C.nonproxy \ s.deleted)
    (C.designatedDestination hD s theta) (C.designation_disjoint hD s theta) colors hcolors
  have hgreen := hh.2.2 v ((designatedProxies_mem _ _ v).mpr ⟨u,hu,hdest⟩)
  have hv := C.designatedDestination_mem hD s theta u
  rw [hdest] at hv
  obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp ((C.destinations_proxy s v).mp hv)
  exact Finset.mem_filter.mpr ⟨C.proxy_survives s hs.1 o ho,hgreen⟩

lemma favorable_red_rule (C : Comparison D S O) (hD : D.Nonempty)
    (kappa theta : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta),
      colors u = requiredColors (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) u)
    (u : V) (hu : u ∈ designatedRed (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    match C.designatedDestination hD s theta u with
    | .proxy v => v ∈ colorClass (S \ s.deleted) colors 0
    | .covered _ => True
    | .uncovered _ => False := by
  have huR := (Finset.mem_filter.mp hu).1
  have hblue := (Finset.mem_filter.mp hu).2
  cases he : C.designatedDestination hD s theta u with
  | proxy v => exact C.favorable_destination_green hD kappa theta s hs colors hcolors u huR v he
  | covered i => trivial
  | uncovered v => simp only [he,Destination.isBlue,Bool.true_eq_false] at hblue

noncomputable def blueDestination (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V) : V :=
  destinationFacility (C.coveredCenter s) (C.designatedDestination hD s theta u)

lemma blueDestination_uncovered (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V)
    (hu : u ∈ designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    C.designatedDestination hD s theta u = .uncovered (C.blueDestination hD s theta u) :=
  blue_destination_eq _ (Finset.mem_filter.mp hu).2 _

lemma blueDestination_mem (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V)
    (hu : u ∈ designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    C.blueDestination hD s theta u ∈ C.bad \ C.covered s := by
  have hh := C.designatedDestination_mem hD s theta u
  rw [C.blueDestination_uncovered hD s theta u hu] at hh
  exact (C.destinations_uncovered s _).mp hh

lemma blueDestination_distance (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V)
    (hu : u ∈ designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    dist u (C.blueDestination hD s theta u) =
      minimumMixed theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
        (C.destinations s) (C.destinations_nonempty hD s) u := by
  have hh := selectedDestination_distance theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
    (C.destinations s) (C.destinations_nonempty hD s) u
  change mixedDistance theta (C.coveredCenter s) (leafCenter s) (leafRadius s) u
    (C.designatedDestination hD s theta u) = _ at hh
  rw [C.blueDestination_uncovered hD s theta u hu] at hh
  exact hh

end MetricKMedianRecovery.Sampling.Comparison

end OAI
