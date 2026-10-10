import OAI.Combinatorics.Ryser.Construction.CosetIndex
import OAI.Combinatorics.Ryser.Construction.DirectionSets

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F]
variable [instDecidableEqk : DecidableEq k] [instDecidableEqF : DecidableEq F] [instFintypek : Fintype k]

def cosetPlacement (σ : k →+* F) (c : CosetIndex σ) : PlaneLinearMap F :=
  PlaneLinearMap.diagonal (cosetRepresentative σ c : F)
    (cosetRepresentative σ c).ne_zero

@[simp] theorem placedDirection_coset_none (σ : k →+* F) (c : CosetIndex σ) :
    placedDirection σ (cosetPlacement σ c) none = none := let _ := instDecidableEqk; let _ := instFintypek; by
  simp [placedDirection, mapDirection, cosetPlacement]

@[simp] theorem placedDirection_coset_some (σ : k →+* F) (c : CosetIndex σ)
    (t : k) :
    placedDirection σ (cosetPlacement σ c) (some t) =
      some ((cosetRepresentative σ c : F) * σ t) := let _ := instDecidableEqk; let _ := instFintypek; by
  simp [placedDirection, mapDirection, cosetPlacement]

theorem coset_axisDirections (σ : k →+* F) (c : CosetIndex σ) :
    axisDirections σ (cosetPlacement σ c) = {none, some 0} := by
  ext d
  simp [mem_axisDirections_iff]

theorem mem_coset_altered_iff (σ : k →+* F) (c : CosetIndex σ)
    (d : Direction F) :
    d ∈ alteredDirections σ (cosetPlacement σ c) ↔
      ∃ t : k, t ≠ 0 ∧ d = some ((cosetRepresentative σ c : F) * σ t) := by
  rw [mem_alteredDirections_iff]
  simp only [placedDirection_coset_some, eq_comm]

@[simp] theorem none_notMem_coset_altered (σ : k →+* F) (c : CosetIndex σ) :
    none ∉ alteredDirections σ (cosetPlacement σ c) := by
  simp [mem_coset_altered_iff]

@[simp] theorem zero_notMem_coset_altered (σ : k →+* F) (c : CosetIndex σ) :
    some 0 ∉ alteredDirections σ (cosetPlacement σ c) := by
  rintro hd
  obtain ⟨t, ht, heq⟩ := (mem_coset_altered_iff σ c _).mp hd
  have hz := Option.some.inj heq
  exact mul_ne_zero (cosetRepresentative σ c).ne_zero
    (fun hz' => ht (σ.injective (hz'.trans (map_zero σ).symm))) hz.symm

theorem unitCoset_mul_embedded (σ : k →+* F) (a : Fˣ) (u : kˣ) :
    unitCoset σ (a * embeddedUnits σ u) = unitCoset σ a := let _ := instDecidableEqk; let _ := instDecidableEqF; let _ := instFintypek; by
  apply (unitCoset_eq_iff σ _ _).mpr
  refine ⟨u, ?_⟩
  simp only [mul_div_cancel_left]

theorem some_unit_mem_coset_altered_iff (σ : k →+* F) (c : CosetIndex σ)
    (a : Fˣ) :
    some (a : F) ∈ alteredDirections σ (cosetPlacement σ c) ↔
      unitCoset σ a = c := by
  constructor
  · intro ha
    obtain ⟨t, ht, heq⟩ := (mem_coset_altered_iff σ c _).mp ha
    have hu : a = cosetRepresentative σ c * embeddedUnits σ (Units.mk0 t ht) := by
      apply Units.ext
      simpa [embeddedUnits] using Option.some.inj heq
    rw [hu, unitCoset_mul_embedded, unitCoset_representative]
  · intro ha
    obtain ⟨u, hu⟩ := exists_embeddedUnit_mul_representative σ a
    apply (mem_coset_altered_iff σ c _).mpr
    refine ⟨(u : k), u.ne_zero, ?_⟩
    apply congrArg Option.some
    have hv := congrArg (fun z : Fˣ => (z : F)) hu
    simpa [embeddedUnits, ha, mul_comm] using hv

theorem existsUnique_coset_altered (σ : k →+* F) (a : F) (ha : a ≠ 0) :
    ∃! c : CosetIndex σ, some a ∈ alteredDirections σ (cosetPlacement σ c) := by
  refine ⟨unitCoset σ (Units.mk0 a ha), ?_, ?_⟩
  · exact (some_unit_mem_coset_altered_iff σ _ (Units.mk0 a ha)).mpr rfl
  · intro c hc
    exact ((some_unit_mem_coset_altered_iff σ c (Units.mk0 a ha)).mp hc).symm

theorem coset_altered_index_eq (σ : k →+* F) {c e : CosetIndex σ}
    {d : Direction F}
    (hc : d ∈ alteredDirections σ (cosetPlacement σ c))
    (he : d ∈ alteredDirections σ (cosetPlacement σ e)) : c = e := by
  obtain ⟨t, ht, rfl⟩ := (mem_coset_altered_iff σ c d).mp hc
  let a : Fˣ := cosetRepresentative σ c * embeddedUnits σ (Units.mk0 t ht)
  have hc' : unitCoset σ a = c := by
    simp only [a, unitCoset_mul_embedded, unitCoset_representative]
  have he' : unitCoset σ a = e := by
    apply (some_unit_mem_coset_altered_iff σ e a).mp
    simpa [a, embeddedUnits] using he
  exact hc'.symm.trans he'

theorem disjoint_coset_altered (σ : k →+* F) {c e : CosetIndex σ}
    (hce : c ≠ e) :
    Disjoint (alteredDirections σ (cosetPlacement σ c))
      (alteredDirections σ (cosetPlacement σ e)) := by
  apply Finset.disjoint_left.mpr
  intro d hc he
  exact hce (coset_altered_index_eq σ hc he)

theorem identity_coset_altered (σ : k →+* F) :
    alteredDirections σ (cosetPlacement σ 1) =
      (Finset.univ.erase (0 : k)).image (fun t => some (σ t)) := by
  simp [alteredDirections, placedDirection_coset_some]

end RyserCoveringCounterexample.Construction

end

end OAI
