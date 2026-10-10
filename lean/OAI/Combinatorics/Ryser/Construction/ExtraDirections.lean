import OAI.Combinatorics.Ryser.Construction.DirectionSets
import OAI.Combinatorics.Ryser.Construction.LinearPlacement

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [DecidableEq k] [DecidableEq F]

namespace PlaneLinearMap

theorem directionMap_bijective [Fintype F] (M : PlaneLinearMap F) :
    Function.Bijective M.directionMap :=
  M.directionMap_injective.bijective_of_finite

end PlaneLinearMap

theorem extra_placedDirection (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (d : Direction k) :
    placedDirection σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) d =
      mapDirection σ ((PlaneLinearMap.extra u v huv).directionMap d) := by
  cases d with
  | none =>
      simp [placedDirection, mapDirection]
  | some t =>
      have hzero : 1 + σ t = 0 ↔ 1 + t = 0 := by
        constructor
        · intro h
          apply σ.injective
          simpa only [map_add, map_one, map_zero] using h
        · intro h
          simpa only [map_add, map_one, map_zero] using congrArg σ h
      by_cases ht : 1 + t = 0
      · have hF := hzero.mpr ht
        simp [placedDirection, mapDirection, PlaneLinearMap.directionMap,
          PlaneLinearMap.extra, ht, hF]
      · have hF : 1 + σ t ≠ 0 := fun h => ht (hzero.mp h)
        simp [placedDirection, mapDirection, PlaneLinearMap.directionMap,
          PlaneLinearMap.extra, ht, hF, map_div₀, map_add, map_mul]

variable [instFintypek : Fintype k]

theorem extra_allDirections_image (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    (Finset.univ.image
      (placedDirection σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)))) =
      Finset.univ.image (mapDirection σ) := by
  ext d
  constructor
  · intro hd
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_image.mpr
      ⟨(PlaneLinearMap.extra u v huv).directionMap e, Finset.mem_univ _,
        (extra_placedDirection σ u v huv e).symm⟩
  · intro hd
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨a, ha⟩ := (PlaneLinearMap.extra u v huv).directionMap_bijective.surjective e
    refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
    rw [extra_placedDirection σ u v huv a, ha]

theorem extra_axisDirections (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    axisDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) =
      {some (σ u), some (σ v)} := let _ := instFintypek; by
  simp [axisDirections, placedDirection, mapDirection, Finset.pair_comm]

theorem alteredDirections_eq_allDirections_sdiff_axisDirections
    (σ : k →+* F) (M : PlaneLinearMap F) :
    alteredDirections σ M =
      (Finset.univ.image (placedDirection σ M)) \ axisDirections σ M := by
  ext d
  constructor
  · intro hd
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · obtain ⟨t, _, rfl⟩ := (mem_alteredDirections_iff σ M d).mp hd
      exact Finset.mem_image.mpr ⟨some t, Finset.mem_univ _, rfl⟩
    · intro ha
      exact Finset.disjoint_left.mp (disjoint_alteredDirections_axisDirections σ M) hd ha
  · intro hd
    obtain ⟨hf, hn⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hf
    rcases Finset.mem_union.mp (placedDirection_mem_altered_or_axis σ M a) with ha | ha
    · exact ha
    · exact False.elim (hn ha)

theorem extra_alteredDirections (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    alteredDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) =
      (Finset.univ.image (mapDirection σ)) \ {some (σ u), some (σ v)} := by
  rw [alteredDirections_eq_allDirections_sdiff_axisDirections,
    extra_allDirections_image σ u v huv, extra_axisDirections σ u v huv]

theorem none_mem_extra_alteredDirections (σ : k →+* F) (u v : k) (huv : u ≠ v) :
    none ∈ alteredDirections σ
      (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) := by
  rw [extra_alteredDirections σ u v huv]
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩
  · simp

theorem zero_mem_extra_alteredDirections (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    some 0 ∈ alteredDirections σ
      (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) := by
  have hσu : σ u ≠ 0 := by
    intro h
    apply hu
    apply σ.injective
    simpa only [map_zero] using h
  have hσv : σ v ≠ 0 := by
    intro h
    apply hv
    apply σ.injective
    simpa only [map_zero] using h
  rw [extra_alteredDirections σ u v huv]
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨some 0, Finset.mem_univ _, by simp [mapDirection]⟩
  · simp [Ne.symm hσu, Ne.symm hσv]

theorem diagonal_one_axisDirections_subset_extra_alteredDirections
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0) :
    axisDirections σ (PlaneLinearMap.diagonal (1 : F) one_ne_zero) ⊆
      alteredDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) := by
  intro d hd
  rcases (mem_axisDirections_iff σ (PlaneLinearMap.diagonal (1 : F) one_ne_zero) d).mp hd
      with h | h
  · have hd' : d = none := by simpa [placedDirection, mapDirection] using h
    subst d
    simpa [placedDirection, mapDirection] using none_mem_extra_alteredDirections σ u v huv
  · have hd' : d = some 0 := by simpa [placedDirection, mapDirection] using h
    subst d
    simpa [placedDirection, mapDirection] using zero_mem_extra_alteredDirections σ u v huv hu hv

theorem extra_axisDirections_subset_diagonal_one_alteredDirections
    (σ : k →+* F) (u v : k) (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0) :
    axisDirections σ (PlaneLinearMap.extra (σ u) (σ v) (σ.injective.ne huv)) ⊆
      alteredDirections σ (PlaneLinearMap.diagonal (1 : F) one_ne_zero) := by
  intro d hd
  rw [extra_axisDirections σ u v huv] at hd
  rcases Finset.mem_insert.mp hd with hd | hd
  · subst d
    simpa [placedDirection, mapDirection] using
      placedDirection_mem_alteredDirections σ
        (PlaneLinearMap.diagonal (1 : F) one_ne_zero) u hu
  · have hd' : d = some (σ v) := Finset.mem_singleton.mp hd
    subst d
    simpa [placedDirection, mapDirection] using
      placedDirection_mem_alteredDirections σ
        (PlaneLinearMap.diagonal (1 : F) one_ne_zero) v hv

end RyserCoveringCounterexample.Construction

end OAI
