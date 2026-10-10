import OAI.Probability.RadialTransition.IdealUniform

namespace OAI

universe uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def finiteMax {ι : Type uIndex} [Fintype ι] (f : ι → ℝ) : ℝ := sSup (range f)
lemma finiteMax_le {ι : Type uIndex} [Fintype ι] [Nonempty ι] (f : ι → ℝ) {c : ℝ}
    (hc : ∀ i, f i ≤ c) : finiteMax f ≤ c := csSup_le (range_nonempty f) (by rintro _ ⟨i,rfl⟩; exact hc i)
lemma le_finiteMax {ι : Type uIndex} [Fintype ι] (f : ι → ℝ) (i : ι) : f i ≤ finiteMax f :=
  le_csSup (Finite.bddAbove_range f) (mem_range_self i)
lemma finiteMax_attained {ι : Type uIndex} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ∃ i, finiteMax f = f i := by
  obtain ⟨i, hi⟩ := Finite.exists_max f
  exact ⟨i, le_antisymm (finiteMax_le f hi) (le_finiteMax f i)⟩

def phaseMass : ℝ := 3/(2*packingDensity)
def phaseDensity : Fin 3 → ℝ := ![0,packingDensity,4*packingDensity]
def phaseOffset : Fin 3 → ℝ := ![0,0,-9*packingDensity]
def limitingPlane (i : Fin 3) (β h : ℝ) : ℝ :=
  phaseDensity i*h+phaseOffset i+β*phaseMass/2*(phaseDensity i)^2
def threePlane (β h : ℝ) : ℝ := finiteMax (fun i => limitingPlane i β h)

lemma phaseMass_pos : 0 < phaseMass := div_pos (by norm_num) (mul_pos (by norm_num) packingDensity_pos)

lemma phaseDensity_bounds (i : Fin 3) : 0 ≤ phaseDensity i ∧ phaseDensity i ≤ 4*packingDensity := by
  have hp := packingDensity_pos
  fin_cases i
  · change 0 ≤ (0:ℝ) ∧ 0 ≤ 4*packingDensity
    constructor <;> positivity
  · change 0 ≤ packingDensity ∧ packingDensity ≤ 4*packingDensity
    constructor <;> linarith
  · change 0 ≤ 4*packingDensity ∧ 4*packingDensity ≤ 4*packingDensity
    constructor
    · positivity
    · exact le_rfl

lemma bareLimit_finiteMax (h : ℝ) : bareLimit h = finiteMax (fun i => phaseDensity i*h+phaseOffset i) := by
  apply le_antisymm
  · apply max_le
    · simpa [phaseDensity, phaseOffset] using le_finiteMax (fun i => phaseDensity i*h+phaseOffset i) 0
    apply max_le
    · simpa [phaseDensity, phaseOffset] using le_finiteMax (fun i => phaseDensity i*h+phaseOffset i) 1
    · calc
        packingDensity*(4*h-9) = phaseDensity 2*h+phaseOffset 2 := by dsimp [phaseDensity, phaseOffset]; ring
        _ ≤ _ := le_finiteMax (fun i => phaseDensity i*h+phaseOffset i) 2
  · apply finiteMax_le
    intro i
    fin_cases i
    · simp [phaseDensity, phaseOffset, bareLimit]
    · simp [phaseDensity, phaseOffset, bareLimit]
    · have hh := (le_max_right (packingDensity*h) (packingDensity*(4*h-9))).trans (le_max_right 0 (max (packingDensity*h) (packingDensity*(4*h-9))))
      dsimp [phaseDensity, phaseOffset]
      unfold bareLimit
      nlinarith

lemma limiting_branch_attained (β h u : ℝ) : ∃ i : Fin 3,
    attractionBranch (fun _ h => bareLimit h) phaseMass u β h =
      limitingPlane i β h-β*phaseMass/2*(u-phaseDensity i)^2 := by
  obtain ⟨i, hi⟩ := finiteMax_attained (fun i => phaseDensity i*(h+β*phaseMass*u)+phaseOffset i)
  refine ⟨i, ?_⟩
  dsimp only [attractionBranch]
  rw [bareLimit_finiteMax, hi]
  unfold limitingPlane
  ring

lemma limiting_branch_ge (β h u : ℝ) (i : Fin 3) :
    limitingPlane i β h-β*phaseMass/2*(u-phaseDensity i)^2 ≤
      attractionBranch (fun _ h => bareLimit h) phaseMass u β h := by
  have hh := le_finiteMax (fun i => phaseDensity i*(h+β*phaseMass*u)+phaseOffset i) i
  dsimp only [attractionBranch]
  rw [bareLimit_finiteMax]
  unfold limitingPlane
  nlinarith

lemma limiting_branch_le {β : ℝ} (hβ : 0 ≤ β) (h u : ℝ) :
    attractionBranch (fun _ h => bareLimit h) phaseMass u β h ≤ threePlane β h := by
  obtain ⟨i, hi⟩ := limiting_branch_attained β h u
  rw [hi]
  have hh := le_finiteMax (fun i => limitingPlane i β h) i
  change limitingPlane i β h-β*phaseMass/2*(u-phaseDensity i)^2 ≤ finiteMax _
  have hA := phaseMass_pos
  nlinarith [mul_nonneg (show 0 ≤ β*phaseMass/2 by positivity) (sq_nonneg (u-phaseDensity i))]

lemma ideal_approx_threePlane {Q : Pressure} {β h U ε u : ℝ} (hβ : 0 ≤ β)
    (hU : 4*packingDensity ≤ U) (hu : ActiveShift Q phaseMass β h u) (hub : u ∈ Icc (0:ℝ) U)
    (he : ∀ v ∈ Icc (0:ℝ) U, |Q β (h+β*phaseMass*v)-bareLimit (h+β*phaseMass*v)| ≤ ε) :
    |idealAttraction Q phaseMass β h-threePlane β h| ≤ ε := by
  rw [idealAttraction_eq_of_active hu, abs_le]
  constructor
  · obtain ⟨i, hi⟩ := finiteMax_attained (fun i => limitingPlane i β h)
    have hib : phaseDensity i ∈ Icc (0:ℝ) U := ⟨(phaseDensity_bounds i).1, (phaseDensity_bounds i).2.trans hU⟩
    have happ := (abs_le.mp (he _ hib)).1
    have hg := limiting_branch_ge β h (phaseDensity i) i
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at hg
    have hm := hu (phaseDensity i)
    change threePlane β h = limitingPlane i β h at hi
    rw [hi]
    dsimp only [attractionBranch] at hg hm ⊢
    linarith
  · have happ := (abs_le.mp (he u hub)).2
    have hg := limiting_branch_le hβ h u
    dsimp only [attractionBranch] at hg ⊢
    linarith

lemma active_near_phase {Q : Pressure} {β h U ε u : ℝ} (hβ : 0 ≤ β)
    (hU : 4*packingDensity ≤ U) (hu : ActiveShift Q phaseMass β h u) (hub : u ∈ Icc (0:ℝ) U)
    (he : ∀ v ∈ Icc (0:ℝ) U, |Q β (h+β*phaseMass*v)-bareLimit (h+β*phaseMass*v)| ≤ ε) :
    ∃ i : Fin 3, β*phaseMass/2*(u-phaseDensity i)^2 ≤ 2*ε := by
  have hp := (abs_le.mp (ideal_approx_threePlane hβ hU hu hub he)).1
  rw [idealAttraction_eq_of_active hu] at hp
  have ha := (abs_le.mp (he u hub)).2
  obtain ⟨i, hi⟩ := limiting_branch_attained β h u
  refine ⟨i, ?_⟩
  have hh := le_finiteMax (fun i => limitingPlane i β h) i
  change limitingPlane i β h ≤ threePlane β h at hh
  dsimp only [attractionBranch] at hi hp
  linarith

end RadialTransition
end

end OAI
