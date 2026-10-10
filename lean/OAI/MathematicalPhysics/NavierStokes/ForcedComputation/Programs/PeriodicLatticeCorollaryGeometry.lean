import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLatticeTransform

namespace OAI

/-! The exact label and open slab of the rapid torus corollary. -/

noncomputable section
open Set
open scoped ContDiff BigOperators
namespace PeriodicLattice.RapidTorus
open TorusCalculus Planar Scales

def corollaryStart : Space := WithLp.toLp 2 ![1 / 2, 1 / 4, 1 / 2]
def corollaryDetector : Set Torus :=
  {q | ∃ s : ℝ, 1 / 4 < s ∧ s < 3 / 8 ∧ (s : UnitAddCircle) = q 0}

def pointTransform (x : Space) : Space :=
  transverseLinear x + WithLp.toLp 2 ![5 / 8, -(1 / 4), 0]

theorem pointTransform_first (x : Space) :
    pointTransform x 0 = 5 / 8 - x 0 / 2 := by
  simp [pointTransform, transverseLinear_apply, PiLp.add_apply]
  ring

theorem pointTransform_second (x : Space) : pointTransform x 1 = x 1 - 1 / 4 := by
  simp [pointTransform, transverseLinear_apply, PiLp.add_apply, sub_eq_add_neg]

theorem pointTransform_third (x : Space) : pointTransform x 2 = x 2 := by
  simp [pointTransform, transverseLinear_apply, PiLp.add_apply]

theorem pointTransform_initial : pointTransform initialParticle = corollaryStart := by
  ext i
  fin_cases i <;> norm_num [pointTransform, transverseLinear_apply, initialParticle,
    corollaryStart, PiLp.add_apply]

theorem corollaryDetector_open : IsOpen corollaryDetector := by
  have he : corollaryDetector = (fun q : Torus => q 0) ⁻¹'
      ((fun s : ℝ => (s : UnitAddCircle)) '' Ioo (1 / 4) (3 / 8)) := by
    ext q
    simp [corollaryDetector, and_assoc]
  rw [he]
  have hopen : IsOpen ((fun s : ℝ => (s : UnitAddCircle)) '' Ioo (1 / 4) (3 / 8)) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  exact hopen.preimage (continuous_apply 0)

theorem corollaryDetector_mem {x : Space} (hx0 : 0 ≤ x 0) (hx1 : x 0 < 1) :
    torusMk x ∈ corollaryDetector ↔ 1 / 4 < x 0 ∧ x 0 < 3 / 8 := by
  constructor
  · rintro ⟨s, hs0, hs1, he⟩
    have hx : x 0 ∈ Ico (0 : ℝ) (0 + 1) := ⟨hx0, by simpa using hx1⟩
    have hs : s ∈ Ico (0 : ℝ) (0 + 1) := ⟨by linarith, by linarith⟩
    have h := (AddCircle.coe_eq_coe_iff_of_mem_Ico hs hx).mp he
    exact h ▸ ⟨hs0, hs1⟩
  · exact fun h => ⟨x 0, h.1, h.2, rfl⟩

theorem transformed_curve_event {b : ℕ} (hb : 2 ≤ b) (L : ℕ) (c : ℕ → ℕ)
    (H : ℕ → ℤ → Bool) :
    (∃ t : ℝ, 0 ≤ t ∧
      torusMk (pointTransform (embed (curve b L c H t))) ∈ corollaryDetector) ↔
      ∃ n : ℕ, H n (c n) = true := by
  constructor
  · rintro ⟨t, ht, hevent⟩
    by_contra hn
    have hall : ∀ n, H n (c n) = false := by
      intro n
      exact Bool.eq_false_iff.mpr (fun hh => hn ⟨n, hh⟩)
    obtain ⟨hlo, hhi⟩ := curve_no_signal hb L c H hall ht
    have hp0 : 0 ≤ pointTransform (embed (curve b L c H t)) 0 := by
      rw [pointTransform_first, embed_first]
      linarith
    have hp1 : pointTransform (embed (curve b L c H t)) 0 < 1 := by
      rw [pointTransform_first, embed_first]
      linarith
    have hh := (corollaryDetector_mem hp0 hp1).mp hevent
    rw [pointTransform_first, embed_first] at hh
    linarith
  · intro hn
    let n := Nat.find hn
    have hs : H n (c n) = true := Nat.find_spec hn
    have hp : ∀ m < n, H m (c m) = false := by
      intro m hm
      exact Bool.eq_false_iff.mpr (Nat.find_min hn hm)
    have he : (curve b L c H (n + 2)).1 = 1 / 2 + beta b L (n + 1) := by
      rw [curve_x_slot b L c H n hp (by linarith) le_rfl, hs,
        Profiles.clock_one (by linarith), Signal.halting_end]
    have hβ0 := beta_pos hb L (n + 1)
    have hβ1 : beta b L (n + 1) < 1 / 4 := by
      simpa only [beta_zero] using beta_strictAnti hb L (Nat.succ_pos n)
    have hlo : 1 / 4 < pointTransform (embed (curve b L c H (n + 2))) 0 := by
      rw [pointTransform_first, embed_first, he]
      linarith
    have hhi : pointTransform (embed (curve b L c H (n + 2))) 0 < 3 / 8 := by
      rw [pointTransform_first, embed_first, he]
      linarith
    exact ⟨(n : ℝ) + 2, by positivity,
      (corollaryDetector_mem (by linarith) (by linarith)).mpr ⟨hlo, hhi⟩⟩

theorem transformed_path_event (d : Input) (hd : d.WellFormed) :
    (∃ t : ℝ, 0 ≤ t ∧
      torusMk (pointTransform (FluidLift.path d t)) ∈ corollaryDetector) ↔ Halts d := by
  have he := CompilerPlanar.path_event_iff d hd
  rw [CompilerPlanar.path, curve_event_iff (CompilerPlanar.radix_ge_two d)] at he
  exact (transformed_curve_event (CompilerPlanar.radix_ge_two d) _ _ _).trans he

theorem velocity_shift_pointTransform (d : Input) (t : ℝ) (x : Space) :
    FluidLift.velocity d t (shift (torusMk (pointTransform x))) =
      FluidLift.velocity d t (torusMk x) := by
  rw [shift, ← mk_add, FluidLift.velocity_cover, FluidLift.velocity_cover]
  have hy : (pointTransform x + shiftVector) 1 = x 1 := by
    rw [PiLp.add_apply, pointTransform_second]
    norm_num [shiftVector]
  have hz : (pointTransform x + shiftVector) 2 = x 2 := by
    rw [PiLp.add_apply, pointTransform_third]
    norm_num [shiftVector]
  rw [hy, hz]

def corollaryPath (d : Input) (t : ℝ) : Space := pointTransform (FluidLift.path d t)

theorem corollaryPath_start (d : Input) : corollaryPath d 0 = corollaryStart := by
  rw [corollaryPath, FluidLift.path_start, pointTransform_initial]

theorem corollaryPath_hasDerivAt (d : Input) (hd : d.WellFormed) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (corollaryPath d)
      (transformedField (FluidLift.velocity d) t (torusMk (corollaryPath d t))) t := by
  have h := (transverseLinear.hasFDerivAt.comp_hasDerivAt t
    (FluidLift.path_hasDerivAt d hd ht)).add_const
      (WithLp.toLp 2 ![5 / 8, -(1 / 4), 0] : Space)
  change HasDerivAt (corollaryPath d)
    (transverseLinear (FluidLift.velocity d t (torusMk (FluidLift.path d t)))) t at h
  simpa only [transformedField, shiftedField, corollaryPath,
    velocity_shift_pointTransform] using h

theorem corollaryPath_unique (d : Input) (hd : d.WellFormed) {Y : ℝ → Space}
    (hY₀ : Y 0 = corollaryStart)
    (hY : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt Y
      (transformedField (FluidLift.velocity d) t (torusMk (Y t))) (Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) : Y t = corollaryPath d t := by
  apply Trajectories.unique (v := fun s x => transformedField (FluidLift.velocity d) s (torusMk x))
    ((transformedField_smooth (FluidLift.velocity_contDiff d)).of_le
      (by exact WithTop.coe_le_coe.mpr le_top))
    hY (fun s hs => (corollaryPath_hasDerivAt d hd hs).hasDerivWithinAt) _ ht
  rw [hY₀, corollaryPath_start]

end PeriodicLattice.RapidTorus

end

end OAI
