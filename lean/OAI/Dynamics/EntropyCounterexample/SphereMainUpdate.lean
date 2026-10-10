import OAI.Dynamics.EntropyCounterexample.SphereTranslation
import OAI.Dynamics.EntropyCounterexample.SphereDoubling

namespace OAI

noncomputable section

namespace Problem340.SphereMainUpdate

def update (c : ℂ) (x : StandardSphere2) : StandardSphere2 :=
  SphereTranslation.translate c (SphereDoubling.sphereMap x)

def ambient (c : ℂ) (x : SphereAmbient) : SphereAmbient :=
  SphereTranslation.ambient c (SphereDoubling.ambientMap x)

@[simp] theorem coe_update (c : ℂ) (x : StandardSphere2) :
    (update c x).1 = ambient c x.1 := rfl

@[continuity, fun_prop] theorem continuous_update :
    Continuous (fun p : ℂ × StandardSphere2 => update p.1 p.2) :=
  SphereTranslation.continuous_translate.comp
    (continuous_fst.prodMk (SphereDoubling.continuous_sphereMap.comp continuous_snd))

theorem contDiffAt_ambient (n : WithTop ℕ∞) (c : ℂ) (x : StandardSphere2) :
    ContDiffAt ℝ n (fun p : ℂ × SphereAmbient => ambient p.1 p.2) (c, x.1) := by
  have hi : ContDiff ℝ n (fun p : ℂ × SphereAmbient =>
      (p.1, SphereDoubling.ambientMap p.2)) :=
    contDiff_fst.prodMk ((SphereDoubling.contDiff_ambientMap n).comp contDiff_snd)
  change ContDiffAt ℝ n
    ((fun q : ℂ × SphereAmbient => SphereTranslation.ambient q.1 q.2) ∘
      (fun p : ℂ × SphereAmbient => (p.1, SphereDoubling.ambientMap p.2))) (c, x.1)
  exact (SphereTranslation.contDiffAt_ambient n c (SphereDoubling.sphereMap x)).comp
    (f := fun p : ℂ × SphereAmbient => (p.1, SphereDoubling.ambientMap p.2))
    (c, x.1) hi.contDiffAt

theorem chart_eq_stereoCoordinate (x : SphereAmbient) :
    SphereTranslation.chart x = SphereDoubling.stereoCoordinate x := by
  unfold SphereTranslation.chart SphereDoubling.stereoCoordinate
  rw [show (1 : ℂ) - (x 2 : ℂ) = ((1 - x 2 : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.div_ofReal]
  simp

theorem chart_update (c : ℂ) (x : StandardSphere2) (hx : x ≠ SphereDoubling.north) :
    SphereTranslation.chart (update c x).1 = SphereTranslation.chart x.1 ^ 2 + c := by
  rw [update, SphereTranslation.translate]
  rw [SphereTranslation.chart_ambient c (SphereDoubling.sphereMap x)
    (SphereDoubling.ambientMap_third_ne_one (mt (SphereDoubling.eq_north_iff x).mpr hx))]
  rw [chart_eq_stereoCoordinate, SphereDoubling.stereoCoordinate_sphereMap hx,
    chart_eq_stereoCoordinate]

@[simp] theorem update_north (c : ℂ) :
    update c SphereDoubling.north = SphereDoubling.north := by
  unfold update
  rw [SphereDoubling.sphereMap_north]
  apply Subtype.ext
  exact SphereTranslation.ambient_north c

theorem update_ne_north (c : ℂ) (x : StandardSphere2) (hx : x ≠ SphereDoubling.north) :
    update c x ≠ SphereDoubling.north := by
  intro h
  have hn := (SphereDoubling.eq_north_iff (update c x)).mp h
  exact SphereTranslation.ambient_not_north c (SphereDoubling.sphereMap x)
    (SphereDoubling.ambientMap_third_ne_one (mt (SphereDoubling.eq_north_iff x).mpr hx)) hn

@[simp] theorem update_eq_north_iff (c : ℂ) (x : StandardSphere2) :
    update c x = SphereDoubling.north ↔ x = SphereDoubling.north := by
  constructor
  · intro h
    by_contra hx
    exact update_ne_north c x hx h
  · rintro rfl
    exact update_north c

@[simp] theorem update_zero (x : StandardSphere2) : update 0 x = SphereDoubling.sphereMap x :=
  SphereTranslation.translate_zero _

def squaring : ContinuousMap StandardSphere2 StandardSphere2 :=
  ⟨SphereDoubling.sphereMap, SphereDoubling.continuous_sphereMap⟩

def continuousMap {X : Type*} [TopologicalSpace X]
    (C : ContinuousMap X ℂ) (g : ContinuousMap X StandardSphere2) :
    ContinuousMap X StandardSphere2 :=
  SphereTranslation.continuousMap C (squaring.comp g)

@[simp] theorem continuousMap_apply {X : Type*} [TopologicalSpace X]
    (C : ContinuousMap X ℂ) (g : ContinuousMap X StandardSphere2) (x : X) :
    continuousMap C g x = update (C x) (g x) := rfl

def homotopy {X : Type*} [TopologicalSpace X]
    (C : ContinuousMap X ℂ) (g : ContinuousMap X StandardSphere2) :
    ContinuousMap.Homotopy (squaring.comp g) (continuousMap C g) :=
  SphereTranslation.homotopy C (squaring.comp g)

theorem orbit_ne_north (c : ℕ → ℂ) (x : ℕ → StandardSphere2)
    (hrec : ∀ n, x (n + 1) = update (c n) (x n))
    (hx : x 0 ≠ SphereDoubling.north) : ∀ n, x n ≠ SphereDoubling.north := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [hrec n]
      exact update_ne_north (c n) (x n) ih

theorem chart_orbit_recurrence (c : ℕ → ℂ) (x : ℕ → StandardSphere2)
    (hrec : ∀ n, x (n + 1) = update (c n) (x n))
    (hx : x 0 ≠ SphereDoubling.north) (n : ℕ) :
    SphereTranslation.chart (x (n + 1)).1 =
      SphereTranslation.chart (x n).1 ^ 2 + c n := by
  rw [hrec n]
  exact chart_update (c n) (x n) (orbit_ne_north c x hrec hx n)

end Problem340.SphereMainUpdate

end

end OAI
