import OAI.Dynamics.EntropyCounterexample.StandardSaturation

namespace OAI

noncomputable section

open Set
open scoped ContDiff

namespace Problem340

def standardRegisterUpdate (R : ℝ) (hR : 1 ≤ R) (a : ℝ) (c : ℂ)
    (x : StandardSphere2) : StandardSphere2 :=
  sphereOfComplex (a • standardSphereSaturation R hR x + c)

@[simp] theorem standardRegisterUpdate_affine (R : ℝ) (hR : 1 ≤ R)
    (a : ℝ) (c z : ℂ) :
    standardRegisterUpdate R hR a c (sphereOfComplex z) =
      sphereOfComplex (a • saturation R hR z + c) := by
  simp [standardRegisterUpdate]

@[simp] theorem standardRegisterUpdate_north (R : ℝ) (hR : 1 ≤ R)
    (a : ℝ) (c : ℂ) :
    standardRegisterUpdate R hR a c chartNorthPole = sphereOfComplex c := by
  simp [standardRegisterUpdate]

theorem standardRegisterUpdate_ne_north (R : ℝ) (hR : 1 ≤ R)
    (a : ℝ) (c : ℂ) (x : StandardSphere2) :
    standardRegisterUpdate R hR a c x ≠ chartNorthPole :=
  sphereOfComplex_ne_north _

theorem continuous_standardRegisterUpdate (R : ℝ) (hR : 1 ≤ R) :
    Continuous (fun p : ℝ × (ℂ × StandardSphere2) =>
      standardRegisterUpdate R hR p.1 p.2.1 p.2.2) := by
  exact continuous_sphereOfComplex.comp
    ((continuous_fst.smul ((standardSphereSaturation_continuous R hR).comp
      (continuous_snd.comp continuous_snd))).add (continuous_fst.comp continuous_snd))

theorem standardRegisterUpdate_local_ambient (R : ℝ) (hR : 1 ≤ R)
    (a : ℝ) (c : ℂ) (x : StandardSphere2) :
    ∃ U : Set (ℝ × (ℂ × SphereAmbient)), IsOpen U ∧
      (a, c, (x : SphereAmbient)) ∈ U ∧
      ∃ A : (ℝ × (ℂ × SphereAmbient)) → SphereAmbient, ContDiffOn ℝ ∞ A U ∧
        ∀ (b : ℝ) (d : ℂ) (y : StandardSphere2),
          (b, d, (y : SphereAmbient)) ∈ U →
          (standardRegisterUpdate R hR b d y : SphereAmbient) = A (b, d, y) := by
  obtain ⟨V, hV, hx, F, hF, hmatch⟩ := standardSphereSaturation_local_ambient R hR x
  let U : Set (ℝ × (ℂ × SphereAmbient)) := {p | p.2.2 ∈ V}
  have hU : IsOpen U := hV.preimage (continuous_snd.comp continuous_snd)
  have hFlift : ContDiffOn ℝ ∞ (fun p : ℝ × (ℂ × SphereAmbient) => F p.2.2) U :=
    hF.comp (contDiff_snd.comp contDiff_snd).contDiffOn (fun _ h => h)
  refine ⟨U, hU, hx, fun p => (sphereOfComplex (p.1 • F p.2.2 + p.2.1) : SphereAmbient), ?_, ?_⟩
  · exact contDiff_sphereOfComplex_val.comp_contDiffOn
      ((contDiff_fst.contDiffOn.smul hFlift).add
        (contDiff_fst.comp contDiff_snd).contDiffOn)
  · intro b d y hy
    change (sphereOfComplex (b • standardSphereSaturation R hR y + d) : SphereAmbient) = _
    rw [hmatch y hy]

theorem standardRegisterUpdate_eq_transport (R : ℝ) (hR : 1 ≤ R)
    (a : ℝ) (c : ℂ) (x : StandardSphere2) :
    standardRegisterUpdate R hR a c x =
      complexSphereHomeomorph
        ((a • sphereSaturation R hR (complexSphereHomeomorph.symm x) + c : ℂ) : OnePoint ℂ) := by
  simp only [complexSphereHomeomorph_coe, standardRegisterUpdate,
    standardSphereSaturation_eq_transport]

end Problem340

end

end OAI
