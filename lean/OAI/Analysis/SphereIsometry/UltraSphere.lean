import OAI.Analysis.SphereIsometry.UnitRepresentatives
import OAI.Analysis.SphereIsometry.UltraNormed

namespace OAI

/-!
# The actual sphere map on the ultranorm quotient

Unit representatives exist even when the original coordinates vanish. The map
and its inverse are induced coordinatewise, and every fixed real radius has the
exact ultralimit defect formula.
-/

noncomputable section
namespace Tingley
open Filter
open scoped Topology

universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Every sequence of unit vectors is uniformly bounded. -/
def unitSequence (U : Ultrafilter ℕ) (s : ℕ → UnitSphere X) : UltraSequence U X :=
  UltraSequence.ofBounded U (fun n => (s n : X)) ⟨1, zero_le_one, fun n => by simp⟩

@[simp] theorem unitSequence_apply (U : Ultrafilter ℕ) (s : ℕ → UnitSphere X) (n : ℕ) :
    unitSequence U s n = (s n : X) := rfl

/-- The actual class of a sequence of unit vectors. -/
def unitClass (U : Ultrafilter ℕ) (s : ℕ → UnitSphere X) : UnitSphere (UltraQuotient U X) :=
  ⟨classOf U (unitSequence U s), by simp only [norm_classOf, unitSequence_apply,
    UnitSphere.norm_coe, realULim_const]⟩

@[simp] theorem unitClass_val (U : Ultrafilter ℕ) (s : ℕ → UnitSphere X) :
    (unitClass U s : UltraQuotient U X) = classOf U (unitSequence U s) := rfl

theorem norm_sub_unitClass (U : Ultrafilter ℕ) (s t : ℕ → UnitSphere X) :
    ‖(unitClass U s : UltraQuotient U X) - (unitClass U t : UltraQuotient U X)‖ =
      realULim U (fun n => ‖(s n : X) - (t n : X)‖) := by
  simpa only [unitClass_val, unitSequence_apply] using
    norm_sub_classOf U (unitSequence U s) (unitSequence U t)

theorem unitClass_eq_iff (U : Ultrafilter ℕ) (s t : ℕ → UnitSphere X) :
    unitClass U s = unitClass U t ↔ realULim U (fun n => ‖(s n : X) - (t n : X)‖) = 0 := by
  rw [Subtype.ext_iff]
  exact classOf_eq_iff U (unitSequence U s) (unitSequence U t)

theorem unitClass_surjective [Nontrivial X] (U : Ultrafilter ℕ) :
    Function.Surjective (unitClass U : (ℕ → UnitSphere X) → UnitSphere (UltraQuotient U X)) := by
  classical
  intro z
  obtain ⟨a, ha⟩ := classOf_surjective U X (z : UltraQuotient U X)
  let e : UnitSphere X := Classical.choice inferInstance
  let s : ℕ → UnitSphere X := fun n => unitize e (a n)
  have ha1 : realULim U (fun n => ‖a n‖) = 1 := by
    rw [← norm_classOf, ha]
    exact z.property
  have hlim : Tendsto (fun n => ‖a n‖) (U : Filter ℕ) (𝓝 (1 : ℝ)) := by
    simpa only [ha1] using tendsto_realULim U (UltraSequence.norm_bounded a)
  have he : realULim U (fun n => ‖a n - (s n : X)‖) = 0 := by
    apply realULim_eq_of_tendsto U
    simpa only [s, norm_sub_unitize, sub_self, abs_zero] using
      (hlim.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  refine ⟨s, ?_⟩
  apply Subtype.ext
  change classOf U (unitSequence U s) = (z : UltraQuotient U X)
  rw [← ha]
  exact ((classOf_eq_iff U a (unitSequence U s)).2 he).symm

/-- Choice selects actual unit representatives after surjectivity is proved. -/
def unitRep [Nontrivial X] (U : Ultrafilter ℕ) (z : UnitSphere (UltraQuotient U X)) :
    ℕ → UnitSphere X :=
  Classical.choose (unitClass_surjective U z)

@[simp] theorem unitRep_spec [Nontrivial X] (U : Ultrafilter ℕ)
    (z : UnitSphere (UltraQuotient U X)) : unitClass U (unitRep U z) = z :=
  Classical.choose_spec (unitClass_surjective U z)

theorem unitClass_map_eq (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (s t : ℕ → UnitSphere X) (h : unitClass U s = unitClass U t) :
    unitClass U (fun n => f (s n)) = unitClass U (fun n => f (t n)) := by
  apply (unitClass_eq_iff U _ _).2
  simpa only [sphere_norm_sub] using (unitClass_eq_iff U s t).1 h

def ultraSphereMap [Nontrivial X] (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (z : UnitSphere (UltraQuotient U X)) : UnitSphere (UltraQuotient U Y) :=
  unitClass U (fun n => f (unitRep U z n))

@[simp] theorem ultraSphereMap_unitClass [Nontrivial X] (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (s : ℕ → UnitSphere X) :
    ultraSphereMap U f (unitClass U s) = unitClass U (fun n => f (s n)) :=
  unitClass_map_eq U f _ s (unitRep_spec U (unitClass U s))

theorem ultraSphereMap_isometry [Nontrivial X] (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) : Isometry (ultraSphereMap U f) := by
  apply Isometry.of_dist_eq
  intro z w
  calc
    dist (ultraSphereMap U f z) (ultraSphereMap U f w) =
        dist (unitClass U (unitRep U z)) (unitClass U (unitRep U w)) := by
      simp only [ultraSphereMap, Subtype.dist_eq, dist_eq_norm, norm_sub_unitClass,
        sphere_norm_sub]
    _ = dist z w := by rw [unitRep_spec, unitRep_spec]

/-- Surjectivity comes from the actual coordinatewise inverse, not from isometry alone. -/
def ultraSphereEquiv [Nontrivial X] [Nontrivial Y] (U : Ultrafilter ℕ)
    (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    UnitSphere (UltraQuotient U X) ≃ᵢ UnitSphere (UltraQuotient U Y) where
  toFun := ultraSphereMap U f
  invFun := ultraSphereMap U f.symm
  left_inv z := by
    obtain ⟨s, rfl⟩ := unitClass_surjective U z
    simp only [ultraSphereMap_unitClass, IsometryEquiv.symm_apply_apply]
  right_inv z := by
    obtain ⟨s, rfl⟩ := unitClass_surjective U z
    simp only [ultraSphereMap_unitClass, IsometryEquiv.apply_symm_apply]
  isometry_toFun := ultraSphereMap_isometry U f

@[simp] theorem ultraSphereEquiv_unitClass [Nontrivial X] [Nontrivial Y]
    (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y) (s : ℕ → UnitSphere X) :
    ultraSphereEquiv U f (unitClass U s) = unitClass U (fun n => f (s n)) :=
  ultraSphereMap_unitClass U f s

@[simp] theorem ultraSphereEquiv_symm [Nontrivial X] [Nontrivial Y]
    (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    (ultraSphereEquiv U f).symm = ultraSphereEquiv U f.symm := by
  ext z
  rfl

/-- The radius-scaled norm is inherited from the linear quotient projection. -/
theorem norm_sub_smul_unitClass (U : Ultrafilter ℕ) (q : ℝ) (s t : ℕ → UnitSphere X) :
    ‖(unitClass U s : UltraQuotient U X) - q • (unitClass U t : UltraQuotient U X)‖ =
      realULim U (fun n => ‖(s n : X) - q • (t n : X)‖) := by
  change ‖classOf U (unitSequence U s) - q • classOf U (unitSequence U t)‖ = _
  rw [← classOf_smul, ← classOf_sub, norm_classOf]
  rfl

theorem unitPairNorm_bounded (q : ℝ) (s t : ℕ → UnitSphere X) :
    RealSeqBounded (fun n => ‖(s n : X) - q • (t n : X)‖) := by
  refine ⟨1 + |q|, fun n => ?_⟩
  rw [abs_of_nonneg (norm_nonneg _)]
  calc
    ‖(s n : X) - q • (t n : X)‖ ≤ ‖(s n : X)‖ + ‖q • (t n : X)‖ := norm_sub_le _ _
    _ = 1 + |q| := by simp only [norm_smul, Real.norm_eq_abs, UnitSphere.norm_coe, mul_one]

theorem signedDefect_sequence_bounded (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (q : ℝ) (s t : ℕ → UnitSphere X) :
    RealSeqBounded (fun n => signedDefect f q (s n) (t n)) :=
  (unitPairNorm_bounded q (fun n => f (s n)) (fun n => f (t n))).sub
    (unitPairNorm_bounded q s t)

/-- Exact defect formula at every fixed real radius. -/
theorem signedDefect_ultraSphereEquiv [Nontrivial X] [Nontrivial Y]
    (U : Ultrafilter ℕ) (f : UnitSphere X ≃ᵢ UnitSphere Y) (q : ℝ)
    (s t : ℕ → UnitSphere X) :
    signedDefect (ultraSphereEquiv U f) q (unitClass U s) (unitClass U t) =
      realULim U (fun n => signedDefect f q (s n) (t n)) := by
  simp only [signedDefect, ultraSphereEquiv_unitClass, norm_sub_smul_unitClass]
  exact (realULim_sub U
    (unitPairNorm_bounded q (fun n => f (s n)) (fun n => f (t n)))
    (unitPairNorm_bounded q s t)).symm

/-- One ultrafilter transfers the bound for each arbitrarily chosen real radius. -/
theorem HasDefectBound.ultraSphereEquiv [Nontrivial X] [Nontrivial Y]
    {f : UnitSphere X ≃ᵢ UnitSphere Y} {M : ℝ} (h : HasDefectBound f M)
    (U : Ultrafilter ℕ) : HasDefectBound (ultraSphereEquiv U f) M := by
  intro q hq z w
  obtain ⟨s, rfl⟩ := unitClass_surjective U z
  obtain ⟨t, rfl⟩ := unitClass_surjective U w
  rw [signedDefect_ultraSphereEquiv, ← realULim_abs U (signedDefect_sequence_bounded f q s t)]
  exact realULim_le_of_eventually_le U (signedDefect_sequence_bounded f q s t).abs
    (Filter.Eventually.of_forall fun n => h q hq (s n) (t n))

end Tingley

end

end OAI
