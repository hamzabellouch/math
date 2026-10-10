import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HorseshoeProjectiveTowers

namespace OAI

/-! # Exactness at the middle coefficient in complete cohomology -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCompleteCohomology_middle_exact (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology p S.X₂)
    (hx : shiftedCompletedCohomologyMap p S.g x = 0) :
    ∃ y : ShiftedCompletedCohomology p S.X₁, shiftedCompletedCohomologyMap p S.f y = x := by
  let L := horseshoeLeftTower S hS
  let M := horseshoeMiddleTower S hS
  let R := horseshoeRightTower S hS
  let f := horseshoeTowerInl S hS
  let g := horseshoeTowerSnd S hS
  let eL := L.completeCohomologyEquiv (L.obj 0) (Iso.refl _) p
  let eM := M.completeCohomologyEquiv (M.obj 0) (Iso.refl _) p
  let eR := R.completeCohomologyEquiv (R.obj 0) (Iso.refl _) p
  let z := eM.symm x
  have hz : g.cohomologyMap p z = 0 := by
    apply eR.injective
    rw [map_zero]
    have h := IntegralProjectiveTower.completeCohomologyEquiv_natural g p z
    change eR (g.cohomologyMap p z) = shiftedCompletedCohomologyMap p S.g (eM z) at h
    rw [show eM z = x from eM.apply_symm_apply x] at h
    exact h.trans hx
  obtain ⟨a, ha⟩ := IntegralProjectiveTower.cohomology_exact f g
    (horseshoeTower_zero S hS) (horseshoeTower_shortExact S hS) p z hz
  refine ⟨eL a, ?_⟩
  have h := IntegralProjectiveTower.completeCohomologyEquiv_natural f p a
  change eM (f.cohomologyMap p a) = shiftedCompletedCohomologyMap p S.f (eL a) at h
  rw [ha] at h
  exact h.symm.trans (eM.apply_symm_apply x)

theorem shiftedCompleteCohomology_shortExact_middle (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (S.map (shiftedCompletedCohomologyFunctor p)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  exact shiftedCompleteCohomology_middle_exact p S hS x hx

end PolycyclicRecognition

end

end OAI
