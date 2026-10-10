import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalWeakLimit

namespace OAI

/-! # A continuous physical limit lifts to a weakly continuous bounded Y path -/

open Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_homogeneous_weaklyContinuous_lift (a k M T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (v : C(Icc (0 : ℝ) T × E, ℂ))
    (hv : ∀ t : Icc (0 : ℝ) T, ∃ u : HomogeneousY a k,
      ‖u‖ ≤ M ∧ ∀ y, homogeneousPhysicalCLM a k ha ha1 hk u y = v (t, y)) :
    ∃ u : Icc (0 : ℝ) T → HomogeneousY a k,
      (∀ t, ‖u t‖ ≤ M) ∧
      (∀ t y, homogeneousPhysicalCLM a k ha ha1 hk (u t) y = v (t, y)) ∧
      ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ, Continuous (fun t => ℓ (u t)) := by
  classical
  choose u hu hp using hv
  refine ⟨u, hu, hp, fun ℓ => ?_⟩
  apply continuous_functional_of_physical a k M ha ha1 hk u hu (ℓ := ℓ)
  intro y
  exact (v.continuous.comp (continuous_id.prodMk continuous_const)).congr
    (fun t => (hp t y).symm)

end DefocusingNLS

end OAI
