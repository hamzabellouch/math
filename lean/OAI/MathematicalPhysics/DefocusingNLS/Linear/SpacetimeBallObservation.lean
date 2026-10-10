import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSpacetimeObservation

namespace OAI

/-! # Continuous compact-ball observations of a local space-time limit -/

open Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def spacetimeBallPath (T R : ℝ) (v : C(Icc (0 : ℝ) T × E, ℂ)) :
    C(Icc (0 : ℝ) T, C(Metric.closedBall (0 : E) R, ℂ)) :=
  ContinuousMap.curry (v.comp
    ⟨fun p => (p.1, (p.2 : E)), continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩)

@[simp] theorem spacetimeBallPath_apply (T R : ℝ) (v : C(Icc (0 : ℝ) T × E, ℂ))
    (t : Icc (0 : ℝ) T) (y : Metric.closedBall (0 : E) R) :
    spacetimeBallPath T R v t y = v (t, (y : E)) := rfl

theorem continuous_spacetimeBallPath (T R : ℝ) : Continuous (spacetimeBallPath T R) := by
  exact ContinuousMap.continuous_curry.comp (ContinuousMap.continuous_precomp
    (⟨fun p => (p.1, (p.2 : E)),
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩ :
      C(Icc (0 : ℝ) T × Metric.closedBall (0 : E) R, Icc (0 : ℝ) T × E)))

theorem spacetimeBallPath_norm_le (T R B : ℝ) (hB : 0 ≤ B)
    (v : C(Icc (0 : ℝ) T × E, ℂ)) (hv : ∀ t y, ‖v (t, y)‖ ≤ B)
    (t : Icc (0 : ℝ) T) : ‖spacetimeBallPath T R v t‖ ≤ B :=
  (ContinuousMap.norm_le _ hB).mpr (fun y => hv t y)

theorem spacetimeBallPath_expanding (a k L T R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (t : Icc (0 : ℝ) T) :
    spacetimeBallPath T R (expandingSpacetimePath a k L T ha ha1 hk hL u) t =
      expandingPhysicalBall a k (expandingRadius L t) R ha ha1 hk
        (hL.trans (expandingRadius_ge L t hL t.2.1)) (u t) := by
  ext y
  simp only [spacetimeBallPath_apply, expandingSpacetimePath_apply, expandingPhysicalBall_apply]

end DefocusingNLS

end OAI
