import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1491 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a240 n184 n275 n305 n311 n314 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 8, 9} {3, 8, 9} a240 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1494 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a305 n100
  exact n100 (h.down {3, 4, 8, 9} {3, 8, 9} a305 (by decide) (by decide))

theorem c1495 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a305 n184 n240 n275 n311 n314 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 8, 9} {3, 8, 9} a305 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1496 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a311 n100
  exact n100 (h.down {3, 5, 8, 9} {3, 8, 9} a311 (by decide) (by decide))

theorem c1497 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a311 n184 n240 n275 n305 n314 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 8, 9} {3, 8, 9} a311 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1499 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a314 n184 n240 n275 n305 n311 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 8, 9} {3, 8, 9} a314 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1500 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a315 n100
  exact n100 (h.down {3, 7, 8, 9} {3, 8, 9} a315 (by decide) (by decide))

theorem c1501 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a315 n184 n240 n275 n305 n311 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 7, 8, 9} {3, 8, 9} a315 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1502 (h : TenSystem T Q) :
    T {4, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 6, 9} → False := by
  intro a101 n185 n241 n276 n296 n316 n317 n318
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 5, 6} a101
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n185 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact n276 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact n296 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 6} = {4, 5, 6, 7} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 6} = {4, 5, 6, 8} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 6} = {4, 5, 6, 9} by decide)) hS)

theorem c1504 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 6, 9} → False := by
  intro a185 n241 n276 n296 n316 n317 n318
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 6} {4, 5, 6} a185 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact n276 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact n296 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 6} = {4, 5, 6, 7} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 6} = {4, 5, 6, 8} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 6} = {4, 5, 6, 9} by decide)) hS)

theorem c1506 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 6, 9} → False := by
  intro a241 n185 n276 n296 n316 n317 n318
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 6} {4, 5, 6} a241 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n185 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n276 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact n296 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 6} = {4, 5, 6, 7} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 6} = {4, 5, 6, 8} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 6} = {4, 5, 6, 9} by decide)) hS)

theorem c1508 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 6, 9} → False := by
  intro a276 n185 n241 n296 n316 n317 n318
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 5, 6} {4, 5, 6} a276 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n185 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 6} = {4, 5, 6, 7} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 6} = {4, 5, 6, 8} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 6} = {4, 5, 6, 9} by decide)) hS)

theorem c1510 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 6, 9} → False := by
  intro a296 n185 n241 n276 n316 n317 n318
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 6} {4, 5, 6} a296 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n185 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact n276 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 6} = {4, 5, 6, 7} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 6} = {4, 5, 6, 8} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 6} = {4, 5, 6, 9} by decide)) hS)

theorem c1517 (h : TenSystem T Q) :
    T {4, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 7, 9} → False := by
  intro a102 n186 n242 n277 n297 n316 n319 n320
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 5, 7} a102
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n186 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact n277 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact n297 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n319 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 7} = {4, 5, 7, 8} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 7} = {4, 5, 7, 9} by decide)) hS)

theorem c1518 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → ¬ T {4, 5, 7} → False := by
  intro a186 n102
  exact n102 (h.down {0, 4, 5, 7} {4, 5, 7} a186 (by decide) (by decide))

theorem c1521 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 7, 9} → False := by
  intro a242 n186 n277 n297 n316 n319 n320
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 7} {4, 5, 7} a242 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n186 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n277 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact n297 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n319 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 7} = {4, 5, 7, 8} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 7} = {4, 5, 7, 9} by decide)) hS)

theorem c1522 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → ¬ T {4, 5, 7} → False := by
  intro a277 n102
  exact n102 (h.down {2, 4, 5, 7} {4, 5, 7} a277 (by decide) (by decide))

theorem c1524 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {4, 5, 7} → False := by
  intro a297 n102
  exact n102 (h.down {3, 4, 5, 7} {4, 5, 7} a297 (by decide) (by decide))

theorem c1525 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 7, 9} → False := by
  intro a297 n186 n242 n277 n316 n319 n320
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 7} {4, 5, 7} a297 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n186 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact n277 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n319 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 7} = {4, 5, 7, 8} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 7} = {4, 5, 7, 9} by decide)) hS)

theorem c1532 (h : TenSystem T Q) :
    T {4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a103 n187 n243 n278 n298 n317 n319 n321
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 5, 8} a103
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n187 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n298 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 8} = {4, 5, 8, 9} by decide)) hS)

theorem c1533 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a187 n103
  exact n103 (h.down {0, 4, 5, 8} {4, 5, 8} a187 (by decide) (by decide))

theorem c1534 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a187 n243 n278 n298 n317 n319 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {4, 5, 8} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n243 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n298 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 8} = {4, 5, 8, 9} by decide)) hS)

theorem c1535 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a243 n103
  exact n103 (h.down {1, 4, 5, 8} {4, 5, 8} a243 (by decide) (by decide))

theorem c1536 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a243 n187 n278 n298 n317 n319 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 8} {4, 5, 8} a243 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n187 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n278 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n298 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 8} = {4, 5, 8, 9} by decide)) hS)

theorem c1538 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a278 n187 n243 n298 n317 n319 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 5, 8} {4, 5, 8} a278 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n187 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 8} = {4, 5, 8, 9} by decide)) hS)

theorem c1539 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a298 n103
  exact n103 (h.down {3, 4, 5, 8} {4, 5, 8} a298 (by decide) (by decide))

theorem c1540 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {4, 5, 8, 9} → False := by
  intro a298 n187 n243 n278 n317 n319 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 8} {4, 5, 8} a298 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n187 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 5, 8} = {4, 5, 8, 9} by decide)) hS)

theorem c1547 (h : TenSystem T Q) :
    T {4, 5, 9} → ¬ Q {0, 4, 5, 9} → ¬ Q {1, 4, 5, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 5, 8, 9} → False := by
  intro a104 n188 n244 n279 n299 n318 n320 n321
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 5, 9} a104
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n188 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 5, 9} = {0, 4, 5, 9} by decide)) hS)
  · exact n244 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 9} = {1, 4, 5, 9} by decide)) hS)
  · exact n279 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact n299 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1549 (h : TenSystem T Q) :
    Q {0, 4, 5, 9} → ¬ Q {1, 4, 5, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 5, 8, 9} → False := by
  intro a188 n244 n279 n299 n318 n320 n321
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 9} {4, 5, 9} a188 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n244 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 5, 9} = {1, 4, 5, 9} by decide)) hS)
  · exact n279 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 5, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact n299 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 5, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 5, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 5, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 5, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1562 (h : TenSystem T Q) :
    T {4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a105 n189 n245 n280 n300 n316 n322 n323
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 6, 7} a105
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n189 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n245 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact n300 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 7} = {4, 6, 7, 8} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 7} = {4, 6, 7, 9} by decide)) hS)

theorem c1563 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a189 n105
  exact n105 (h.down {0, 4, 6, 7} {4, 6, 7} a189 (by decide) (by decide))

theorem c1564 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a189 n245 n280 n300 n316 n322 n323
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 7} {4, 6, 7} a189 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n245 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact n300 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 7} = {4, 6, 7, 8} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 7} = {4, 6, 7, 9} by decide)) hS)

end BorsukNine.FiniteObstruction

end OAI
