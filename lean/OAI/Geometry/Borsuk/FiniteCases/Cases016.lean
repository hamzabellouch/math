import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1427 (h : TenSystem T Q) :
    T {3, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 8, 9} → False := by
  intro a96 n180 n236 n271 n301 n307 n312 n314
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 6, 8} a96
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n180 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 8} = {3, 6, 8, 9} by decide)) hS)

theorem c1428 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {3, 6, 8} → False := by
  intro a180 n96
  exact n96 (h.down {0, 3, 6, 8} {3, 6, 8} a180 (by decide) (by decide))

theorem c1434 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {3, 6, 8} → False := by
  intro a301 n96
  exact n96 (h.down {3, 4, 6, 8} {3, 6, 8} a301 (by decide) (by decide))

theorem c1435 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 8, 9} → False := by
  intro a301 n180 n236 n271 n307 n312 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 8} {3, 6, 8} a301 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n180 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 8} = {3, 6, 8, 9} by decide)) hS)

theorem c1437 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 8, 9} → False := by
  intro a307 n180 n236 n271 n301 n312 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 8} {3, 6, 8} a307 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n180 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 8} = {3, 6, 8, 9} by decide)) hS)

theorem c1438 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {3, 6, 8} → False := by
  intro a312 n96
  exact n96 (h.down {3, 6, 7, 8} {3, 6, 8} a312 (by decide) (by decide))

theorem c1439 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 6, 8, 9} → False := by
  intro a312 n180 n236 n271 n301 n307 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 8} {3, 6, 8} a312 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n180 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 8} = {3, 6, 8, 9} by decide)) hS)

theorem c1440 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {3, 6, 8} → False := by
  intro a314 n96
  exact n96 (h.down {3, 6, 8, 9} {3, 6, 8} a314 (by decide) (by decide))

theorem c1441 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ Q {0, 3, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 6, 7, 8} → False := by
  intro a314 n180 n236 n271 n301 n307 n312
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 8, 9} {3, 6, 8} a314 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n180 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c1442 (h : TenSystem T Q) :
    T {3, 6, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a97 n181 n237 n272 n302 n308 n313 n314
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 6, 9} a97
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n181 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1444 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a181 n237 n272 n302 n308 n313 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 6, 9} {3, 6, 9} a181 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1445 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {3, 6, 9} → False := by
  intro a237 n97
  exact n97 (h.down {1, 3, 6, 9} {3, 6, 9} a237 (by decide) (by decide))

theorem c1449 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {3, 6, 9} → False := by
  intro a302 n97
  exact n97 (h.down {3, 4, 6, 9} {3, 6, 9} a302 (by decide) (by decide))

theorem c1450 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a302 n181 n237 n272 n308 n313 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 9} {3, 6, 9} a302 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n181 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n308 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1452 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a308 n181 n237 n272 n302 n313 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 9} {3, 6, 9} a308 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n181 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1453 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {3, 6, 9} → False := by
  intro a313 n97
  exact n97 (h.down {3, 6, 7, 9} {3, 6, 9} a313 (by decide) (by decide))

theorem c1454 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 6, 8, 9} → False := by
  intro a313 n181 n237 n272 n302 n308 n314
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 9} {3, 6, 9} a313 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n181 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1456 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 6, 7, 9} → False := by
  intro a314 n181 n237 n272 n302 n308 n313
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 8, 9} {3, 6, 9} a314 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n181 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 6, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)

theorem c1457 (h : TenSystem T Q) :
    T {3, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 7, 8, 9} → False := by
  intro a98 n182 n238 n273 n303 n309 n312 n315
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 7, 8} a98
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n182 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact n312 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 7, 8} = {3, 7, 8, 9} by decide)) hS)

theorem c1467 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 7, 8, 9} → False := by
  intro a309 n182 n238 n273 n303 n312 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 7, 8} {3, 7, 8} a309 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n182 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 7, 8} = {3, 7, 8, 9} by decide)) hS)

theorem c1468 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {3, 7, 8} → False := by
  intro a312 n98
  exact n98 (h.down {3, 6, 7, 8} {3, 7, 8} a312 (by decide) (by decide))

theorem c1469 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 7, 8, 9} → False := by
  intro a312 n182 n238 n273 n303 n309 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 8} {3, 7, 8} a312 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n182 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 7, 8} = {3, 7, 8, 9} by decide)) hS)

theorem c1472 (h : TenSystem T Q) :
    T {3, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a99 n183 n239 n274 n304 n310 n313 n315
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 7, 9} a99
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 7, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1475 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {3, 7, 9} → False := by
  intro a239 n99
  exact n99 (h.down {1, 3, 7, 9} {3, 7, 9} a239 (by decide) (by decide))

theorem c1478 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a274 n183 n239 n304 n310 n313 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 7, 9} {3, 7, 9} a274 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 7, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1479 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 7, 9} → False := by
  intro a304 n99
  exact n99 (h.down {3, 4, 7, 9} {3, 7, 9} a304 (by decide) (by decide))

theorem c1480 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a304 n183 n239 n274 n310 n313 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 9} {3, 7, 9} a304 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n310 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 7, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1481 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → ¬ T {3, 7, 9} → False := by
  intro a310 n99
  exact n99 (h.down {3, 5, 7, 9} {3, 7, 9} a310 (by decide) (by decide))

theorem c1482 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a310 n183 n239 n274 n304 n313 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 7, 9} {3, 7, 9} a310 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 7, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1484 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a313 n183 n239 n274 n304 n310 n315
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 9} {3, 7, 9} a313 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 7, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1485 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {3, 7, 9} → False := by
  intro a315 n99
  exact n99 (h.down {3, 7, 8, 9} {3, 7, 9} a315 (by decide) (by decide))

theorem c1486 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 6, 7, 9} → False := by
  intro a315 n183 n239 n274 n304 n310 n313
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 7, 8, 9} {3, 7, 9} a315 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n183 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)

theorem c1487 (h : TenSystem T Q) :
    T {3, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  intro a100 n184 n240 n275 n305 n311 n314 n315
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 8, 9} a100
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n184 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1490 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {3, 8, 9} → False := by
  intro a240 n100
  exact n100 (h.down {1, 3, 8, 9} {3, 8, 9} a240 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
