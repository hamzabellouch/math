import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1565 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a245 n105
  exact n105 (h.down {1, 4, 6, 7} {4, 6, 7} a245 (by decide) (by decide))

theorem c1566 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a245 n189 n280 n300 n316 n322 n323
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 7} {4, 6, 7} a245 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n189 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n280 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact n300 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 7} = {4, 6, 7, 8} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 7} = {4, 6, 7, 9} by decide)) hS)

theorem c1567 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a280 n105
  exact n105 (h.down {2, 4, 6, 7} {4, 6, 7} a280 (by decide) (by decide))

theorem c1568 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a280 n189 n245 n300 n316 n322 n323
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 7} {4, 6, 7} a280 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n189 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n245 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 7} = {4, 6, 7, 8} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 7} = {4, 6, 7, 9} by decide)) hS)

theorem c1569 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a300 n105
  exact n105 (h.down {3, 4, 6, 7} {4, 6, 7} a300 (by decide) (by decide))

theorem c1570 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 7, 9} → False := by
  intro a300 n189 n245 n280 n316 n322 n323
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 7} {4, 6, 7} a300 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n189 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n245 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 7} = {4, 6, 7, 8} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 7} = {4, 6, 7, 9} by decide)) hS)

theorem c1577 (h : TenSystem T Q) :
    T {4, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a106 n190 n246 n281 n301 n317 n322 n324
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 6, 8} a106
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n190 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 8} = {4, 6, 8, 9} by decide)) hS)

theorem c1578 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a190 n106
  exact n106 (h.down {0, 4, 6, 8} {4, 6, 8} a190 (by decide) (by decide))

theorem c1579 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a190 n246 n281 n301 n317 n322 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 8} {4, 6, 8} a190 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n246 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 8} = {4, 6, 8, 9} by decide)) hS)

theorem c1580 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a246 n106
  exact n106 (h.down {1, 4, 6, 8} {4, 6, 8} a246 (by decide) (by decide))

theorem c1581 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a246 n190 n281 n301 n317 n322 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 8} {4, 6, 8} a246 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n190 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n281 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 8} = {4, 6, 8, 9} by decide)) hS)

theorem c1582 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a281 n106
  exact n106 (h.down {2, 4, 6, 8} {4, 6, 8} a281 (by decide) (by decide))

theorem c1583 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {4, 6, 8, 9} → False := by
  intro a281 n190 n246 n301 n317 n322 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 8} {4, 6, 8} a281 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n190 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (9 : Labels) {4, 6, 8} = {4, 6, 8, 9} by decide)) hS)

theorem c1584 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a301 n106
  exact n106 (h.down {3, 4, 6, 8} {4, 6, 8} a301 (by decide) (by decide))

theorem c1592 (h : TenSystem T Q) :
    T {4, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 6, 8, 9} → False := by
  intro a107 n191 n247 n282 n302 n318 n323 n324
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 6, 9} a107
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n191 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 9} = {1, 4, 6, 9} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 9} = {2, 4, 6, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n323 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1593 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → ¬ T {4, 6, 9} → False := by
  intro a191 n107
  exact n107 (h.down {0, 4, 6, 9} {4, 6, 9} a191 (by decide) (by decide))

theorem c1594 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 6, 8, 9} → False := by
  intro a191 n247 n282 n302 n318 n323 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 9} {4, 6, 9} a191 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n247 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 9} = {1, 4, 6, 9} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 9} = {2, 4, 6, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n323 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1596 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 6, 8, 9} → False := by
  intro a247 n191 n282 n302 n318 n323 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 9} {4, 6, 9} a247 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n191 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n282 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 9} = {2, 4, 6, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n323 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1597 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → ¬ T {4, 6, 9} → False := by
  intro a282 n107
  exact n107 (h.down {2, 4, 6, 9} {4, 6, 9} a282 (by decide) (by decide))

theorem c1598 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 6, 8, 9} → False := by
  intro a282 n191 n247 n302 n318 n323 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 9} {4, 6, 9} a282 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n191 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 9} = {1, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 6, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n323 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1599 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {4, 6, 9} → False := by
  intro a302 n107
  exact n107 (h.down {3, 4, 6, 9} {4, 6, 9} a302 (by decide) (by decide))

theorem c1600 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 6, 8, 9} → False := by
  intro a302 n191 n247 n282 n318 n323 n324
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 9} {4, 6, 9} a302 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n191 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 6, 9} = {1, 4, 6, 9} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 6, 9} = {2, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n323 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 6, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 6, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1608 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → ¬ T {4, 7, 8} → False := by
  intro a192 n108
  exact n108 (h.down {0, 4, 7, 8} {4, 7, 8} a192 (by decide) (by decide))

theorem c1612 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → ¬ T {4, 7, 8} → False := by
  intro a283 n108
  exact n108 (h.down {2, 4, 7, 8} {4, 7, 8} a283 (by decide) (by decide))

theorem c1614 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → ¬ T {4, 7, 8} → False := by
  intro a303 n108
  exact n108 (h.down {3, 4, 7, 8} {4, 7, 8} a303 (by decide) (by decide))

theorem c1622 (h : TenSystem T Q) :
    T {4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a109 n193 n249 n284 n304 n320 n323 n325
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 7, 9} a109
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n193 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n320 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 7, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1623 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a193 n109
  exact n109 (h.down {0, 4, 7, 9} {4, 7, 9} a193 (by decide) (by decide))

theorem c1624 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a193 n249 n284 n304 n320 n323 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 7, 9} {4, 7, 9} a193 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n249 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n320 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 7, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1625 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a249 n109
  exact n109 (h.down {1, 4, 7, 9} {4, 7, 9} a249 (by decide) (by decide))

theorem c1626 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a249 n193 n284 n304 n320 n323 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 7, 9} {4, 7, 9} a249 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n193 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n284 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n320 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 7, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1627 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a284 n109
  exact n109 (h.down {2, 4, 7, 9} {4, 7, 9} a284 (by decide) (by decide))

theorem c1628 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a284 n193 n249 n304 n320 n323 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 7, 9} {4, 7, 9} a284 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n193 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 7, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n320 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 7, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1629 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a304 n109
  exact n109 (h.down {3, 4, 7, 9} {4, 7, 9} a304 (by decide) (by decide))

theorem c1630 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a304 n193 n249 n284 n320 n323 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 9} {4, 7, 9} a304 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n193 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n320 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (8 : Labels) {4, 7, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1637 (h : TenSystem T Q) :
    T {4, 8, 9} → ¬ Q {0, 4, 8, 9} → ¬ Q {1, 4, 8, 9} → ¬ Q {2, 4, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a110 n194 n250 n285 n305 n321 n324 n325
  obtain ⟨S, hS, hUS⟩ := h.pure {4, 8, 9} a110
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n194 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 8, 9} = {0, 4, 8, 9} by decide)) hS)
  · exact n250 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 8, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact n285 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 8, 9} = {2, 4, 8, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n325 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1638 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a194 n110
  exact n110 (h.down {0, 4, 8, 9} {4, 8, 9} a194 (by decide) (by decide))

theorem c1639 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ Q {1, 4, 8, 9} → ¬ Q {2, 4, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a194 n250 n285 n305 n321 n324 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 8, 9} {4, 8, 9} a194 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n250 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 8, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact n285 (Eq.mp (congrArg Q (show insert (2 : Labels) {4, 8, 9} = {2, 4, 8, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n325 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1643 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → ¬ Q {0, 4, 8, 9} → ¬ Q {1, 4, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {4, 7, 8, 9} → False := by
  intro a285 n194 n250 n305 n321 n324 n325
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 8, 9} {4, 8, 9} a285 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {4, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n194 (Eq.mp (congrArg Q (show insert (0 : Labels) {4, 8, 9} = {0, 4, 8, 9} by decide)) hS)
  · exact n250 (Eq.mp (congrArg Q (show insert (1 : Labels) {4, 8, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (3 : Labels) {4, 8, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (5 : Labels) {4, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (6 : Labels) {4, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n325 (Eq.mp (congrArg Q (show insert (7 : Labels) {4, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
