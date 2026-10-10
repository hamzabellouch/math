import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c585 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {1, 2, 5} → False := by
  intro a219 n39
  exact n39 (h.down {1, 2, 5, 9} {1, 2, 5} a219 (by decide) (by decide))

theorem c587 (h : TenSystem T Q) :
    T {1, 2, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 6, 9} → False := by
  intro a40 n124 n207 n212 n216 n220 n221 n222
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 6} a40
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n124 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 6} = {1, 2, 6, 7} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 6} = {1, 2, 6, 8} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 6} = {1, 2, 6, 9} by decide)) hS)

theorem c588 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {1, 2, 6} → False := by
  intro a124 n40
  exact n40 (h.down {0, 1, 2, 6} {1, 2, 6} a124 (by decide) (by decide))

theorem c589 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 6, 9} → False := by
  intro a124 n207 n212 n216 n220 n221 n222
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 6} {1, 2, 6} a124 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 6} = {1, 2, 6, 7} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 6} = {1, 2, 6, 8} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 6} = {1, 2, 6, 9} by decide)) hS)

theorem c590 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {1, 2, 6} → False := by
  intro a207 n40
  exact n40 (h.down {1, 2, 3, 6} {1, 2, 6} a207 (by decide) (by decide))

theorem c592 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → ¬ T {1, 2, 6} → False := by
  intro a212 n40
  exact n40 (h.down {1, 2, 4, 6} {1, 2, 6} a212 (by decide) (by decide))

theorem c593 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 6, 9} → False := by
  intro a212 n124 n207 n216 n220 n221 n222
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 4, 6} {1, 2, 6} a212 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n124 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 6} = {1, 2, 6, 7} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 6} = {1, 2, 6, 8} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 6} = {1, 2, 6, 9} by decide)) hS)

theorem c594 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ T {1, 2, 6} → False := by
  intro a216 n40
  exact n40 (h.down {1, 2, 5, 6} {1, 2, 6} a216 (by decide) (by decide))

theorem c595 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 6, 9} → False := by
  intro a216 n124 n207 n212 n220 n221 n222
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 5, 6} {1, 2, 6} a216 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n124 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 6} = {1, 2, 6, 7} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 6} = {1, 2, 6, 8} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 6} = {1, 2, 6, 9} by decide)) hS)

theorem c596 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {1, 2, 6} → False := by
  intro a220 n40
  exact n40 (h.down {1, 2, 6, 7} {1, 2, 6} a220 (by decide) (by decide))

theorem c599 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 9} → False := by
  intro a221 n124 n207 n212 n216 n220 n222
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 6, 8} {1, 2, 6} a221 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n124 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 6} = {1, 2, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n222 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 6} = {1, 2, 6, 9} by decide)) hS)

theorem c600 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {1, 2, 6} → False := by
  intro a222 n40
  exact n40 (h.down {1, 2, 6, 9} {1, 2, 6} a222 (by decide) (by decide))

theorem c601 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 6, 8} → False := by
  intro a222 n124 n207 n212 n216 n220 n221
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 6, 9} {1, 2, 6} a222 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n124 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 6} = {1, 2, 6, 7} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 6} = {1, 2, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c602 (h : TenSystem T Q) :
    T {1, 2, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 7, 8} → ¬ Q {1, 2, 7, 9} → False := by
  intro a41 n125 n208 n213 n217 n220 n223 n224
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 7} a41
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n125 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n208 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 7} = {1, 2, 3, 7} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact n217 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n220 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n223 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 7} = {1, 2, 7, 8} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 7} = {1, 2, 7, 9} by decide)) hS)

theorem c603 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {1, 2, 7} → False := by
  intro a125 n41
  exact n41 (h.down {0, 1, 2, 7} {1, 2, 7} a125 (by decide) (by decide))

theorem c605 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {1, 2, 7} → False := by
  intro a208 n41
  exact n41 (h.down {1, 2, 3, 7} {1, 2, 7} a208 (by decide) (by decide))

theorem c607 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → ¬ T {1, 2, 7} → False := by
  intro a213 n41
  exact n41 (h.down {1, 2, 4, 7} {1, 2, 7} a213 (by decide) (by decide))

theorem c609 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {1, 2, 7} → False := by
  intro a217 n41
  exact n41 (h.down {1, 2, 5, 7} {1, 2, 7} a217 (by decide) (by decide))

theorem c611 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {1, 2, 7} → False := by
  intro a220 n41
  exact n41 (h.down {1, 2, 6, 7} {1, 2, 7} a220 (by decide) (by decide))

theorem c615 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {1, 2, 7} → False := by
  intro a224 n41
  exact n41 (h.down {1, 2, 7, 9} {1, 2, 7} a224 (by decide) (by decide))

theorem c616 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ Q {0, 1, 2, 7} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 7, 8} → False := by
  intro a224 n125 n208 n213 n217 n220 n223
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 7, 9} {1, 2, 7} a224 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n125 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n208 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 7} = {1, 2, 3, 7} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact n217 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n220 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n223 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 7} = {1, 2, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c617 (h : TenSystem T Q) :
    T {1, 2, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {1, 2, 3, 8} → ¬ Q {1, 2, 4, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 7, 8} → ¬ Q {1, 2, 8, 9} → False := by
  intro a42 n126 n209 n214 n218 n221 n223 n225
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 8} a42
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n126 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n209 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 8} = {1, 2, 3, 8} by decide)) hS)
  · exact n214 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 8} = {1, 2, 4, 8} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact n223 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 8} = {1, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n225 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 8} = {1, 2, 8, 9} by decide)) hS)

theorem c618 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → ¬ T {1, 2, 8} → False := by
  intro a126 n42
  exact n42 (h.down {0, 1, 2, 8} {1, 2, 8} a126 (by decide) (by decide))

theorem c620 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {1, 2, 8} → False := by
  intro a209 n42
  exact n42 (h.down {1, 2, 3, 8} {1, 2, 8} a209 (by decide) (by decide))

theorem c626 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → ¬ T {1, 2, 8} → False := by
  intro a221 n42
  exact n42 (h.down {1, 2, 6, 8} {1, 2, 8} a221 (by decide) (by decide))

theorem c630 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {1, 2, 8} → False := by
  intro a225 n42
  exact n42 (h.down {1, 2, 8, 9} {1, 2, 8} a225 (by decide) (by decide))

theorem c632 (h : TenSystem T Q) :
    T {1, 2, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a43 n127 n210 n215 n219 n222 n224 n225
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 9} a43
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c633 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {1, 2, 9} → False := by
  intro a127 n43
  exact n43 (h.down {0, 1, 2, 9} {1, 2, 9} a127 (by decide) (by decide))

theorem c634 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a127 n210 n215 n219 n222 n224 n225
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 9} {1, 2, 9} a127 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c635 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {1, 2, 9} → False := by
  intro a210 n43
  exact n43 (h.down {1, 2, 3, 9} {1, 2, 9} a210 (by decide) (by decide))

theorem c636 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a210 n127 n215 n219 n222 n224 n225
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 3, 9} {1, 2, 9} a210 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c637 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → ¬ T {1, 2, 9} → False := by
  intro a215 n43
  exact n43 (h.down {1, 2, 4, 9} {1, 2, 9} a215 (by decide) (by decide))

theorem c638 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a215 n127 n210 n219 n222 n224 n225
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 4, 9} {1, 2, 9} a215 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n219 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c640 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a219 n127 n210 n215 n222 n224 n225
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 5, 9} {1, 2, 9} a219 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c641 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {1, 2, 9} → False := by
  intro a222 n43
  exact n43 (h.down {1, 2, 6, 9} {1, 2, 9} a222 (by decide) (by decide))

theorem c643 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {1, 2, 9} → False := by
  intro a224 n43
  exact n43 (h.down {1, 2, 7, 9} {1, 2, 9} a224 (by decide) (by decide))

theorem c644 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 8, 9} → False := by
  intro a224 n127 n210 n215 n219 n222 n225
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 7, 9} {1, 2, 9} a224 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n225 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c646 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 7, 9} → False := by
  intro a225 n127 n210 n215 n219 n222 n224
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 8, 9} {1, 2, 9} a225 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n127 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)

theorem c647 (h : TenSystem T Q) :
    T {1, 3, 4} → ¬ Q {0, 1, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 4, 8} → ¬ Q {1, 3, 4, 9} → False := by
  intro a44 n128 n205 n226 n227 n228 n229 n230
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 3, 4} a44
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n128 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n205 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 4} = {1, 3, 4, 5} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 4} = {1, 3, 4, 6} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 4} = {1, 3, 4, 7} by decide)) hS)
  · exact n229 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 4} = {1, 3, 4, 8} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 4} = {1, 3, 4, 9} by decide)) hS)

theorem c648 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {1, 3, 4} → False := by
  intro a128 n44
  exact n44 (h.down {0, 1, 3, 4} {1, 3, 4} a128 (by decide) (by decide))

theorem c650 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {1, 3, 4} → False := by
  intro a205 n44
  exact n44 (h.down {1, 2, 3, 4} {1, 3, 4} a205 (by decide) (by decide))

theorem c651 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ Q {0, 1, 3, 4} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 4, 8} → ¬ Q {1, 3, 4, 9} → False := by
  intro a205 n128 n226 n227 n228 n229 n230
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 3, 4} {1, 3, 4} a205 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n128 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 4} = {1, 3, 4, 5} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 4} = {1, 3, 4, 6} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 4} = {1, 3, 4, 7} by decide)) hS)
  · exact n229 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 4} = {1, 3, 4, 8} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 4} = {1, 3, 4, 9} by decide)) hS)

end BorsukNine.FiniteObstruction

end OAI
