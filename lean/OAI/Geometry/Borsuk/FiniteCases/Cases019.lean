import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1644 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a305 n110
  exact n110 (h.down {3, 4, 8, 9} {4, 8, 9} a305 (by decide) (by decide))

theorem c1652 (h : TenSystem T Q) :
    T {5, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 7, 9} → False := by
  intro a111 n195 n251 n286 n306 n316 n326 n327
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 6, 7} a111
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n195 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact n251 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact n286 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 7} = {2, 5, 6, 7} by decide)) hS)
  · exact n306 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 7} = {3, 5, 6, 7} by decide)) hS)
  · exact n316 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 6, 7} = {5, 6, 7, 8} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 7} = {5, 6, 7, 9} by decide)) hS)

theorem c1653 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a195 n111
  exact n111 (h.down {0, 5, 6, 7} {5, 6, 7} a195 (by decide) (by decide))

theorem c1655 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a251 n111
  exact n111 (h.down {1, 5, 6, 7} {5, 6, 7} a251 (by decide) (by decide))

theorem c1657 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a286 n111
  exact n111 (h.down {2, 5, 6, 7} {5, 6, 7} a286 (by decide) (by decide))

theorem c1659 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a306 n111
  exact n111 (h.down {3, 5, 6, 7} {5, 6, 7} a306 (by decide) (by decide))

theorem c1660 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {4, 5, 6, 7} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 7, 9} → False := by
  intro a306 n195 n251 n286 n316 n326 n327
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 7} {5, 6, 7} a306 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n195 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact n251 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact n286 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 7} = {2, 5, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n316 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 7} = {4, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 6, 7} = {5, 6, 7, 8} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 7} = {5, 6, 7, 9} by decide)) hS)

theorem c1667 (h : TenSystem T Q) :
    T {5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a112 n196 n252 n287 n307 n317 n326 n328
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 6, 8} a112
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n196 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

theorem c1668 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a196 n112
  exact n112 (h.down {0, 5, 6, 8} {5, 6, 8} a196 (by decide) (by decide))

theorem c1669 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a196 n252 n287 n307 n317 n326 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 8} {5, 6, 8} a196 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

theorem c1670 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a252 n112
  exact n112 (h.down {1, 5, 6, 8} {5, 6, 8} a252 (by decide) (by decide))

theorem c1671 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a252 n196 n287 n307 n317 n326 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 6, 8} {5, 6, 8} a252 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n196 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n287 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

theorem c1672 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a287 n112
  exact n112 (h.down {2, 5, 6, 8} {5, 6, 8} a287 (by decide) (by decide))

theorem c1673 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a287 n196 n252 n307 n317 n326 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 6, 8} {5, 6, 8} a287 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n196 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

theorem c1674 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a307 n112
  exact n112 (h.down {3, 5, 6, 8} {5, 6, 8} a307 (by decide) (by decide))

theorem c1675 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {4, 5, 6, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 6, 8, 9} → False := by
  intro a307 n196 n252 n287 n317 n326 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 8} {5, 6, 8} a307 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n196 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n317 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 8} = {4, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 6, 8} = {5, 6, 8, 9} by decide)) hS)

theorem c1682 (h : TenSystem T Q) :
    T {5, 6, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 6, 8, 9} → False := by
  intro a113 n197 n253 n288 n308 n318 n327 n328
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 6, 9} a113
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n197 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact n253 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n288 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n327 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 6, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1684 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 6, 8, 9} → False := by
  intro a197 n253 n288 n308 n318 n327 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 9} {5, 6, 9} a197 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n253 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n288 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 6, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact n318 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n327 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 6, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1689 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → ¬ T {5, 6, 9} → False := by
  intro a308 n113
  exact n113 (h.down {3, 5, 6, 9} {5, 6, 9} a308 (by decide) (by decide))

theorem c1690 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {4, 5, 6, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 6, 8, 9} → False := by
  intro a308 n197 n253 n288 n318 n327 n328
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 9} {5, 6, 9} a308 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n197 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 6, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact n253 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 6, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n288 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 6, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n318 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 6, 9} = {4, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n327 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 6, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 6, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1697 (h : TenSystem T Q) :
    T {5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 7, 8, 9} → False := by
  intro a114 n198 n254 n289 n309 n319 n326 n329
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 7, 8} a114
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n198 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact n289 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 7, 8} = {5, 7, 8, 9} by decide)) hS)

theorem c1698 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a198 n114
  exact n114 (h.down {0, 5, 7, 8} {5, 7, 8} a198 (by decide) (by decide))

theorem c1699 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 7, 8, 9} → False := by
  intro a198 n254 n289 n309 n319 n326 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 7, 8} {5, 7, 8} a198 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact n289 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 7, 8} = {5, 7, 8, 9} by decide)) hS)

theorem c1700 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a254 n114
  exact n114 (h.down {1, 5, 7, 8} {5, 7, 8} a254 (by decide) (by decide))

theorem c1701 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 7, 8, 9} → False := by
  intro a254 n198 n289 n309 n319 n326 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 7, 8} {5, 7, 8} a254 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n198 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n289 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 7, 8} = {5, 7, 8, 9} by decide)) hS)

theorem c1703 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 7, 8, 9} → False := by
  intro a289 n198 n254 n309 n319 n326 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 7, 8} {5, 7, 8} a289 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n198 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n309 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact n319 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 7, 8} = {5, 7, 8, 9} by decide)) hS)

theorem c1704 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a309 n114
  exact n114 (h.down {3, 5, 7, 8} {5, 7, 8} a309 (by decide) (by decide))

theorem c1705 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {4, 5, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {5, 7, 8, 9} → False := by
  intro a309 n198 n254 n289 n319 n326 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 7, 8} {5, 7, 8} a309 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n198 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact n289 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n319 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 8} = {4, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n326 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (9 : Labels) {5, 7, 8} = {5, 7, 8, 9} by decide)) hS)

theorem c1712 (h : TenSystem T Q) :
    T {5, 7, 9} → ¬ Q {0, 5, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a115 n199 n255 n290 n310 n320 n327 n329
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 7, 9} a115
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n199 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 9} = {0, 5, 7, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n290 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 9} = {2, 5, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n327 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 7, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1715 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {5, 7, 9} → False := by
  intro a255 n115
  exact n115 (h.down {1, 5, 7, 9} {5, 7, 9} a255 (by decide) (by decide))

theorem c1716 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ Q {0, 5, 7, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {4, 5, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a255 n199 n290 n310 n320 n327 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 7, 9} {5, 7, 9} a255 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n199 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 7, 9} = {0, 5, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n290 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 7, 9} = {2, 5, 7, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 7, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n320 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 7, 9} = {4, 5, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n327 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n329 (Eq.mp (congrArg Q (show insert (8 : Labels) {5, 7, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1717 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → ¬ T {5, 7, 9} → False := by
  intro a290 n115
  exact n115 (h.down {2, 5, 7, 9} {5, 7, 9} a290 (by decide) (by decide))

theorem c1719 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → ¬ T {5, 7, 9} → False := by
  intro a310 n115
  exact n115 (h.down {3, 5, 7, 9} {5, 7, 9} a310 (by decide) (by decide))

theorem c1727 (h : TenSystem T Q) :
    T {5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a116 n200 n256 n291 n311 n321 n328 n329
  obtain ⟨S, hS, hUS⟩ := h.pure {5, 8, 9} a116
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n200 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n291 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1728 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a200 n116
  exact n116 (h.down {0, 5, 8, 9} {5, 8, 9} a200 (by decide) (by decide))

theorem c1729 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a200 n256 n291 n311 n321 n328 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 8, 9} {5, 8, 9} a200 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n291 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1730 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a256 n116
  exact n116 (h.down {1, 5, 8, 9} {5, 8, 9} a256 (by decide) (by decide))

theorem c1731 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a256 n200 n291 n311 n321 n328 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 8, 9} {5, 8, 9} a256 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n200 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n291 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
