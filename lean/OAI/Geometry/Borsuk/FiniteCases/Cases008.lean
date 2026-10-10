import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c654 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → ¬ T {1, 3, 4} → False := by
  intro a227 n44
  exact n44 (h.down {1, 3, 4, 6} {1, 3, 4} a227 (by decide) (by decide))

theorem c655 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → ¬ Q {0, 1, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 4, 8} → ¬ Q {1, 3, 4, 9} → False := by
  intro a227 n128 n205 n226 n228 n229 n230
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 6} {1, 3, 4} a227 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n128 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n205 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 4} = {1, 3, 4, 5} by decide)) hS)
  · exact hne (by decide)
  · exact n228 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 4} = {1, 3, 4, 7} by decide)) hS)
  · exact n229 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 4} = {1, 3, 4, 8} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 4} = {1, 3, 4, 9} by decide)) hS)

theorem c656 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {1, 3, 4} → False := by
  intro a228 n44
  exact n44 (h.down {1, 3, 4, 7} {1, 3, 4} a228 (by decide) (by decide))

theorem c660 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {1, 3, 4} → False := by
  intro a230 n44
  exact n44 (h.down {1, 3, 4, 9} {1, 3, 4} a230 (by decide) (by decide))

theorem c661 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ Q {0, 1, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 4, 8} → False := by
  intro a230 n128 n205 n226 n227 n228 n229
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 9} {1, 3, 4} a230 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c662 (h : TenSystem T Q) :
    T {1, 3, 5} → ¬ Q {0, 1, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 3, 5, 9} → False := by
  intro a45 n129 n206 n226 n231 n232 n233 n234
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 3, 5} a45
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n129 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 5} = {0, 1, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n206 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n231 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 5} = {1, 3, 5, 6} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 5} = {1, 3, 5, 7} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 5} = {1, 3, 5, 8} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 5} = {1, 3, 5, 9} by decide)) hS)

theorem c664 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 3, 5, 9} → False := by
  intro a129 n206 n226 n231 n232 n233 n234
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 5} {1, 3, 5} a129 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n206 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n231 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 5} = {1, 3, 5, 6} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 5} = {1, 3, 5, 7} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 5} = {1, 3, 5, 8} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 5} = {1, 3, 5, 9} by decide)) hS)

theorem c665 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {1, 3, 5} → False := by
  intro a206 n45
  exact n45 (h.down {1, 2, 3, 5} {1, 3, 5} a206 (by decide) (by decide))

theorem c669 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {1, 3, 5} → False := by
  intro a231 n45
  exact n45 (h.down {1, 3, 5, 6} {1, 3, 5} a231 (by decide) (by decide))

theorem c671 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {1, 3, 5} → False := by
  intro a232 n45
  exact n45 (h.down {1, 3, 5, 7} {1, 3, 5} a232 (by decide) (by decide))

theorem c673 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {1, 3, 5} → False := by
  intro a233 n45
  exact n45 (h.down {1, 3, 5, 8} {1, 3, 5} a233 (by decide) (by decide))

theorem c674 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ Q {0, 1, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 5, 9} → False := by
  intro a233 n129 n206 n226 n231 n232 n234
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 5, 8} {1, 3, 5} a233 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n129 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 5} = {0, 1, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n206 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n226 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n231 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 5} = {1, 3, 5, 6} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 5} = {1, 3, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n234 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 5} = {1, 3, 5, 9} by decide)) hS)

theorem c675 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {1, 3, 5} → False := by
  intro a234 n45
  exact n45 (h.down {1, 3, 5, 9} {1, 3, 5} a234 (by decide) (by decide))

theorem c677 (h : TenSystem T Q) :
    T {1, 3, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 3, 6, 9} → False := by
  intro a46 n130 n207 n227 n231 n235 n236 n237
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 3, 6} a46
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n130 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n227 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n235 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 6} = {1, 3, 6, 7} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 6} = {1, 3, 6, 8} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 6} = {1, 3, 6, 9} by decide)) hS)

theorem c678 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {1, 3, 6} → False := by
  intro a130 n46
  exact n46 (h.down {0, 1, 3, 6} {1, 3, 6} a130 (by decide) (by decide))

theorem c679 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 3, 6, 9} → False := by
  intro a130 n207 n227 n231 n235 n236 n237
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 6} {1, 3, 6} a130 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n227 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n235 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 6} = {1, 3, 6, 7} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 6} = {1, 3, 6, 8} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 6} = {1, 3, 6, 9} by decide)) hS)

theorem c680 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {1, 3, 6} → False := by
  intro a207 n46
  exact n46 (h.down {1, 2, 3, 6} {1, 3, 6} a207 (by decide) (by decide))

theorem c682 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → ¬ T {1, 3, 6} → False := by
  intro a227 n46
  exact n46 (h.down {1, 3, 4, 6} {1, 3, 6} a227 (by decide) (by decide))

theorem c684 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {1, 3, 6} → False := by
  intro a231 n46
  exact n46 (h.down {1, 3, 5, 6} {1, 3, 6} a231 (by decide) (by decide))

theorem c686 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {1, 3, 6} → False := by
  intro a235 n46
  exact n46 (h.down {1, 3, 6, 7} {1, 3, 6} a235 (by decide) (by decide))

theorem c687 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ Q {0, 1, 3, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 3, 6, 9} → False := by
  intro a235 n130 n207 n227 n231 n236 n237
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 6, 7} {1, 3, 6} a235 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n130 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n207 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n227 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n236 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 6} = {1, 3, 6, 8} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 6} = {1, 3, 6, 9} by decide)) hS)

theorem c688 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {1, 3, 6} → False := by
  intro a236 n46
  exact n46 (h.down {1, 3, 6, 8} {1, 3, 6} a236 (by decide) (by decide))

theorem c690 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {1, 3, 6} → False := by
  intro a237 n46
  exact n46 (h.down {1, 3, 6, 9} {1, 3, 6} a237 (by decide) (by decide))

theorem c692 (h : TenSystem T Q) :
    T {1, 3, 7} → ¬ Q {0, 1, 3, 7} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 3, 7, 9} → False := by
  intro a47 n131 n208 n228 n232 n235 n238 n239
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 3, 7} a47
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n131 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n208 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 7} = {1, 2, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n228 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n238 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 7} = {1, 3, 7, 8} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 7} = {1, 3, 7, 9} by decide)) hS)

theorem c694 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 3, 7, 9} → False := by
  intro a131 n208 n228 n232 n235 n238 n239
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 7} {1, 3, 7} a131 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n208 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 7} = {1, 2, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n228 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n238 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 7} = {1, 3, 7, 8} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 7} = {1, 3, 7, 9} by decide)) hS)

theorem c695 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {1, 3, 7} → False := by
  intro a208 n47
  exact n47 (h.down {1, 2, 3, 7} {1, 3, 7} a208 (by decide) (by decide))

theorem c696 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ Q {0, 1, 3, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 3, 7, 9} → False := by
  intro a208 n131 n228 n232 n235 n238 n239
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 3, 7} {1, 3, 7} a208 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n131 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n228 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n238 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 7} = {1, 3, 7, 8} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 7} = {1, 3, 7, 9} by decide)) hS)

theorem c701 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {1, 3, 7} → False := by
  intro a235 n47
  exact n47 (h.down {1, 3, 6, 7} {1, 3, 7} a235 (by decide) (by decide))

theorem c705 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 3, 7} → False := by
  intro a239 n47
  exact n47 (h.down {1, 3, 7, 9} {1, 3, 7} a239 (by decide) (by decide))

theorem c714 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {1, 3, 8} → False := by
  intro a233 n48
  exact n48 (h.down {1, 3, 5, 8} {1, 3, 8} a233 (by decide) (by decide))

theorem c715 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {1, 2, 3, 8} → ¬ Q {1, 3, 4, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 3, 8, 9} → False := by
  intro a233 n132 n209 n229 n236 n238 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 5, 8} {1, 3, 8} a233 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n132 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n209 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 8} = {1, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n229 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 8} = {1, 3, 4, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n236 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n240 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 3, 8} = {1, 3, 8, 9} by decide)) hS)

theorem c716 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {1, 3, 8} → False := by
  intro a236 n48
  exact n48 (h.down {1, 3, 6, 8} {1, 3, 8} a236 (by decide) (by decide))

theorem c720 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {1, 3, 8} → False := by
  intro a240 n48
  exact n48 (h.down {1, 3, 8, 9} {1, 3, 8} a240 (by decide) (by decide))

theorem c722 (h : TenSystem T Q) :
    T {1, 3, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a49 n133 n210 n230 n234 n237 n239 n240
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 3, 9} a49
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c723 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {1, 3, 9} → False := by
  intro a133 n49
  exact n49 (h.down {0, 1, 3, 9} {1, 3, 9} a133 (by decide) (by decide))

theorem c724 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a133 n210 n230 n234 n237 n239 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 9} {1, 3, 9} a133 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c725 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {1, 3, 9} → False := by
  intro a210 n49
  exact n49 (h.down {1, 2, 3, 9} {1, 3, 9} a210 (by decide) (by decide))

theorem c727 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {1, 3, 9} → False := by
  intro a230 n49
  exact n49 (h.down {1, 3, 4, 9} {1, 3, 9} a230 (by decide) (by decide))

theorem c728 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a230 n133 n210 n234 n237 n239 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 9} {1, 3, 9} a230 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c729 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {1, 3, 9} → False := by
  intro a234 n49
  exact n49 (h.down {1, 3, 5, 9} {1, 3, 9} a234 (by decide) (by decide))

theorem c730 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a234 n133 n210 n230 n237 n239 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 5, 9} {1, 3, 9} a234 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c731 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {1, 3, 9} → False := by
  intro a237 n49
  exact n49 (h.down {1, 3, 6, 9} {1, 3, 9} a237 (by decide) (by decide))

theorem c732 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a237 n133 n210 n230 n234 n239 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 6, 9} {1, 3, 9} a237 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n239 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 3, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
