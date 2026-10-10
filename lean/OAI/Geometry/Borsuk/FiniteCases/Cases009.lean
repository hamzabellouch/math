import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c733 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 3, 9} → False := by
  intro a239 n49
  exact n49 (h.down {1, 3, 7, 9} {1, 3, 9} a239 (by decide) (by decide))

theorem c734 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 8, 9} → False := by
  intro a239 n133 n210 n230 n234 n237 n240
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 7, 9} {1, 3, 9} a239 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n133 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n210 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n230 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 3, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 3, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 3, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n240 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 3, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c735 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {1, 3, 9} → False := by
  intro a240 n49
  exact n49 (h.down {1, 3, 8, 9} {1, 3, 9} a240 (by decide) (by decide))

theorem c736 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 3, 7, 9} → False := by
  intro a240 n133 n210 n230 n234 n237 n239
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 8, 9} {1, 3, 9} a240 (by decide) (by decide)
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
  · exact hne (by decide)
  · exact hv (by decide)

theorem c737 (h : TenSystem T Q) :
    T {1, 4, 5} → ¬ Q {0, 1, 4, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 4, 5, 9} → False := by
  intro a50 n134 n211 n226 n241 n242 n243 n244
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 4, 5} a50
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n134 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact n226 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 4, 5} = {1, 4, 5, 6} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 4, 5} = {1, 4, 5, 7} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 5} = {1, 4, 5, 8} by decide)) hS)
  · exact n244 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 5} = {1, 4, 5, 9} by decide)) hS)

theorem c742 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → ¬ T {1, 4, 5} → False := by
  intro a226 n50
  exact n50 (h.down {1, 3, 4, 5} {1, 4, 5} a226 (by decide) (by decide))

theorem c744 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 4, 5} → False := by
  intro a241 n50
  exact n50 (h.down {1, 4, 5, 6} {1, 4, 5} a241 (by decide) (by decide))

theorem c746 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ T {1, 4, 5} → False := by
  intro a242 n50
  exact n50 (h.down {1, 4, 5, 7} {1, 4, 5} a242 (by decide) (by decide))

theorem c747 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ Q {0, 1, 4, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 4, 5, 9} → False := by
  intro a242 n134 n211 n226 n241 n243 n244
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 7} {1, 4, 5} a242 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n134 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact n226 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 4, 5} = {1, 4, 5, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n243 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 5} = {1, 4, 5, 8} by decide)) hS)
  · exact n244 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 5} = {1, 4, 5, 9} by decide)) hS)

theorem c748 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {1, 4, 5} → False := by
  intro a243 n50
  exact n50 (h.down {1, 4, 5, 8} {1, 4, 5} a243 (by decide) (by decide))

theorem c749 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ Q {0, 1, 4, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 3, 4, 5} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 4, 5, 9} → False := by
  intro a243 n134 n211 n226 n241 n242 n244
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 8} {1, 4, 5} a243 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n134 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact n226 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 5} = {1, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 4, 5} = {1, 4, 5, 6} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 4, 5} = {1, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n244 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 5} = {1, 4, 5, 9} by decide)) hS)

theorem c752 (h : TenSystem T Q) :
    T {1, 4, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 6, 7} → ¬ Q {1, 4, 6, 8} → ¬ Q {1, 4, 6, 9} → False := by
  intro a51 n135 n212 n227 n241 n245 n246 n247
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 4, 6} a51
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n135 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n212 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 4, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n245 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 4, 6} = {1, 4, 6, 7} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 6} = {1, 4, 6, 8} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 6} = {1, 4, 6, 9} by decide)) hS)

theorem c757 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → ¬ T {1, 4, 6} → False := by
  intro a227 n51
  exact n51 (h.down {1, 3, 4, 6} {1, 4, 6} a227 (by decide) (by decide))

theorem c759 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 4, 6} → False := by
  intro a241 n51
  exact n51 (h.down {1, 4, 5, 6} {1, 4, 6} a241 (by decide) (by decide))

theorem c761 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {1, 4, 6} → False := by
  intro a245 n51
  exact n51 (h.down {1, 4, 6, 7} {1, 4, 6} a245 (by decide) (by decide))

theorem c763 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {1, 4, 6} → False := by
  intro a246 n51
  exact n51 (h.down {1, 4, 6, 8} {1, 4, 6} a246 (by decide) (by decide))

theorem c765 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ T {1, 4, 6} → False := by
  intro a247 n51
  exact n51 (h.down {1, 4, 6, 9} {1, 4, 6} a247 (by decide) (by decide))

theorem c766 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ Q {0, 1, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 4, 6, 7} → ¬ Q {1, 4, 6, 8} → False := by
  intro a247 n135 n212 n227 n241 n245 n246
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 9} {1, 4, 6} a247 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n135 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n212 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n241 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 4, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n245 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 4, 6} = {1, 4, 6, 7} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 6} = {1, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c768 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {1, 4, 7} → False := by
  intro a136 n52
  exact n52 (h.down {0, 1, 4, 7} {1, 4, 7} a136 (by decide) (by decide))

theorem c772 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {1, 4, 7} → False := by
  intro a228 n52
  exact n52 (h.down {1, 3, 4, 7} {1, 4, 7} a228 (by decide) (by decide))

theorem c774 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ T {1, 4, 7} → False := by
  intro a242 n52
  exact n52 (h.down {1, 4, 5, 7} {1, 4, 7} a242 (by decide) (by decide))

theorem c775 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ Q {0, 1, 4, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {1, 4, 7, 8} → ¬ Q {1, 4, 7, 9} → False := by
  intro a242 n136 n213 n228 n245 n248 n249
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 7} {1, 4, 7} a242 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n136 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n213 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n245 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 4, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n248 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 7} = {1, 4, 7, 8} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 4, 7} = {1, 4, 7, 9} by decide)) hS)

theorem c776 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {1, 4, 7} → False := by
  intro a245 n52
  exact n52 (h.down {1, 4, 6, 7} {1, 4, 7} a245 (by decide) (by decide))

theorem c780 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {1, 4, 7} → False := by
  intro a249 n52
  exact n52 (h.down {1, 4, 7, 9} {1, 4, 7} a249 (by decide) (by decide))

theorem c789 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {1, 4, 8} → False := by
  intro a243 n53
  exact n53 (h.down {1, 4, 5, 8} {1, 4, 8} a243 (by decide) (by decide))

theorem c797 (h : TenSystem T Q) :
    T {1, 4, 9} → ¬ Q {0, 1, 4, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 4, 5, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {1, 4, 8, 9} → False := by
  intro a54 n138 n215 n230 n244 n247 n249 n250
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 4, 9} a54
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n138 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 4, 9} = {0, 1, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n215 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 4, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 4, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n244 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 4, 9} = {1, 4, 5, 9} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 4, 9} = {1, 4, 6, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 4, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n250 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 4, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c802 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {1, 4, 9} → False := by
  intro a230 n54
  exact n54 (h.down {1, 3, 4, 9} {1, 4, 9} a230 (by decide) (by decide))

theorem c806 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ T {1, 4, 9} → False := by
  intro a247 n54
  exact n54 (h.down {1, 4, 6, 9} {1, 4, 9} a247 (by decide) (by decide))

theorem c808 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {1, 4, 9} → False := by
  intro a249 n54
  exact n54 (h.down {1, 4, 7, 9} {1, 4, 9} a249 (by decide) (by decide))

theorem c810 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {1, 4, 9} → False := by
  intro a250 n54
  exact n54 (h.down {1, 4, 8, 9} {1, 4, 9} a250 (by decide) (by decide))

theorem c812 (h : TenSystem T Q) :
    T {1, 5, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 6, 9} → False := by
  intro a55 n139 n216 n231 n241 n251 n252 n253
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 5, 6} a55
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n139 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 6} = {1, 5, 6, 7} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 6} = {1, 5, 6, 8} by decide)) hS)
  · exact n253 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 6} = {1, 5, 6, 9} by decide)) hS)

theorem c814 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 6, 9} → False := by
  intro a139 n216 n231 n241 n251 n252 n253
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 5, 6} {1, 5, 6} a139 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 6} = {1, 5, 6, 7} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 6} = {1, 5, 6, 8} by decide)) hS)
  · exact n253 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 6} = {1, 5, 6, 9} by decide)) hS)

theorem c817 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {1, 5, 6} → False := by
  intro a231 n55
  exact n55 (h.down {1, 3, 5, 6} {1, 5, 6} a231 (by decide) (by decide))

theorem c819 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {1, 5, 6} → False := by
  intro a241 n55
  exact n55 (h.down {1, 4, 5, 6} {1, 5, 6} a241 (by decide) (by decide))

theorem c823 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {1, 5, 6} → False := by
  intro a252 n55
  exact n55 (h.down {1, 5, 6, 8} {1, 5, 6} a252 (by decide) (by decide))

theorem c824 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ Q {0, 1, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 6, 9} → False := by
  intro a252 n139 n216 n231 n241 n251 n253
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 6, 8} {1, 5, 6} a252 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n139 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 6} = {1, 5, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n253 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 6} = {1, 5, 6, 9} by decide)) hS)

theorem c826 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ Q {0, 1, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {1, 4, 5, 6} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 6, 8} → False := by
  intro a253 n139 n216 n231 n241 n251 n252
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 6, 9} {1, 5, 6} a253 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n139 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n241 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 6} = {1, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 6} = {1, 5, 6, 7} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 6} = {1, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c827 (h : TenSystem T Q) :
    T {1, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 7, 9} → False := by
  intro a56 n140 n217 n232 n242 n251 n254 n255
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 5, 7} a56
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n140 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n217 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 7} = {1, 5, 7, 9} by decide)) hS)

theorem c829 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 7, 9} → False := by
  intro a140 n217 n232 n242 n251 n254 n255
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 5, 7} {1, 5, 7} a140 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n217 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 7} = {1, 5, 7, 9} by decide)) hS)

theorem c831 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 7, 9} → False := by
  intro a217 n140 n232 n242 n251 n254 n255
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 5, 7} {1, 5, 7} a217 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n140 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 7} = {1, 5, 7, 9} by decide)) hS)

theorem c832 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {1, 5, 7} → False := by
  intro a232 n56
  exact n56 (h.down {1, 3, 5, 7} {1, 5, 7} a232 (by decide) (by decide))

theorem c835 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 7, 9} → False := by
  intro a242 n140 n217 n232 n251 n254 n255
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 7} {1, 5, 7} a242 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n140 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n217 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 7} = {1, 5, 7, 9} by decide)) hS)

theorem c836 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {1, 5, 7} → False := by
  intro a251 n56
  exact n56 (h.down {1, 5, 6, 7} {1, 5, 7} a251 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
