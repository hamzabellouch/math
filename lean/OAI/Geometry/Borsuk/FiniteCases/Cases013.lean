import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1117 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {2, 4, 9} → False := by
  intro a265 n75
  exact n75 (h.down {2, 3, 4, 9} {2, 4, 9} a265 (by decide) (by decide))

theorem c1121 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → ¬ T {2, 4, 9} → False := by
  intro a282 n75
  exact n75 (h.down {2, 4, 6, 9} {2, 4, 9} a282 (by decide) (by decide))

theorem c1123 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {2, 4, 9} → False := by
  intro a284 n75
  exact n75 (h.down {2, 4, 7, 9} {2, 4, 9} a284 (by decide) (by decide))

theorem c1127 (h : TenSystem T Q) :
    T {2, 5, 6} → ¬ Q {0, 2, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 5, 6, 9} → False := by
  intro a76 n160 n216 n266 n276 n286 n287 n288
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 5, 6} a76
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n160 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n266 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact n276 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n286 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 6} = {2, 5, 6, 7} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 5, 6} = {2, 5, 6, 8} by decide)) hS)
  · exact n288 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 5, 6} = {2, 5, 6, 9} by decide)) hS)

theorem c1128 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → ¬ T {2, 5, 6} → False := by
  intro a160 n76
  exact n76 (h.down {0, 2, 5, 6} {2, 5, 6} a160 (by decide) (by decide))

theorem c1134 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {2, 5, 6} → False := by
  intro a276 n76
  exact n76 (h.down {2, 4, 5, 6} {2, 5, 6} a276 (by decide) (by decide))

theorem c1136 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → ¬ T {2, 5, 6} → False := by
  intro a286 n76
  exact n76 (h.down {2, 5, 6, 7} {2, 5, 6} a286 (by decide) (by decide))

theorem c1139 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ Q {0, 2, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 5, 6, 9} → False := by
  intro a287 n160 n216 n266 n276 n286 n288
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 6, 8} {2, 5, 6} a287 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n160 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n266 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact n276 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n286 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 6} = {2, 5, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n288 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 5, 6} = {2, 5, 6, 9} by decide)) hS)

theorem c1141 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → ¬ Q {0, 2, 5, 6} → ¬ Q {1, 2, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 5, 6, 8} → False := by
  intro a288 n160 n216 n266 n276 n286 n287
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 6, 9} {2, 5, 6} a288 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n160 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact n216 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 6} = {1, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n266 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact n276 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n286 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 6} = {2, 5, 6, 7} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 5, 6} = {2, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c1157 (h : TenSystem T Q) :
    T {2, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {2, 5, 8, 9} → False := by
  intro a78 n162 n218 n268 n278 n287 n289 n291
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 5, 8} a78
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n162 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n268 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n287 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 5, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n289 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n291 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 5, 8} = {2, 5, 8, 9} by decide)) hS)

theorem c1158 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {2, 5, 8} → False := by
  intro a162 n78
  exact n78 (h.down {0, 2, 5, 8} {2, 5, 8} a162 (by decide) (by decide))

theorem c1162 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {2, 5, 8} → False := by
  intro a268 n78
  exact n78 (h.down {2, 3, 5, 8} {2, 5, 8} a268 (by decide) (by decide))

theorem c1165 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {2, 5, 8, 9} → False := by
  intro a278 n162 n218 n268 n287 n289 n291
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 5, 8} {2, 5, 8} a278 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n162 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n268 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n287 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 5, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n289 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n291 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 5, 8} = {2, 5, 8, 9} by decide)) hS)

theorem c1166 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {2, 5, 8} → False := by
  intro a287 n78
  exact n78 (h.down {2, 5, 6, 8} {2, 5, 8} a287 (by decide) (by decide))

theorem c1167 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {2, 5, 8, 9} → False := by
  intro a287 n162 n218 n268 n278 n289 n291
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 6, 8} {2, 5, 8} a287 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n162 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n268 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n289 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n291 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 5, 8} = {2, 5, 8, 9} by decide)) hS)

theorem c1170 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {2, 5, 8} → False := by
  intro a291 n78
  exact n78 (h.down {2, 5, 8, 9} {2, 5, 8} a291 (by decide) (by decide))

theorem c1171 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 5, 7, 8} → False := by
  intro a291 n162 n218 n268 n278 n287 n289
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 8, 9} {2, 5, 8} a291 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n162 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n268 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact n278 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n287 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 5, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact n289 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 8} = {2, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c1172 (h : TenSystem T Q) :
    T {2, 5, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {2, 5, 8, 9} → False := by
  intro a79 n163 n219 n269 n279 n288 n290 n291
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 5, 9} a79
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n163 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n269 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact n279 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n288 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 5, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact n290 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 9} = {2, 5, 7, 9} by decide)) hS)
  · exact n291 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 5, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1176 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {2, 5, 8, 9} → False := by
  intro a219 n163 n269 n279 n288 n290 n291
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 5, 9} {2, 5, 9} a219 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n163 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n269 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact n279 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n288 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 5, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact n290 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 9} = {2, 5, 7, 9} by decide)) hS)
  · exact n291 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 5, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1184 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {2, 5, 8, 9} → False := by
  intro a290 n163 n219 n269 n279 n288 n291
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 7, 9} {2, 5, 9} a290 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n163 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n269 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact n279 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n288 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 5, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n291 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 5, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1185 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {2, 5, 9} → False := by
  intro a291 n79
  exact n79 (h.down {2, 5, 8, 9} {2, 5, 9} a291 (by decide) (by decide))

theorem c1186 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {2, 5, 7, 9} → False := by
  intro a291 n163 n219 n269 n279 n288 n290
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 8, 9} {2, 5, 9} a291 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n163 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 5, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 5, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n269 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact n279 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 5, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n288 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 5, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact n290 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 5, 9} = {2, 5, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)

theorem c1187 (h : TenSystem T Q) :
    T {2, 6, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 6, 7, 9} → False := by
  intro a80 n164 n220 n270 n280 n286 n292 n293
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 6, 7} a80
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n164 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact n220 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n270 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact n286 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 7} = {2, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n292 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 6, 7} = {2, 6, 7, 8} by decide)) hS)
  · exact n293 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 6, 7} = {2, 6, 7, 9} by decide)) hS)

theorem c1196 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → ¬ T {2, 6, 7} → False := by
  intro a286 n80
  exact n80 (h.down {2, 5, 6, 7} {2, 6, 7} a286 (by decide) (by decide))

theorem c1201 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ Q {0, 2, 6, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → False := by
  intro a293 n164 n220 n270 n280 n286 n292
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 6, 7, 9} {2, 6, 7} a293 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n164 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact n220 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n270 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 6, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact n286 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 7} = {2, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n292 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 6, 7} = {2, 6, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c1202 (h : TenSystem T Q) :
    T {2, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 6, 8, 9} → False := by
  intro a81 n165 n221 n271 n281 n287 n292 n294
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 6, 8} a81
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n165 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n271 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n292 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 6, 8} = {2, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n294 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 6, 8} = {2, 6, 8, 9} by decide)) hS)

theorem c1209 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ T {2, 6, 8} → False := by
  intro a281 n81
  exact n81 (h.down {2, 4, 6, 8} {2, 6, 8} a281 (by decide) (by decide))

theorem c1210 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 6, 8, 9} → False := by
  intro a281 n165 n221 n271 n287 n292 n294
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 8} {2, 6, 8} a281 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n165 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n271 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n287 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n292 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 6, 8} = {2, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n294 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 6, 8} = {2, 6, 8, 9} by decide)) hS)

theorem c1216 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → ¬ Q {0, 2, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 5, 6, 8} → ¬ Q {2, 6, 7, 8} → False := by
  intro a294 n165 n221 n271 n281 n287 n292
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 6, 8, 9} {2, 6, 8} a294 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n165 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n221 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n271 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 6, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n287 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 8} = {2, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n292 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 6, 8} = {2, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c1217 (h : TenSystem T Q) :
    T {2, 6, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {2, 6, 8, 9} → False := by
  intro a82 n166 n222 n272 n282 n288 n293 n294
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 6, 9} a82
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n166 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 6, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n222 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 6, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n272 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 6, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 6, 9} = {2, 4, 6, 9} by decide)) hS)
  · exact n288 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 6, 9} = {2, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n293 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 6, 9} = {2, 6, 7, 9} by decide)) hS)
  · exact n294 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 6, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1218 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {2, 6, 9} → False := by
  intro a166 n82
  exact n82 (h.down {0, 2, 6, 9} {2, 6, 9} a166 (by decide) (by decide))

theorem c1222 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → ¬ T {2, 6, 9} → False := by
  intro a272 n82
  exact n82 (h.down {2, 3, 6, 9} {2, 6, 9} a272 (by decide) (by decide))

theorem c1230 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → ¬ T {2, 6, 9} → False := by
  intro a294 n82
  exact n82 (h.down {2, 6, 8, 9} {2, 6, 9} a294 (by decide) (by decide))

theorem c1247 (h : TenSystem T Q) :
    T {2, 7, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {2, 7, 8, 9} → False := by
  intro a84 n168 n224 n274 n284 n290 n293 n295
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 7, 9} a84
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n168 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 7, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact n224 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n274 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 7, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 7, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n290 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 7, 9} = {2, 5, 7, 9} by decide)) hS)
  · exact n293 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 7, 9} = {2, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n295 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 7, 9} = {2, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1248 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {2, 7, 9} → False := by
  intro a168 n84
  exact n84 (h.down {0, 2, 7, 9} {2, 7, 9} a168 (by decide) (by decide))

theorem c1252 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ T {2, 7, 9} → False := by
  intro a274 n84
  exact n84 (h.down {2, 3, 7, 9} {2, 7, 9} a274 (by decide) (by decide))

theorem c1254 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {2, 7, 9} → False := by
  intro a284 n84
  exact n84 (h.down {2, 4, 7, 9} {2, 7, 9} a284 (by decide) (by decide))

theorem c1258 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ T {2, 7, 9} → False := by
  intro a293 n84
  exact n84 (h.down {2, 6, 7, 9} {2, 7, 9} a293 (by decide) (by decide))

theorem c1262 (h : TenSystem T Q) :
    T {2, 8, 9} → ¬ Q {0, 2, 8, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {2, 4, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {2, 7, 8, 9} → False := by
  intro a85 n169 n225 n275 n285 n291 n294 n295
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 8, 9} a85
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n169 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 8, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 8, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n275 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact n285 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 8, 9} = {2, 4, 8, 9} by decide)) hS)
  · exact n291 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact n294 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact n295 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 8, 9} = {2, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
