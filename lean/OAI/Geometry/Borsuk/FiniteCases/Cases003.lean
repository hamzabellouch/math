import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c226 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → False := by
  intro a169 n127 n154 n159 n163 n166 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 8, 9} {0, 2, 9} a169 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n154 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)

theorem c227 (h : TenSystem T Q) :
    T {0, 3, 4} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 4, 9} → False := by
  intro a16 n128 n149 n170 n171 n172 n173 n174
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 3, 4} a16
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n128 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact n149 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n170 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 4} = {0, 3, 4, 5} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 4} = {0, 3, 4, 6} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 4} = {0, 3, 4, 7} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 4} = {0, 3, 4, 8} by decide)) hS)
  · exact n174 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 4} = {0, 3, 4, 9} by decide)) hS)

theorem c228 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {0, 3, 4} → False := by
  intro a128 n16
  exact n16 (h.down {0, 1, 3, 4} {0, 3, 4} a128 (by decide) (by decide))

theorem c231 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 4, 9} → False := by
  intro a149 n128 n170 n171 n172 n173 n174
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 4} {0, 3, 4} a149 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n128 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n170 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 4} = {0, 3, 4, 5} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 4} = {0, 3, 4, 6} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 4} = {0, 3, 4, 7} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 4} = {0, 3, 4, 8} by decide)) hS)
  · exact n174 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 4} = {0, 3, 4, 9} by decide)) hS)

theorem c236 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {0, 3, 4} → False := by
  intro a172 n16
  exact n16 (h.down {0, 3, 4, 7} {0, 3, 4} a172 (by decide) (by decide))

theorem c241 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 4, 8} → False := by
  intro a174 n128 n149 n170 n171 n172 n173
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 4, 9} {0, 3, 4} a174 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n128 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact n149 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n170 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 4} = {0, 3, 4, 5} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 4} = {0, 3, 4, 6} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 4} = {0, 3, 4, 7} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 4} = {0, 3, 4, 8} by decide)) hS)
  · exact hne (by decide)

theorem c253 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {0, 3, 5} → False := by
  intro a177 n17
  exact n17 (h.down {0, 3, 5, 8} {0, 3, 5} a177 (by decide) (by decide))

theorem c254 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ Q {0, 1, 3, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 3, 5, 9} → False := by
  intro a177 n129 n150 n170 n175 n176 n178
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 8} {0, 3, 5} a177 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n129 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 5} = {0, 1, 3, 5} by decide)) hS)
  · exact n150 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n170 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 5} = {0, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n175 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 5} = {0, 3, 5, 6} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 5} = {0, 3, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n178 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 5} = {0, 3, 5, 9} by decide)) hS)

theorem c257 (h : TenSystem T Q) :
    T {0, 3, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 2, 3, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 6, 9} → False := by
  intro a18 n130 n151 n171 n175 n179 n180 n181
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 3, 6} a18
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n130 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact n151 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 6} = {0, 2, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n171 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n175 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n179 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 6} = {0, 3, 6, 7} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 6} = {0, 3, 6, 8} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 6} = {0, 3, 6, 9} by decide)) hS)

theorem c258 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {0, 3, 6} → False := by
  intro a130 n18
  exact n18 (h.down {0, 1, 3, 6} {0, 3, 6} a130 (by decide) (by decide))

theorem c263 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 2, 3, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 6, 9} → False := by
  intro a171 n130 n151 n175 n179 n180 n181
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 4, 6} {0, 3, 6} a171 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n130 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact n151 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 6} = {0, 2, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n175 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n179 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 6} = {0, 3, 6, 7} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 6} = {0, 3, 6, 8} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 6} = {0, 3, 6, 9} by decide)) hS)

theorem c264 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → ¬ T {0, 3, 6} → False := by
  intro a175 n18
  exact n18 (h.down {0, 3, 5, 6} {0, 3, 6} a175 (by decide) (by decide))

theorem c266 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {0, 3, 6} → False := by
  intro a179 n18
  exact n18 (h.down {0, 3, 6, 7} {0, 3, 6} a179 (by decide) (by decide))

theorem c268 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {0, 3, 6} → False := by
  intro a180 n18
  exact n18 (h.down {0, 3, 6, 8} {0, 3, 6} a180 (by decide) (by decide))

theorem c271 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 2, 3, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 3, 6, 8} → False := by
  intro a181 n130 n151 n171 n175 n179 n180
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 6, 9} {0, 3, 6} a181 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n130 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact n151 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 6} = {0, 2, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n171 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n175 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n179 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 6} = {0, 3, 6, 7} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 6} = {0, 3, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c272 (h : TenSystem T Q) :
    T {0, 3, 7} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 7, 9} → False := by
  intro a19 n131 n152 n172 n176 n179 n182 n183
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 3, 7} a19
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n131 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact n152 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n172 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n179 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n182 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 7} = {0, 3, 7, 8} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 7} = {0, 3, 7, 9} by decide)) hS)

theorem c276 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 7, 9} → False := by
  intro a152 n131 n172 n176 n179 n182 n183
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 7} {0, 3, 7} a152 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n131 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n172 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n179 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n182 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 7} = {0, 3, 7, 8} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 7} = {0, 3, 7, 9} by decide)) hS)

theorem c279 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → ¬ T {0, 3, 7} → False := by
  intro a176 n19
  exact n19 (h.down {0, 3, 5, 7} {0, 3, 7} a176 (by decide) (by decide))

theorem c281 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {0, 3, 7} → False := by
  intro a179 n19
  exact n19 (h.down {0, 3, 6, 7} {0, 3, 7} a179 (by decide) (by decide))

theorem c282 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 7, 9} → False := by
  intro a179 n131 n152 n172 n176 n182 n183
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 6, 7} {0, 3, 7} a179 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n131 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact n152 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n172 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n182 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 7} = {0, 3, 7, 8} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 7} = {0, 3, 7, 9} by decide)) hS)

theorem c283 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ T {0, 3, 7} → False := by
  intro a182 n19
  exact n19 (h.down {0, 3, 7, 8} {0, 3, 7} a182 (by decide) (by decide))

theorem c284 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 3, 7, 9} → False := by
  intro a182 n131 n152 n172 n176 n179 n183
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 7, 8} {0, 3, 7} a182 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n131 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact n152 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n172 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n179 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n183 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 7} = {0, 3, 7, 9} by decide)) hS)

theorem c285 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {0, 3, 7} → False := by
  intro a183 n19
  exact n19 (h.down {0, 3, 7, 9} {0, 3, 7} a183 (by decide) (by decide))

theorem c286 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 3, 7, 8} → False := by
  intro a183 n131 n152 n172 n176 n179 n182
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 7, 9} {0, 3, 7} a183 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n131 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 7} = {0, 1, 3, 7} by decide)) hS)
  · exact n152 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n172 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n179 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n182 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 7} = {0, 3, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c287 (h : TenSystem T Q) :
    T {0, 3, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 8, 9} → False := by
  intro a20 n132 n153 n173 n177 n180 n182 n184
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 3, 8} a20
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n132 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact n153 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n173 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 8} = {0, 3, 8, 9} by decide)) hS)

theorem c291 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 8, 9} → False := by
  intro a153 n132 n173 n177 n180 n182 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 8} {0, 3, 8} a153 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n132 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n173 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 8} = {0, 3, 8, 9} by decide)) hS)

theorem c292 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ T {0, 3, 8} → False := by
  intro a173 n20
  exact n20 (h.down {0, 3, 4, 8} {0, 3, 8} a173 (by decide) (by decide))

theorem c293 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 8, 9} → False := by
  intro a173 n132 n153 n177 n180 n182 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 4, 8} {0, 3, 8} a173 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n132 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact n153 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n177 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 8} = {0, 3, 8, 9} by decide)) hS)

theorem c294 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {0, 3, 8} → False := by
  intro a177 n20
  exact n20 (h.down {0, 3, 5, 8} {0, 3, 8} a177 (by decide) (by decide))

theorem c295 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 3, 8, 9} → False := by
  intro a177 n132 n153 n173 n180 n182 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 8} {0, 3, 8} a177 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n132 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 8} = {0, 1, 3, 8} by decide)) hS)
  · exact n153 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n173 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n180 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 3, 8} = {0, 3, 8, 9} by decide)) hS)

theorem c296 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {0, 3, 8} → False := by
  intro a180 n20
  exact n20 (h.down {0, 3, 6, 8} {0, 3, 8} a180 (by decide) (by decide))

theorem c298 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ T {0, 3, 8} → False := by
  intro a182 n20
  exact n20 (h.down {0, 3, 7, 8} {0, 3, 8} a182 (by decide) (by decide))

theorem c300 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {0, 3, 8} → False := by
  intro a184 n20
  exact n20 (h.down {0, 3, 8, 9} {0, 3, 8} a184 (by decide) (by decide))

theorem c302 (h : TenSystem T Q) :
    T {0, 3, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 3, 8, 9} → False := by
  intro a21 n133 n154 n174 n178 n181 n183 n184
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 3, 9} a21
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n133 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n154 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n174 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c303 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {0, 3, 9} → False := by
  intro a133 n21
  exact n21 (h.down {0, 1, 3, 9} {0, 3, 9} a133 (by decide) (by decide))

theorem c305 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {0, 3, 9} → False := by
  intro a154 n21
  exact n21 (h.down {0, 2, 3, 9} {0, 3, 9} a154 (by decide) (by decide))

theorem c306 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 3, 8, 9} → False := by
  intro a154 n133 n174 n178 n181 n183 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 9} {0, 3, 9} a154 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n133 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n174 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c307 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {0, 3, 9} → False := by
  intro a174 n21
  exact n21 (h.down {0, 3, 4, 9} {0, 3, 9} a174 (by decide) (by decide))

theorem c308 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 3, 8, 9} → False := by
  intro a174 n133 n154 n178 n181 n183 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 4, 9} {0, 3, 9} a174 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n133 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n154 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n178 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
