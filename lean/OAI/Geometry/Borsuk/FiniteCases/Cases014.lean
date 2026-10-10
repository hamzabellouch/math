import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1270 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → ¬ Q {0, 2, 8, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {2, 3, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {2, 7, 8, 9} → False := by
  intro a285 n169 n225 n275 n291 n294 n295
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 8, 9} {2, 8, 9} a285 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n169 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 8, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact n225 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 8, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n275 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 8, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n291 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact n294 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact n295 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 8, 9} = {2, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1271 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {2, 8, 9} → False := by
  intro a291 n85
  exact n85 (h.down {2, 5, 8, 9} {2, 8, 9} a291 (by decide) (by decide))

theorem c1273 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → ¬ T {2, 8, 9} → False := by
  intro a294 n85
  exact n85 (h.down {2, 6, 8, 9} {2, 8, 9} a294 (by decide) (by decide))

theorem c1275 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → ¬ T {2, 8, 9} → False := by
  intro a295 n85
  exact n85 (h.down {2, 7, 8, 9} {2, 8, 9} a295 (by decide) (by decide))

theorem c1281 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → ¬ Q {0, 3, 4, 5} → ¬ Q {2, 3, 4, 5} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 4, 5, 9} → False := by
  intro a226 n170 n261 n296 n297 n298 n299
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 5} {3, 4, 5} a226 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n170 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 5} = {0, 3, 4, 5} by decide)) hS)
  · exact hne (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 5} = {2, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 5} = {3, 4, 5, 6} by decide)) hS)
  · exact n297 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 5} = {3, 4, 5, 7} by decide)) hS)
  · exact n298 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 5} = {3, 4, 5, 8} by decide)) hS)
  · exact n299 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 5} = {3, 4, 5, 9} by decide)) hS)

theorem c1284 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {3, 4, 5} → False := by
  intro a296 n86
  exact n86 (h.down {3, 4, 5, 6} {3, 4, 5} a296 (by decide) (by decide))

theorem c1286 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {3, 4, 5} → False := by
  intro a297 n86
  exact n86 (h.down {3, 4, 5, 7} {3, 4, 5} a297 (by decide) (by decide))

theorem c1288 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {3, 4, 5} → False := by
  intro a298 n86
  exact n86 (h.down {3, 4, 5, 8} {3, 4, 5} a298 (by decide) (by decide))

theorem c1292 (h : TenSystem T Q) :
    T {3, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 6, 9} → False := by
  intro a87 n171 n227 n262 n296 n300 n301 n302
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 4, 6} a87
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n171 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 6} = {3, 4, 6, 7} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 6} = {3, 4, 6, 8} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 6} = {3, 4, 6, 9} by decide)) hS)

theorem c1296 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 6, 9} → False := by
  intro a227 n171 n262 n296 n300 n301 n302
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 6} {3, 4, 6} a227 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n171 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 6} = {3, 4, 6, 7} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 6} = {3, 4, 6, 8} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 6} = {3, 4, 6, 9} by decide)) hS)

theorem c1297 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {3, 4, 6} → False := by
  intro a262 n87
  exact n87 (h.down {2, 3, 4, 6} {3, 4, 6} a262 (by decide) (by decide))

theorem c1298 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 6, 9} → False := by
  intro a262 n171 n227 n296 n300 n301 n302
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 6} {3, 4, 6} a262 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n171 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 6} = {3, 4, 6, 7} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 6} = {3, 4, 6, 8} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 6} = {3, 4, 6, 9} by decide)) hS)

theorem c1299 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {3, 4, 6} → False := by
  intro a296 n87
  exact n87 (h.down {3, 4, 5, 6} {3, 4, 6} a296 (by decide) (by decide))

theorem c1300 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 6, 9} → False := by
  intro a296 n171 n227 n262 n300 n301 n302
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 6} {3, 4, 6} a296 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n171 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 6} = {3, 4, 6, 7} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 6} = {3, 4, 6, 8} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 6} = {3, 4, 6, 9} by decide)) hS)

theorem c1301 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {3, 4, 6} → False := by
  intro a300 n87
  exact n87 (h.down {3, 4, 6, 7} {3, 4, 6} a300 (by decide) (by decide))

theorem c1302 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 6, 9} → False := by
  intro a300 n171 n227 n262 n296 n301 n302
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 7} {3, 4, 6} a300 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n171 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n301 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 6} = {3, 4, 6, 8} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 6} = {3, 4, 6, 9} by decide)) hS)

theorem c1304 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 9} → False := by
  intro a301 n171 n227 n262 n296 n300 n302
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 8} {3, 4, 6} a301 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n171 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 6} = {3, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n302 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 6} = {3, 4, 6, 9} by decide)) hS)

theorem c1305 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {3, 4, 6} → False := by
  intro a302 n87
  exact n87 (h.down {3, 4, 6, 9} {3, 4, 6} a302 (by decide) (by decide))

theorem c1306 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ Q {0, 3, 4, 6} → ¬ Q {1, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 6, 8} → False := by
  intro a302 n171 n227 n262 n296 n300 n301
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 9} {3, 4, 6} a302 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n171 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact n227 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 6} = {1, 3, 4, 6} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 6} = {3, 4, 6, 7} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 6} = {3, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c1307 (h : TenSystem T Q) :
    T {3, 4, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 4, 7, 9} → False := by
  intro a88 n172 n228 n263 n297 n300 n303 n304
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 4, 7} a88
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n172 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n297 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact n300 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 7} = {3, 4, 7, 8} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 7} = {3, 4, 7, 9} by decide)) hS)

theorem c1309 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 4, 7, 9} → False := by
  intro a172 n228 n263 n297 n300 n303 n304
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 4, 7} {3, 4, 7} a172 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n228 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n297 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact n300 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 7} = {3, 4, 7, 8} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 7} = {3, 4, 7, 9} by decide)) hS)

theorem c1314 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {3, 4, 7} → False := by
  intro a297 n88
  exact n88 (h.down {3, 4, 5, 7} {3, 4, 7} a297 (by decide) (by decide))

theorem c1316 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {3, 4, 7} → False := by
  intro a300 n88
  exact n88 (h.down {3, 4, 6, 7} {3, 4, 7} a300 (by decide) (by decide))

theorem c1317 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 4, 7, 9} → False := by
  intro a300 n172 n228 n263 n297 n303 n304
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 7} {3, 4, 7} a300 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n172 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n297 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 7} = {3, 4, 7, 8} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 7} = {3, 4, 7, 9} by decide)) hS)

theorem c1319 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → ¬ Q {0, 3, 4, 7} → ¬ Q {1, 3, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 4, 7, 9} → False := by
  intro a303 n172 n228 n263 n297 n300 n304
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 8} {3, 4, 7} a303 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n172 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact n228 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 7} = {1, 3, 4, 7} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n297 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact n300 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 7} = {3, 4, 7, 9} by decide)) hS)

theorem c1320 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 4, 7} → False := by
  intro a304 n88
  exact n88 (h.down {3, 4, 7, 9} {3, 4, 7} a304 (by decide) (by decide))

theorem c1322 (h : TenSystem T Q) :
    T {3, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {1, 3, 4, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 4, 8, 9} → False := by
  intro a89 n173 n229 n264 n298 n301 n303 n305
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 4, 8} a89
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n173 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact n229 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 8} = {1, 3, 4, 8} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact n301 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 8} = {3, 4, 6, 8} by decide)) hS)
  · exact n303 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 8} = {3, 4, 8, 9} by decide)) hS)

theorem c1329 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {3, 4, 8} → False := by
  intro a298 n89
  exact n89 (h.down {3, 4, 5, 8} {3, 4, 8} a298 (by decide) (by decide))

theorem c1332 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {1, 3, 4, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 4, 7, 8} → ¬ Q {3, 4, 8, 9} → False := by
  intro a301 n173 n229 n264 n298 n303 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 8} {3, 4, 8} a301 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n173 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact n229 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 8} = {1, 3, 4, 8} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n303 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 8} = {3, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 4, 8} = {3, 4, 8, 9} by decide)) hS)

theorem c1335 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {3, 4, 8} → False := by
  intro a305 n89
  exact n89 (h.down {3, 4, 8, 9} {3, 4, 8} a305 (by decide) (by decide))

theorem c1337 (h : TenSystem T Q) :
    T {3, 4, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a90 n174 n230 n265 n299 n302 n304 n305
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 4, 9} a90
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1340 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {3, 4, 9} → False := by
  intro a230 n90
  exact n90 (h.down {1, 3, 4, 9} {3, 4, 9} a230 (by decide) (by decide))

theorem c1341 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a230 n174 n265 n299 n302 n304 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 4, 9} {3, 4, 9} a230 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n265 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1343 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a265 n174 n230 n299 n302 n304 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 9} {3, 4, 9} a265 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact n304 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1346 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {3, 4, 9} → False := by
  intro a302 n90
  exact n90 (h.down {3, 4, 6, 9} {3, 4, 9} a302 (by decide) (by decide))

theorem c1347 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 7, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a302 n174 n230 n265 n299 n304 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 9} {3, 4, 9} a302 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n304 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 4, 9} = {3, 4, 7, 9} by decide)) hS)
  · exact n305 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1348 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {3, 4, 9} → False := by
  intro a304 n90
  exact n90 (h.down {3, 4, 7, 9} {3, 4, 9} a304 (by decide) (by decide))

theorem c1349 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 4, 6, 9} → ¬ Q {3, 4, 8, 9} → False := by
  intro a304 n174 n230 n265 n299 n302 n305
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 7, 9} {3, 4, 9} a304 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n174 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 4, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n230 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 4, 9} = {1, 3, 4, 9} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 4, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact n302 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 4, 9} = {3, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n305 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 4, 9} = {3, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
