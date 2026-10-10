import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1350 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {3, 4, 9} → False := by
  intro a305 n90
  exact n90 (h.down {3, 4, 8, 9} {3, 4, 9} a305 (by decide) (by decide))

theorem c1352 (h : TenSystem T Q) :
    T {3, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 6, 9} → False := by
  intro a91 n175 n231 n266 n296 n306 n307 n308
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 5, 6} a91
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n175 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n306 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 6} = {3, 5, 6, 7} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 6} = {3, 5, 6, 8} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 6} = {3, 5, 6, 9} by decide)) hS)

theorem c1355 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {3, 5, 6} → False := by
  intro a231 n91
  exact n91 (h.down {1, 3, 5, 6} {3, 5, 6} a231 (by decide) (by decide))

theorem c1359 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {3, 5, 6} → False := by
  intro a296 n91
  exact n91 (h.down {3, 4, 5, 6} {3, 5, 6} a296 (by decide) (by decide))

theorem c1361 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {3, 5, 6} → False := by
  intro a306 n91
  exact n91 (h.down {3, 5, 6, 7} {3, 5, 6} a306 (by decide) (by decide))

theorem c1362 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ Q {0, 3, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 6, 9} → False := by
  intro a306 n175 n231 n266 n296 n307 n308
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 7} {3, 5, 6} a306 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n175 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 6} = {3, 5, 6, 8} by decide)) hS)
  · exact n308 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 6} = {3, 5, 6, 9} by decide)) hS)

theorem c1366 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → ¬ Q {0, 3, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {3, 4, 5, 6} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 5, 6, 8} → False := by
  intro a308 n175 n231 n266 n296 n306 n307
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 9} {3, 5, 6} a308 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n175 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n231 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 6} = {1, 3, 5, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n296 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 6} = {3, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n306 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 6} = {3, 5, 6, 7} by decide)) hS)
  · exact n307 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 6} = {3, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c1367 (h : TenSystem T Q) :
    T {3, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {2, 3, 5, 7} → ¬ Q {3, 4, 5, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 7, 9} → False := by
  intro a92 n176 n232 n267 n297 n306 n309 n310
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 5, 7} a92
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n176 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n267 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 7} = {2, 3, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n297 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 7} = {3, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n306 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 7} = {3, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n309 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 7} = {3, 5, 7, 8} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 7} = {3, 5, 7, 9} by decide)) hS)

theorem c1376 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {3, 5, 7} → False := by
  intro a306 n92
  exact n92 (h.down {3, 5, 6, 7} {3, 5, 7} a306 (by decide) (by decide))

theorem c1382 (h : TenSystem T Q) :
    T {3, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a93 n177 n233 n268 n298 n307 n309 n311
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 5, 8} a93
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1383 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {3, 5, 8} → False := by
  intro a177 n93
  exact n93 (h.down {0, 3, 5, 8} {3, 5, 8} a177 (by decide) (by decide))

theorem c1384 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a177 n233 n268 n298 n307 n309 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 8} {3, 5, 8} a177 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1386 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a233 n177 n268 n298 n307 n309 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 3, 5, 8} {3, 5, 8} a233 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1388 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a268 n177 n233 n298 n307 n309 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 5, 8} {3, 5, 8} a268 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1389 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {3, 5, 8} → False := by
  intro a298 n93
  exact n93 (h.down {3, 4, 5, 8} {3, 5, 8} a298 (by decide) (by decide))

theorem c1390 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a298 n177 n233 n268 n307 n309 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 8} {3, 5, 8} a298 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1391 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {3, 5, 8} → False := by
  intro a307 n93
  exact n93 (h.down {3, 5, 6, 8} {3, 5, 8} a307 (by decide) (by decide))

theorem c1392 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 7, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a307 n177 n233 n268 n298 n309 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 8} {3, 5, 8} a307 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1393 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {3, 5, 8} → False := by
  intro a309 n93
  exact n93 (h.down {3, 5, 7, 8} {3, 5, 8} a309 (by decide) (by decide))

theorem c1394 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 8, 9} → False := by
  intro a309 n177 n233 n268 n298 n307 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 7, 8} {3, 5, 8} a309 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 5, 8} = {3, 5, 8, 9} by decide)) hS)

theorem c1395 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 8} → False := by
  intro a311 n93
  exact n93 (h.down {3, 5, 8, 9} {3, 5, 8} a311 (by decide) (by decide))

theorem c1396 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {3, 4, 5, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {3, 5, 7, 8} → False := by
  intro a311 n177 n233 n268 n298 n307 n309
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 8, 9} {3, 5, 8} a311 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n177 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n298 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 8} = {3, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n307 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 8} = {3, 5, 6, 8} by decide)) hS)
  · exact n309 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 8} = {3, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c1397 (h : TenSystem T Q) :
    T {3, 5, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 5, 8, 9} → False := by
  intro a94 n178 n234 n269 n299 n308 n310 n311
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 5, 9} a94
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n178 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n308 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1399 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 5, 8, 9} → False := by
  intro a178 n234 n269 n299 n308 n310 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 9} {3, 5, 9} a178 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n234 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n308 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1400 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {3, 5, 9} → False := by
  intro a234 n94
  exact n94 (h.down {1, 3, 5, 9} {3, 5, 9} a234 (by decide) (by decide))

theorem c1405 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {3, 5, 8, 9} → False := by
  intro a299 n178 n234 n269 n308 n310 n311
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 5, 9} {3, 5, 9} a299 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n178 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n308 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact n311 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 5, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1410 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {3, 5, 9} → False := by
  intro a311 n94
  exact n94 (h.down {3, 5, 8, 9} {3, 5, 9} a311 (by decide) (by decide))

theorem c1411 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {3, 4, 5, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {3, 5, 7, 9} → False := by
  intro a311 n178 n234 n269 n299 n308 n310
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 8, 9} {3, 5, 9} a311 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n178 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 5, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 5, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 5, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n299 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 5, 9} = {3, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n308 (Eq.mp (congrArg Q (show insert (6 : Labels) {3, 5, 9} = {3, 5, 6, 9} by decide)) hS)
  · exact n310 (Eq.mp (congrArg Q (show insert (7 : Labels) {3, 5, 9} = {3, 5, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)

theorem c1412 (h : TenSystem T Q) :
    T {3, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 7, 9} → False := by
  intro a95 n179 n235 n270 n300 n306 n312 n313
  obtain ⟨S, hS, hUS⟩ := h.pure {3, 6, 7} a95
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n179 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n270 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact n306 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 7} = {3, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 7} = {3, 6, 7, 8} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 7} = {3, 6, 7, 9} by decide)) hS)

theorem c1413 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {3, 6, 7} → False := by
  intro a179 n95
  exact n95 (h.down {0, 3, 6, 7} {3, 6, 7} a179 (by decide) (by decide))

theorem c1419 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {3, 6, 7} → False := by
  intro a300 n95
  exact n95 (h.down {3, 4, 6, 7} {3, 6, 7} a300 (by decide) (by decide))

theorem c1420 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 7, 9} → False := by
  intro a300 n179 n235 n270 n306 n312 n313
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 4, 6, 7} {3, 6, 7} a300 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n179 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n270 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n306 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 7} = {3, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 7} = {3, 6, 7, 8} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 7} = {3, 6, 7, 9} by decide)) hS)

theorem c1422 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 6, 7, 8} → ¬ Q {3, 6, 7, 9} → False := by
  intro a306 n179 n235 n270 n300 n312 n313
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 6, 7} {3, 6, 7} a306 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n179 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n270 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 7} = {3, 6, 7, 8} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 7} = {3, 6, 7, 9} by decide)) hS)

theorem c1424 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 6, 7, 9} → False := by
  intro a312 n179 n235 n270 n300 n306 n313
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 8} {3, 6, 7} a312 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n179 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n270 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact n306 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 7} = {3, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (9 : Labels) {3, 6, 7} = {3, 6, 7, 9} by decide)) hS)

theorem c1425 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {3, 6, 7} → False := by
  intro a313 n95
  exact n95 (h.down {3, 6, 7, 9} {3, 6, 7} a313 (by decide) (by decide))

theorem c1426 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ Q {0, 3, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {3, 5, 6, 7} → ¬ Q {3, 6, 7, 8} → False := by
  intro a313 n179 n235 n270 n300 n306 n312
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 9} {3, 6, 7} a313 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {3, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n179 (Eq.mp (congrArg Q (show insert (0 : Labels) {3, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (1 : Labels) {3, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n270 (Eq.mp (congrArg Q (show insert (2 : Labels) {3, 6, 7} = {2, 3, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n300 (Eq.mp (congrArg Q (show insert (4 : Labels) {3, 6, 7} = {3, 4, 6, 7} by decide)) hS)
  · exact n306 (Eq.mp (congrArg Q (show insert (5 : Labels) {3, 6, 7} = {3, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n312 (Eq.mp (congrArg Q (show insert (8 : Labels) {3, 6, 7} = {3, 6, 7, 8} by decide)) hS)
  · exact hne (by decide)

end BorsukNine.FiniteObstruction

end OAI
