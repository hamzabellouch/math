import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1732 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a291 n116
  exact n116 (h.down {2, 5, 8, 9} {5, 8, 9} a291 (by decide) (by decide))

theorem c1733 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a291 n200 n256 n311 n321 n328 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 5, 8, 9} {5, 8, 9} a291 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n200 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n311 (Eq.mp (congrArg Q (show insert (3 : Labels) {5, 8, 9} = {3, 5, 8, 9} by decide)) hS)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1734 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a311 n116
  exact n116 (h.down {3, 5, 8, 9} {5, 8, 9} a311 (by decide) (by decide))

theorem c1735 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {4, 5, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {5, 7, 8, 9} → False := by
  intro a311 n200 n256 n291 n321 n328 n329
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 5, 8, 9} {5, 8, 9} a311 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {5, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n200 (Eq.mp (congrArg Q (show insert (0 : Labels) {5, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (1 : Labels) {5, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n291 (Eq.mp (congrArg Q (show insert (2 : Labels) {5, 8, 9} = {2, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n321 (Eq.mp (congrArg Q (show insert (4 : Labels) {5, 8, 9} = {4, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n328 (Eq.mp (congrArg Q (show insert (6 : Labels) {5, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (7 : Labels) {5, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1742 (h : TenSystem T Q) :
    T {6, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {3, 6, 7, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {6, 7, 8, 9} → False := by
  intro a117 n201 n257 n292 n312 n322 n326 n330
  obtain ⟨S, hS, hUS⟩ := h.pure {6, 7, 8} a117
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n201 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact n257 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact n292 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 8} = {2, 6, 7, 8} by decide)) hS)
  · exact n312 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 8} = {3, 6, 7, 8} by decide)) hS)
  · exact n322 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact n326 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (9 : Labels) {6, 7, 8} = {6, 7, 8, 9} by decide)) hS)

theorem c1743 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → ¬ T {6, 7, 8} → False := by
  intro a201 n117
  exact n117 (h.down {0, 6, 7, 8} {6, 7, 8} a201 (by decide) (by decide))

theorem c1747 (h : TenSystem T Q) :
    Q {2, 6, 7, 8} → ¬ T {6, 7, 8} → False := by
  intro a292 n117
  exact n117 (h.down {2, 6, 7, 8} {6, 7, 8} a292 (by decide) (by decide))

theorem c1749 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {6, 7, 8} → False := by
  intro a312 n117
  exact n117 (h.down {3, 6, 7, 8} {6, 7, 8} a312 (by decide) (by decide))

theorem c1750 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {4, 6, 7, 8} → ¬ Q {5, 6, 7, 8} → ¬ Q {6, 7, 8, 9} → False := by
  intro a312 n201 n257 n292 n322 n326 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 7, 8} {6, 7, 8} a312 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n201 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact n257 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact n292 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 8} = {2, 6, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n322 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 8} = {4, 6, 7, 8} by decide)) hS)
  · exact n326 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 8} = {5, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (9 : Labels) {6, 7, 8} = {6, 7, 8, 9} by decide)) hS)

theorem c1757 (h : TenSystem T Q) :
    T {6, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a118 n202 n258 n293 n313 n323 n327 n330
  obtain ⟨S, hS, hUS⟩ := h.pure {6, 7, 9} a118
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n202 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact n293 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 9} = {2, 6, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (8 : Labels) {6, 7, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1758 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a202 n118
  exact n118 (h.down {0, 6, 7, 9} {6, 7, 9} a202 (by decide) (by decide))

theorem c1759 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a202 n258 n293 n313 n323 n327 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 7, 9} {6, 7, 9} a202 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n258 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact n293 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 9} = {2, 6, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (8 : Labels) {6, 7, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1760 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a258 n118
  exact n118 (h.down {1, 6, 7, 9} {6, 7, 9} a258 (by decide) (by decide))

theorem c1761 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {2, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a258 n202 n293 n313 n323 n327 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 7, 9} {6, 7, 9} a258 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n202 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n293 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 7, 9} = {2, 6, 7, 9} by decide)) hS)
  · exact n313 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (8 : Labels) {6, 7, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1763 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → ¬ Q {4, 6, 7, 9} → ¬ Q {5, 6, 7, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a293 n202 n258 n313 n323 n327 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 6, 7, 9} {6, 7, 9} a293 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n202 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 7, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n313 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 7, 9} = {3, 6, 7, 9} by decide)) hS)
  · exact n323 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 7, 9} = {4, 6, 7, 9} by decide)) hS)
  · exact n327 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 7, 9} = {5, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (8 : Labels) {6, 7, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1764 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a313 n118
  exact n118 (h.down {3, 6, 7, 9} {6, 7, 9} a313 (by decide) (by decide))

theorem c1772 (h : TenSystem T Q) :
    T {6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a119 n203 n259 n294 n314 n324 n328 n330
  obtain ⟨S, hS, hUS⟩ := h.pure {6, 8, 9} a119
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n203 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n294 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1774 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a203 n259 n294 n314 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 8, 9} {6, 8, 9} a203 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact n259 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n294 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1775 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a259 n119
  exact n119 (h.down {1, 6, 8, 9} {6, 8, 9} a259 (by decide) (by decide))

theorem c1776 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a259 n203 n294 n314 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 8, 9} {6, 8, 9} a259 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n203 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n294 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact n314 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1778 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {3, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a294 n203 n259 n314 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 6, 8, 9} {6, 8, 9} a294 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n203 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n314 (Eq.mp (congrArg Q (show insert (3 : Labels) {6, 8, 9} = {3, 6, 8, 9} by decide)) hS)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1779 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a314 n119
  exact n119 (h.down {3, 6, 8, 9} {6, 8, 9} a314 (by decide) (by decide))

theorem c1780 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → ¬ Q {4, 6, 8, 9} → ¬ Q {5, 6, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a314 n203 n259 n294 n324 n328 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 6, 8, 9} {6, 8, 9} a314 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {6, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n203 (Eq.mp (congrArg Q (show insert (0 : Labels) {6, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (1 : Labels) {6, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n294 (Eq.mp (congrArg Q (show insert (2 : Labels) {6, 8, 9} = {2, 6, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n324 (Eq.mp (congrArg Q (show insert (4 : Labels) {6, 8, 9} = {4, 6, 8, 9} by decide)) hS)
  · exact n328 (Eq.mp (congrArg Q (show insert (5 : Labels) {6, 8, 9} = {5, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n330 (Eq.mp (congrArg Q (show insert (7 : Labels) {6, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1787 (h : TenSystem T Q) :
    T {7, 8, 9} → ¬ Q {0, 7, 8, 9} → ¬ Q {1, 7, 8, 9} → ¬ Q {2, 7, 8, 9} → ¬ Q {3, 7, 8, 9} → ¬ Q {4, 7, 8, 9} → ¬ Q {5, 7, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a120 n204 n260 n295 n315 n325 n329 n330
  obtain ⟨S, hS, hUS⟩ := h.pure {7, 8, 9} a120
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {7, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n204 (Eq.mp (congrArg Q (show insert (0 : Labels) {7, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact n260 (Eq.mp (congrArg Q (show insert (1 : Labels) {7, 8, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact n295 (Eq.mp (congrArg Q (show insert (2 : Labels) {7, 8, 9} = {2, 7, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (3 : Labels) {7, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact n325 (Eq.mp (congrArg Q (show insert (4 : Labels) {7, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (5 : Labels) {7, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact n330 (Eq.mp (congrArg Q (show insert (6 : Labels) {7, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1788 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a204 n120
  exact n120 (h.down {0, 7, 8, 9} {7, 8, 9} a204 (by decide) (by decide))

theorem c1790 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a260 n120
  exact n120 (h.down {1, 7, 8, 9} {7, 8, 9} a260 (by decide) (by decide))

theorem c1791 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → ¬ Q {0, 7, 8, 9} → ¬ Q {2, 7, 8, 9} → ¬ Q {3, 7, 8, 9} → ¬ Q {4, 7, 8, 9} → ¬ Q {5, 7, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a260 n204 n295 n315 n325 n329 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 7, 8, 9} {7, 8, 9} a260 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {7, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n204 (Eq.mp (congrArg Q (show insert (0 : Labels) {7, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n295 (Eq.mp (congrArg Q (show insert (2 : Labels) {7, 8, 9} = {2, 7, 8, 9} by decide)) hS)
  · exact n315 (Eq.mp (congrArg Q (show insert (3 : Labels) {7, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact n325 (Eq.mp (congrArg Q (show insert (4 : Labels) {7, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (5 : Labels) {7, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact n330 (Eq.mp (congrArg Q (show insert (6 : Labels) {7, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1792 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a295 n120
  exact n120 (h.down {2, 7, 8, 9} {7, 8, 9} a295 (by decide) (by decide))

theorem c1793 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → ¬ Q {0, 7, 8, 9} → ¬ Q {1, 7, 8, 9} → ¬ Q {3, 7, 8, 9} → ¬ Q {4, 7, 8, 9} → ¬ Q {5, 7, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a295 n204 n260 n315 n325 n329 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 7, 8, 9} {7, 8, 9} a295 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {7, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n204 (Eq.mp (congrArg Q (show insert (0 : Labels) {7, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact n260 (Eq.mp (congrArg Q (show insert (1 : Labels) {7, 8, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n315 (Eq.mp (congrArg Q (show insert (3 : Labels) {7, 8, 9} = {3, 7, 8, 9} by decide)) hS)
  · exact n325 (Eq.mp (congrArg Q (show insert (4 : Labels) {7, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (5 : Labels) {7, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact n330 (Eq.mp (congrArg Q (show insert (6 : Labels) {7, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1794 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a315 n120
  exact n120 (h.down {3, 7, 8, 9} {7, 8, 9} a315 (by decide) (by decide))

theorem c1795 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ Q {0, 7, 8, 9} → ¬ Q {1, 7, 8, 9} → ¬ Q {2, 7, 8, 9} → ¬ Q {4, 7, 8, 9} → ¬ Q {5, 7, 8, 9} → ¬ Q {6, 7, 8, 9} → False := by
  intro a315 n204 n260 n295 n325 n329 n330
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {3, 7, 8, 9} {7, 8, 9} a315 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {7, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n204 (Eq.mp (congrArg Q (show insert (0 : Labels) {7, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact n260 (Eq.mp (congrArg Q (show insert (1 : Labels) {7, 8, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact n295 (Eq.mp (congrArg Q (show insert (2 : Labels) {7, 8, 9} = {2, 7, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n325 (Eq.mp (congrArg Q (show insert (4 : Labels) {7, 8, 9} = {4, 7, 8, 9} by decide)) hS)
  · exact n329 (Eq.mp (congrArg Q (show insert (5 : Labels) {7, 8, 9} = {5, 7, 8, 9} by decide)) hS)
  · exact n330 (Eq.mp (congrArg Q (show insert (6 : Labels) {7, 8, 9} = {6, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c1802 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {7, 8, 9} → False := by
  intro a121 n101 n120
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 6} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n101 (hc.mpr n120)

theorem c1803 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {7, 8, 9} → False := by
  intro a121 a101 a120
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 6} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a101 a120

theorem c1804 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {6, 8, 9} → False := by
  intro a121 n102 n119
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n102 (hc.mpr n119)

theorem c1805 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 7} → T {6, 8, 9} → False := by
  intro a121 a102 a119
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a102 a119

theorem c1806 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {6, 7, 9} → False := by
  intro a121 n103 n118
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n103 (hc.mpr n118)

theorem c1807 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {6, 7, 9} → False := by
  intro a121 a103 a118
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a103 a118

theorem c1808 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {6, 7, 8} → False := by
  intro a121 n104 n117
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n104 (hc.mpr n117)

theorem c1809 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 9} → T {6, 7, 8} → False := by
  intro a121 a104 a117
  have hc := h.complementary {0, 1, 2, 3} {4, 5, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a104 a117

end BorsukNine.FiniteObstruction

end OAI
