import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}
theorem c3 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 1, 2} → False := by
  intro a121 n1
  exact n1 (h.down {0, 1, 2, 3} {0, 1, 2} a121 (by decide) (by decide))

theorem c4 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ Q {0, 1, 2, 4} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 1, 2, 9} → False := by
  intro a121 n122 n123 n124 n125 n126 n127
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 3} {0, 1, 2} a121 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 2} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n122 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 2} = {0, 1, 2, 4} by decide)) hS)
  · exact n123 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 2} = {0, 1, 2, 5} by decide)) hS)
  · exact n124 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 2} = {0, 1, 2, 6} by decide)) hS)
  · exact n125 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 2} = {0, 1, 2, 7} by decide)) hS)
  · exact n126 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 2} = {0, 1, 2, 8} by decide)) hS)
  · exact n127 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 2} = {0, 1, 2, 9} by decide)) hS)

theorem c18 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 1, 3} → False := by
  intro a121 n2
  exact n2 (h.down {0, 1, 2, 3} {0, 1, 3} a121 (by decide) (by decide))

theorem c19 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 1, 3, 5} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 1, 3, 7} → ¬ Q {0, 1, 3, 8} → ¬ Q {0, 1, 3, 9} → False := by
  intro a121 n128 n129 n130 n131 n132 n133
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 3} {0, 1, 3} a121 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 3} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n128 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 3} = {0, 1, 3, 4} by decide)) hS)
  · exact n129 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 3} = {0, 1, 3, 5} by decide)) hS)
  · exact n130 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 3} = {0, 1, 3, 6} by decide)) hS)
  · exact n131 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 3} = {0, 1, 3, 7} by decide)) hS)
  · exact n132 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 3} = {0, 1, 3, 8} by decide)) hS)
  · exact n133 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 3} = {0, 1, 3, 9} by decide)) hS)

theorem c33 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {0, 1, 4} → False := by
  intro a122 n3
  exact n3 (h.down {0, 1, 2, 4} {0, 1, 4} a122 (by decide) (by decide))

theorem c35 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {0, 1, 4} → False := by
  intro a128 n3
  exact n3 (h.down {0, 1, 3, 4} {0, 1, 4} a128 (by decide) (by decide))

theorem c39 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ T {0, 1, 4} → False := by
  intro a135 n3
  exact n3 (h.down {0, 1, 4, 6} {0, 1, 4} a135 (by decide) (by decide))

theorem c40 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ Q {0, 1, 2, 4} → ¬ Q {0, 1, 3, 4} → ¬ Q {0, 1, 4, 5} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 1, 4, 9} → False := by
  intro a135 n122 n128 n134 n136 n137 n138
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 4, 6} {0, 1, 4} a135 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n122 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 4} = {0, 1, 2, 4} by decide)) hS)
  · exact n128 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 4} = {0, 1, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n134 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 4} = {0, 1, 4, 5} by decide)) hS)
  · exact hne (by decide)
  · exact n136 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 4} = {0, 1, 4, 7} by decide)) hS)
  · exact n137 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 4} = {0, 1, 4, 8} by decide)) hS)
  · exact n138 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 4} = {0, 1, 4, 9} by decide)) hS)

theorem c41 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {0, 1, 4} → False := by
  intro a136 n3
  exact n3 (h.down {0, 1, 4, 7} {0, 1, 4} a136 (by decide) (by decide))

theorem c48 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {0, 1, 5} → False := by
  intro a123 n4
  exact n4 (h.down {0, 1, 2, 5} {0, 1, 5} a123 (by decide) (by decide))

theorem c50 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → ¬ T {0, 1, 5} → False := by
  intro a129 n4
  exact n4 (h.down {0, 1, 3, 5} {0, 1, 5} a129 (by decide) (by decide))

theorem c52 (h : TenSystem T Q) :
    Q {0, 1, 4, 5} → ¬ T {0, 1, 5} → False := by
  intro a134 n4
  exact n4 (h.down {0, 1, 4, 5} {0, 1, 5} a134 (by decide) (by decide))

theorem c54 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → ¬ T {0, 1, 5} → False := by
  intro a139 n4
  exact n4 (h.down {0, 1, 5, 6} {0, 1, 5} a139 (by decide) (by decide))

theorem c56 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ T {0, 1, 5} → False := by
  intro a140 n4
  exact n4 (h.down {0, 1, 5, 7} {0, 1, 5} a140 (by decide) (by decide))

theorem c58 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {0, 1, 5} → False := by
  intro a141 n4
  exact n4 (h.down {0, 1, 5, 8} {0, 1, 5} a141 (by decide) (by decide))

theorem c60 (h : TenSystem T Q) :
    Q {0, 1, 5, 9} → ¬ T {0, 1, 5} → False := by
  intro a142 n4
  exact n4 (h.down {0, 1, 5, 9} {0, 1, 5} a142 (by decide) (by decide))

theorem c62 (h : TenSystem T Q) :
    T {0, 1, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 1, 6, 9} → False := by
  intro a5 n124 n130 n135 n139 n143 n144 n145
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 1, 6} a5
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n124 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact n130 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact n135 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n139 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 6} = {0, 1, 6, 7} by decide)) hS)
  · exact n144 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 6} = {0, 1, 6, 8} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 6} = {0, 1, 6, 9} by decide)) hS)

theorem c63 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {0, 1, 6} → False := by
  intro a124 n5
  exact n5 (h.down {0, 1, 2, 6} {0, 1, 6} a124 (by decide) (by decide))

theorem c65 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {0, 1, 6} → False := by
  intro a130 n5
  exact n5 (h.down {0, 1, 3, 6} {0, 1, 6} a130 (by decide) (by decide))

theorem c66 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 1, 6, 9} → False := by
  intro a130 n124 n135 n139 n143 n144 n145
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 6} {0, 1, 6} a130 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n124 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n135 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n139 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 6} = {0, 1, 6, 7} by decide)) hS)
  · exact n144 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 6} = {0, 1, 6, 8} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 6} = {0, 1, 6, 9} by decide)) hS)

theorem c67 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ T {0, 1, 6} → False := by
  intro a135 n5
  exact n5 (h.down {0, 1, 4, 6} {0, 1, 6} a135 (by decide) (by decide))

theorem c68 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 1, 6, 9} → False := by
  intro a135 n124 n130 n139 n143 n144 n145
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 4, 6} {0, 1, 6} a135 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n124 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact n130 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n139 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 6} = {0, 1, 6, 7} by decide)) hS)
  · exact n144 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 6} = {0, 1, 6, 8} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 6} = {0, 1, 6, 9} by decide)) hS)

theorem c69 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → ¬ T {0, 1, 6} → False := by
  intro a139 n5
  exact n5 (h.down {0, 1, 5, 6} {0, 1, 6} a139 (by decide) (by decide))

theorem c73 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ T {0, 1, 6} → False := by
  intro a144 n5
  exact n5 (h.down {0, 1, 6, 8} {0, 1, 6} a144 (by decide) (by decide))

theorem c76 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 3, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 6, 8} → False := by
  intro a145 n124 n130 n135 n139 n143 n144
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 6, 9} {0, 1, 6} a145 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n124 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact n130 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 6} = {0, 1, 3, 6} by decide)) hS)
  · exact n135 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n139 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 6} = {0, 1, 6, 7} by decide)) hS)
  · exact n144 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 6} = {0, 1, 6, 8} by decide)) hS)
  · exact hne (by decide)

theorem c78 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {0, 1, 7} → False := by
  intro a125 n6
  exact n6 (h.down {0, 1, 2, 7} {0, 1, 7} a125 (by decide) (by decide))

theorem c80 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → ¬ T {0, 1, 7} → False := by
  intro a131 n6
  exact n6 (h.down {0, 1, 3, 7} {0, 1, 7} a131 (by decide) (by decide))

theorem c81 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 1, 7, 9} → False := by
  intro a131 n125 n136 n140 n143 n146 n147
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 3, 7} {0, 1, 7} a131 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n136 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact n140 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n143 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 7} = {0, 1, 7, 8} by decide)) hS)
  · exact n147 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 1, 7} = {0, 1, 7, 9} by decide)) hS)

theorem c82 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {0, 1, 7} → False := by
  intro a136 n6
  exact n6 (h.down {0, 1, 4, 7} {0, 1, 7} a136 (by decide) (by decide))

theorem c84 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ T {0, 1, 7} → False := by
  intro a140 n6
  exact n6 (h.down {0, 1, 5, 7} {0, 1, 7} a140 (by decide) (by decide))

theorem c95 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → ¬ T {0, 1, 8} → False := by
  intro a132 n7
  exact n7 (h.down {0, 1, 3, 8} {0, 1, 8} a132 (by decide) (by decide))

theorem c97 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → ¬ T {0, 1, 8} → False := by
  intro a137 n7
  exact n7 (h.down {0, 1, 4, 8} {0, 1, 8} a137 (by decide) (by decide))

theorem c99 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {0, 1, 8} → False := by
  intro a141 n7
  exact n7 (h.down {0, 1, 5, 8} {0, 1, 8} a141 (by decide) (by decide))

theorem c105 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → ¬ T {0, 1, 8} → False := by
  intro a148 n7
  exact n7 (h.down {0, 1, 8, 9} {0, 1, 8} a148 (by decide) (by decide))

theorem c107 (h : TenSystem T Q) :
    T {0, 1, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 1, 4, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {0, 1, 8, 9} → False := by
  intro a8 n127 n133 n138 n142 n145 n147 n148
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 1, 9} a8
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact n133 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n138 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 9} = {0, 1, 4, 9} by decide)) hS)
  · exact n142 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact n147 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact n148 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c108 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {0, 1, 9} → False := by
  intro a127 n8
  exact n8 (h.down {0, 1, 2, 9} {0, 1, 9} a127 (by decide) (by decide))

theorem c110 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {0, 1, 9} → False := by
  intro a133 n8
  exact n8 (h.down {0, 1, 3, 9} {0, 1, 9} a133 (by decide) (by decide))

theorem c113 (h : TenSystem T Q) :
    Q {0, 1, 4, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {0, 1, 8, 9} → False := by
  intro a138 n127 n133 n142 n145 n147 n148
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 4, 9} {0, 1, 9} a138 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact n133 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n142 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact n147 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 1, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact n148 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c119 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 1, 4, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 1, 8, 9} → False := by
  intro a147 n127 n133 n138 n142 n145 n148
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 7, 9} {0, 1, 9} a147 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 1, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 1, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact n133 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 1, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n138 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 1, 9} = {0, 1, 4, 9} by decide)) hS)
  · exact n142 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 1, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact n145 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 1, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n148 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 1, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c123 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {0, 2, 3} → False := by
  intro a121 n9
  exact n9 (h.down {0, 1, 2, 3} {0, 2, 3} a121 (by decide) (by decide))

theorem c124 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 3, 6} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 3, 9} → False := by
  intro a121 n149 n150 n151 n152 n153 n154
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 3} {0, 2, 3} a121 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 3} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n149 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 3} = {0, 2, 3, 4} by decide)) hS)
  · exact n150 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 3} = {0, 2, 3, 5} by decide)) hS)
  · exact n151 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 3} = {0, 2, 3, 6} by decide)) hS)
  · exact n152 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 3} = {0, 2, 3, 7} by decide)) hS)
  · exact n153 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 3} = {0, 2, 3, 8} by decide)) hS)
  · exact n154 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 3} = {0, 2, 3, 9} by decide)) hS)

theorem c137 (h : TenSystem T Q) :
    T {0, 2, 4} → ¬ Q {0, 1, 2, 4} → ¬ Q {0, 2, 3, 4} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 4, 9} → False := by
  intro a10 n122 n149 n155 n156 n157 n158 n159
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 4} a10
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n122 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 4} = {0, 1, 2, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n149 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n155 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 4} = {0, 2, 4, 5} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 4} = {0, 2, 4, 6} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 4} = {0, 2, 4, 7} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 4} = {0, 2, 4, 8} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 4} = {0, 2, 4, 9} by decide)) hS)

theorem c138 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {0, 2, 4} → False := by
  intro a122 n10
  exact n10 (h.down {0, 1, 2, 4} {0, 2, 4} a122 (by decide) (by decide))

theorem c140 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {0, 2, 4} → False := by
  intro a149 n10
  exact n10 (h.down {0, 2, 3, 4} {0, 2, 4} a149 (by decide) (by decide))

theorem c141 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ Q {0, 1, 2, 4} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 4, 9} → False := by
  intro a149 n122 n155 n156 n157 n158 n159
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 4} {0, 2, 4} a149 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n122 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 4} = {0, 1, 2, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n155 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 4} = {0, 2, 4, 5} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 4} = {0, 2, 4, 6} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 4} = {0, 2, 4, 7} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 4} = {0, 2, 4, 8} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 4} = {0, 2, 4, 9} by decide)) hS)

theorem c142 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → ¬ T {0, 2, 4} → False := by
  intro a155 n10
  exact n10 (h.down {0, 2, 4, 5} {0, 2, 4} a155 (by decide) (by decide))

theorem c144 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {0, 2, 4} → False := by
  intro a156 n10
  exact n10 (h.down {0, 2, 4, 6} {0, 2, 4} a156 (by decide) (by decide))

theorem c146 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {0, 2, 4} → False := by
  intro a157 n10
  exact n10 (h.down {0, 2, 4, 7} {0, 2, 4} a157 (by decide) (by decide))

theorem c148 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {0, 2, 4} → False := by
  intro a158 n10
  exact n10 (h.down {0, 2, 4, 8} {0, 2, 4} a158 (by decide) (by decide))

theorem c150 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {0, 2, 4} → False := by
  intro a159 n10
  exact n10 (h.down {0, 2, 4, 9} {0, 2, 4} a159 (by decide) (by decide))

theorem c152 (h : TenSystem T Q) :
    T {0, 2, 5} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 5, 9} → False := by
  intro a11 n123 n150 n155 n160 n161 n162 n163
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 5} a11
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n123 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 5} = {0, 1, 2, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n150 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n160 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 5} = {0, 2, 5, 6} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 5} = {0, 2, 5, 7} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 5} = {0, 2, 5, 8} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 5} = {0, 2, 5, 9} by decide)) hS)

end BorsukNine.FiniteObstruction

end OAI
