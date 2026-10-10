import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c155 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → ¬ T {0, 2, 5} → False := by
  intro a150 n11
  exact n11 (h.down {0, 2, 3, 5} {0, 2, 5} a150 (by decide) (by decide))

theorem c157 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → ¬ T {0, 2, 5} → False := by
  intro a155 n11
  exact n11 (h.down {0, 2, 4, 5} {0, 2, 5} a155 (by decide) (by decide))

theorem c160 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 5, 9} → False := by
  intro a160 n123 n150 n155 n161 n162 n163
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 5, 6} {0, 2, 5} a160 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n123 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 5} = {0, 1, 2, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n150 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n161 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 5} = {0, 2, 5, 7} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 5} = {0, 2, 5, 8} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 5} = {0, 2, 5, 9} by decide)) hS)

theorem c163 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {0, 2, 5} → False := by
  intro a162 n11
  exact n11 (h.down {0, 2, 5, 8} {0, 2, 5} a162 (by decide) (by decide))

theorem c165 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → ¬ T {0, 2, 5} → False := by
  intro a163 n11
  exact n11 (h.down {0, 2, 5, 9} {0, 2, 5} a163 (by decide) (by decide))

theorem c166 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → ¬ Q {0, 1, 2, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 5, 8} → False := by
  intro a163 n123 n150 n155 n160 n161 n162
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 5, 9} {0, 2, 5} a163 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c170 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {0, 2, 6} → False := by
  intro a151 n12
  exact n12 (h.down {0, 2, 3, 6} {0, 2, 6} a151 (by decide) (by decide))

theorem c171 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 6, 9} → False := by
  intro a151 n124 n156 n160 n164 n165 n166
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 6} {0, 2, 6} a151 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n124 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 6} = {0, 1, 2, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n156 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n160 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n164 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 6} = {0, 2, 6, 7} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 6} = {0, 2, 6, 8} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 6} = {0, 2, 6, 9} by decide)) hS)

theorem c172 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {0, 2, 6} → False := by
  intro a156 n12
  exact n12 (h.down {0, 2, 4, 6} {0, 2, 6} a156 (by decide) (by decide))

theorem c174 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → ¬ T {0, 2, 6} → False := by
  intro a160 n12
  exact n12 (h.down {0, 2, 5, 6} {0, 2, 6} a160 (by decide) (by decide))

theorem c176 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {0, 2, 6} → False := by
  intro a164 n12
  exact n12 (h.down {0, 2, 6, 7} {0, 2, 6} a164 (by decide) (by decide))

theorem c178 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → ¬ T {0, 2, 6} → False := by
  intro a165 n12
  exact n12 (h.down {0, 2, 6, 8} {0, 2, 6} a165 (by decide) (by decide))

theorem c180 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {0, 2, 6} → False := by
  intro a166 n12
  exact n12 (h.down {0, 2, 6, 9} {0, 2, 6} a166 (by decide) (by decide))

theorem c182 (h : TenSystem T Q) :
    T {0, 2, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a13 n125 n152 n157 n161 n164 n167 n168
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 7} a13
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n152 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n164 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 7} = {0, 2, 7, 8} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 7} = {0, 2, 7, 9} by decide)) hS)

theorem c184 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a125 n152 n157 n161 n164 n167 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 7} {0, 2, 7} a125 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n152 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n164 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 7} = {0, 2, 7, 8} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 7} = {0, 2, 7, 9} by decide)) hS)

theorem c185 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {0, 2, 7} → False := by
  intro a152 n13
  exact n13 (h.down {0, 2, 3, 7} {0, 2, 7} a152 (by decide) (by decide))

theorem c187 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {0, 2, 7} → False := by
  intro a157 n13
  exact n13 (h.down {0, 2, 4, 7} {0, 2, 7} a157 (by decide) (by decide))

theorem c188 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a157 n125 n152 n161 n164 n167 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 4, 7} {0, 2, 7} a157 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n152 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n161 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n164 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 7} = {0, 2, 7, 8} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 7} = {0, 2, 7, 9} by decide)) hS)

theorem c189 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → ¬ T {0, 2, 7} → False := by
  intro a161 n13
  exact n13 (h.down {0, 2, 5, 7} {0, 2, 7} a161 (by decide) (by decide))

theorem c190 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a161 n125 n152 n157 n164 n167 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 5, 7} {0, 2, 7} a161 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n152 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n164 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 7} = {0, 2, 7, 8} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 7} = {0, 2, 7, 9} by decide)) hS)

theorem c192 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ Q {0, 1, 2, 7} → ¬ Q {0, 2, 3, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 7, 9} → False := by
  intro a164 n125 n152 n157 n161 n167 n168
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 6, 7} {0, 2, 7} a164 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n125 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 7} = {0, 1, 2, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n152 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 7} = {0, 2, 3, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 7} = {0, 2, 7, 8} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 7} = {0, 2, 7, 9} by decide)) hS)

theorem c193 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ T {0, 2, 7} → False := by
  intro a167 n13
  exact n13 (h.down {0, 2, 7, 8} {0, 2, 7} a167 (by decide) (by decide))

theorem c197 (h : TenSystem T Q) :
    T {0, 2, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a14 n126 n153 n158 n162 n165 n167 n169
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 8} a14
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 8} = {0, 2, 8, 9} by decide)) hS)

theorem c199 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a126 n153 n158 n162 n165 n167 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 8} {0, 2, 8} a126 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 8} = {0, 2, 8, 9} by decide)) hS)

theorem c200 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {0, 2, 8} → False := by
  intro a153 n14
  exact n14 (h.down {0, 2, 3, 8} {0, 2, 8} a153 (by decide) (by decide))

theorem c202 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {0, 2, 8} → False := by
  intro a158 n14
  exact n14 (h.down {0, 2, 4, 8} {0, 2, 8} a158 (by decide) (by decide))

theorem c203 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a158 n126 n153 n162 n165 n167 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 4, 8} {0, 2, 8} a158 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 8} = {0, 2, 8, 9} by decide)) hS)

theorem c204 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {0, 2, 8} → False := by
  intro a162 n14
  exact n14 (h.down {0, 2, 5, 8} {0, 2, 8} a162 (by decide) (by decide))

theorem c205 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a162 n126 n153 n158 n165 n167 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 5, 8} {0, 2, 8} a162 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 8} = {0, 2, 8, 9} by decide)) hS)

theorem c207 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a165 n126 n153 n158 n162 n167 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 6, 8} {0, 2, 8} a165 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 8} = {0, 2, 8, 9} by decide)) hS)

theorem c208 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ T {0, 2, 8} → False := by
  intro a167 n14
  exact n14 (h.down {0, 2, 7, 8} {0, 2, 8} a167 (by decide) (by decide))

theorem c209 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 8, 9} → False := by
  intro a167 n126 n153 n158 n162 n165 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 7, 8} {0, 2, 8} a167 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 2, 8} = {0, 2, 8, 9} by decide)) hS)

theorem c210 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {0, 2, 8} → False := by
  intro a169 n14
  exact n14 (h.down {0, 2, 8, 9} {0, 2, 8} a169 (by decide) (by decide))

theorem c211 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ Q {0, 1, 2, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 2, 7, 8} → False := by
  intro a169 n126 n153 n158 n162 n165 n167
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 8, 9} {0, 2, 8} a169 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n126 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 8} = {0, 1, 2, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n153 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c212 (h : TenSystem T Q) :
    T {0, 2, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {0, 2, 8, 9} → False := by
  intro a15 n127 n154 n159 n163 n166 n168 n169
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 2, 9} a15
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
  · exact n169 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c213 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {0, 2, 9} → False := by
  intro a127 n15
  exact n15 (h.down {0, 1, 2, 9} {0, 2, 9} a127 (by decide) (by decide))

theorem c214 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {0, 2, 8, 9} → False := by
  intro a127 n154 n159 n163 n166 n168 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 9} {0, 2, 9} a127 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n154 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact n169 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c215 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {0, 2, 9} → False := by
  intro a154 n15
  exact n15 (h.down {0, 2, 3, 9} {0, 2, 9} a154 (by decide) (by decide))

theorem c216 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {0, 2, 8, 9} → False := by
  intro a154 n127 n159 n163 n166 n168 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 3, 9} {0, 2, 9} a154 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n159 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 2, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact n169 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c217 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {0, 2, 9} → False := by
  intro a159 n15
  exact n15 (h.down {0, 2, 4, 9} {0, 2, 9} a159 (by decide) (by decide))

theorem c224 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 8, 9} → False := by
  intro a168 n127 n154 n159 n163 n166 n169
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 7, 9} {0, 2, 9} a168 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 2, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n127 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 2, 9} = {0, 1, 2, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n154 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 2, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n159 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 2, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 2, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 2, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n169 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 2, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
