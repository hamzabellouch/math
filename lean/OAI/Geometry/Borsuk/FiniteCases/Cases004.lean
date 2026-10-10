import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c312 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 3, 8, 9} → False := by
  intro a181 n133 n154 n174 n178 n183 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 6, 9} {0, 3, 9} a181 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n133 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n154 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n174 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n183 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 3, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c313 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {0, 3, 9} → False := by
  intro a183 n21
  exact n21 (h.down {0, 3, 7, 9} {0, 3, 9} a183 (by decide) (by decide))

theorem c314 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ Q {0, 1, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {0, 3, 4, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 3, 8, 9} → False := by
  intro a183 n133 n154 n174 n178 n181 n184
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 7, 9} {0, 3, 9} a183 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n133 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 3, 9} = {0, 1, 3, 9} by decide)) hS)
  · exact n154 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n174 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 3, 9} = {0, 3, 4, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 3, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 3, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n184 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 3, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c317 (h : TenSystem T Q) :
    T {0, 4, 5} → ¬ Q {0, 1, 4, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 5, 9} → False := by
  intro a22 n134 n155 n170 n185 n186 n187 n188
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 4, 5} a22
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n134 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact n170 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 5} = {0, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 5} = {0, 4, 5, 6} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 5} = {0, 4, 5, 7} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 5} = {0, 4, 5, 8} by decide)) hS)
  · exact n188 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 5} = {0, 4, 5, 9} by decide)) hS)

theorem c318 (h : TenSystem T Q) :
    Q {0, 1, 4, 5} → ¬ T {0, 4, 5} → False := by
  intro a134 n22
  exact n22 (h.down {0, 1, 4, 5} {0, 4, 5} a134 (by decide) (by decide))

theorem c322 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → ¬ T {0, 4, 5} → False := by
  intro a170 n22
  exact n22 (h.down {0, 3, 4, 5} {0, 4, 5} a170 (by decide) (by decide))

theorem c324 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ T {0, 4, 5} → False := by
  intro a185 n22
  exact n22 (h.down {0, 4, 5, 6} {0, 4, 5} a185 (by decide) (by decide))

theorem c326 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → ¬ T {0, 4, 5} → False := by
  intro a186 n22
  exact n22 (h.down {0, 4, 5, 7} {0, 4, 5} a186 (by decide) (by decide))

theorem c327 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → ¬ Q {0, 1, 4, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 5, 9} → False := by
  intro a186 n134 n155 n170 n185 n187 n188
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 7} {0, 4, 5} a186 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n134 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact n170 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 5} = {0, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 5} = {0, 4, 5, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 5} = {0, 4, 5, 8} by decide)) hS)
  · exact n188 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 5} = {0, 4, 5, 9} by decide)) hS)

theorem c328 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {0, 4, 5} → False := by
  intro a187 n22
  exact n22 (h.down {0, 4, 5, 8} {0, 4, 5} a187 (by decide) (by decide))

theorem c329 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {0, 1, 4, 5} → ¬ Q {0, 2, 4, 5} → ¬ Q {0, 3, 4, 5} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 5, 9} → False := by
  intro a187 n134 n155 n170 n185 n186 n188
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {0, 4, 5} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n134 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 5} = {0, 1, 4, 5} by decide)) hS)
  · exact n155 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 5} = {0, 2, 4, 5} by decide)) hS)
  · exact n170 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 5} = {0, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 5} = {0, 4, 5, 6} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 5} = {0, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n188 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 5} = {0, 4, 5, 9} by decide)) hS)

theorem c332 (h : TenSystem T Q) :
    T {0, 4, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 6, 9} → False := by
  intro a23 n135 n156 n171 n185 n189 n190 n191
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 4, 6} a23
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n135 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n189 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 6} = {0, 4, 6, 7} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 6} = {0, 4, 6, 8} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 6} = {0, 4, 6, 9} by decide)) hS)

theorem c334 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 6, 9} → False := by
  intro a135 n156 n171 n185 n189 n190 n191
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 4, 6} {0, 4, 6} a135 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n156 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n189 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 6} = {0, 4, 6, 7} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 6} = {0, 4, 6, 8} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 6} = {0, 4, 6, 9} by decide)) hS)

theorem c336 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 6, 9} → False := by
  intro a156 n135 n171 n185 n189 n190 n191
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 4, 6} {0, 4, 6} a156 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n135 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n171 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n189 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 6} = {0, 4, 6, 7} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 6} = {0, 4, 6, 8} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 6} = {0, 4, 6, 9} by decide)) hS)

theorem c338 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 6, 9} → False := by
  intro a171 n135 n156 n185 n189 n190 n191
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 4, 6} {0, 4, 6} a171 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n135 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n189 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 6} = {0, 4, 6, 7} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 6} = {0, 4, 6, 8} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 6} = {0, 4, 6, 9} by decide)) hS)

theorem c339 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ T {0, 4, 6} → False := by
  intro a185 n23
  exact n23 (h.down {0, 4, 5, 6} {0, 4, 6} a185 (by decide) (by decide))

theorem c340 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 6, 9} → False := by
  intro a185 n135 n156 n171 n189 n190 n191
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 6} {0, 4, 6} a185 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n135 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n189 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 6} = {0, 4, 6, 7} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 6} = {0, 4, 6, 8} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 6} = {0, 4, 6, 9} by decide)) hS)

theorem c341 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {0, 4, 6} → False := by
  intro a189 n23
  exact n23 (h.down {0, 4, 6, 7} {0, 4, 6} a189 (by decide) (by decide))

theorem c344 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ Q {0, 1, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {0, 3, 4, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 6, 9} → False := by
  intro a190 n135 n156 n171 n185 n189 n191
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 8} {0, 4, 6} a190 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n135 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 6} = {0, 1, 4, 6} by decide)) hS)
  · exact n156 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n171 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 6} = {0, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n185 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n189 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 6} = {0, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n191 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 6} = {0, 4, 6, 9} by decide)) hS)

theorem c347 (h : TenSystem T Q) :
    T {0, 4, 7} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 7, 9} → False := by
  intro a24 n136 n157 n172 n186 n189 n192 n193
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 4, 7} a24
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n136 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n186 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact n189 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n192 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 7} = {0, 4, 7, 8} by decide)) hS)
  · exact n193 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 7} = {0, 4, 7, 9} by decide)) hS)

theorem c348 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {0, 4, 7} → False := by
  intro a136 n24
  exact n24 (h.down {0, 1, 4, 7} {0, 4, 7} a136 (by decide) (by decide))

theorem c350 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {0, 4, 7} → False := by
  intro a157 n24
  exact n24 (h.down {0, 2, 4, 7} {0, 4, 7} a157 (by decide) (by decide))

theorem c352 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {0, 4, 7} → False := by
  intro a172 n24
  exact n24 (h.down {0, 3, 4, 7} {0, 4, 7} a172 (by decide) (by decide))

theorem c356 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {0, 4, 7} → False := by
  intro a189 n24
  exact n24 (h.down {0, 4, 6, 7} {0, 4, 7} a189 (by decide) (by decide))

theorem c357 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 7, 9} → False := by
  intro a189 n136 n157 n172 n186 n192 n193
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 7} {0, 4, 7} a189 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n136 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n186 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n192 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 7} = {0, 4, 7, 8} by decide)) hS)
  · exact n193 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 7} = {0, 4, 7, 9} by decide)) hS)

theorem c359 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 7, 9} → False := by
  intro a192 n136 n157 n172 n186 n189 n193
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 7, 8} {0, 4, 7} a192 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n136 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n186 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact n189 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n193 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 7} = {0, 4, 7, 9} by decide)) hS)

theorem c360 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {0, 4, 7} → False := by
  intro a193 n24
  exact n24 (h.down {0, 4, 7, 9} {0, 4, 7} a193 (by decide) (by decide))

theorem c361 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 4, 7, 8} → False := by
  intro a193 n136 n157 n172 n186 n189 n192
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 7, 9} {0, 4, 7} a193 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n136 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 7} = {0, 1, 4, 7} by decide)) hS)
  · exact n157 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n172 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 7} = {0, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n186 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact n189 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n192 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 4, 7} = {0, 4, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c362 (h : TenSystem T Q) :
    T {0, 4, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 8, 9} → False := by
  intro a25 n137 n158 n173 n187 n190 n192 n194
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 4, 8} a25
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n194 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 8} = {0, 4, 8, 9} by decide)) hS)

theorem c369 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {0, 4, 8} → False := by
  intro a187 n25
  exact n25 (h.down {0, 4, 5, 8} {0, 4, 8} a187 (by decide) (by decide))

theorem c370 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 8, 9} → False := by
  intro a187 n137 n158 n173 n190 n192 n194
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {0, 4, 8} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n190 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n194 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 8} = {0, 4, 8, 9} by decide)) hS)

theorem c372 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 8, 9} → False := by
  intro a190 n137 n158 n173 n187 n192 n194
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 8} {0, 4, 8} a190 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n192 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n194 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 8} = {0, 4, 8, 9} by decide)) hS)

theorem c374 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 8, 9} → False := by
  intro a192 n137 n158 n173 n187 n190 n194
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 7, 8} {0, 4, 8} a192 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n194 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 4, 8} = {0, 4, 8, 9} by decide)) hS)

theorem c376 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ Q {0, 1, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {0, 3, 4, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 4, 7, 8} → False := by
  intro a194 n137 n158 n173 n187 n190 n192
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 8, 9} {0, 4, 8} a194 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n137 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 4, 8} = {0, 1, 4, 8} by decide)) hS)
  · exact n158 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n173 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 4, 8} = {0, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 4, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 4, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 4, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c380 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {0, 4, 9} → False := by
  intro a159 n26
  exact n26 (h.down {0, 2, 4, 9} {0, 4, 9} a159 (by decide) (by decide))

theorem c382 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {0, 4, 9} → False := by
  intro a174 n26
  exact n26 (h.down {0, 3, 4, 9} {0, 4, 9} a174 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
