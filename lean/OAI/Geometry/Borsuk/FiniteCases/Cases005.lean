import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c388 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {0, 4, 9} → False := by
  intro a193 n26
  exact n26 (h.down {0, 4, 7, 9} {0, 4, 9} a193 (by decide) (by decide))

theorem c392 (h : TenSystem T Q) :
    T {0, 5, 6} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 6, 9} → False := by
  intro a27 n139 n160 n175 n185 n195 n196 n197
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 5, 6} a27
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n139 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact n160 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact n175 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n185 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 6} = {0, 5, 6, 7} by decide)) hS)
  · exact n196 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 6} = {0, 5, 6, 8} by decide)) hS)
  · exact n197 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 6} = {0, 5, 6, 9} by decide)) hS)

theorem c402 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → ¬ Q {0, 1, 5, 6} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 3, 5, 6} → ¬ Q {0, 4, 5, 6} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 6, 9} → False := by
  intro a195 n139 n160 n175 n185 n196 n197
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 7} {0, 5, 6} a195 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n139 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 6} = {0, 1, 5, 6} by decide)) hS)
  · exact n160 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 6} = {0, 2, 5, 6} by decide)) hS)
  · exact n175 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 6} = {0, 3, 5, 6} by decide)) hS)
  · exact n185 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 6} = {0, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 6} = {0, 5, 6, 8} by decide)) hS)
  · exact n197 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 6} = {0, 5, 6, 9} by decide)) hS)

theorem c403 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {0, 5, 6} → False := by
  intro a196 n27
  exact n27 (h.down {0, 5, 6, 8} {0, 5, 6} a196 (by decide) (by decide))

theorem c407 (h : TenSystem T Q) :
    T {0, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 7, 9} → False := by
  intro a28 n140 n161 n176 n186 n195 n198 n199
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 5, 7} a28
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n140 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 7} = {0, 5, 7, 8} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 7} = {0, 5, 7, 9} by decide)) hS)

theorem c415 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 7, 9} → False := by
  intro a186 n140 n161 n176 n195 n198 n199
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 7} {0, 5, 7} a186 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n140 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 7} = {0, 5, 7, 8} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 7} = {0, 5, 7, 9} by decide)) hS)

theorem c417 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 7, 9} → False := by
  intro a195 n140 n161 n176 n186 n198 n199
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 7} {0, 5, 7} a195 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n140 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 7} = {0, 5, 7, 8} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 7} = {0, 5, 7, 9} by decide)) hS)

theorem c421 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → ¬ Q {0, 1, 5, 7} → ¬ Q {0, 2, 5, 7} → ¬ Q {0, 3, 5, 7} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 5, 7, 8} → False := by
  intro a199 n140 n161 n176 n186 n195 n198
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 7, 9} {0, 5, 7} a199 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n140 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact n161 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 7} = {0, 2, 5, 7} by decide)) hS)
  · exact n176 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 7} = {0, 3, 5, 7} by decide)) hS)
  · exact n186 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 7} = {0, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 7} = {0, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c422 (h : TenSystem T Q) :
    T {0, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a29 n141 n162 n177 n187 n196 n198 n200
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 5, 8} a29
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c424 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a141 n162 n177 n187 n196 n198 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 5, 8} {0, 5, 8} a141 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c426 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a162 n141 n177 n187 n196 n198 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 5, 8} {0, 5, 8} a162 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c427 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {0, 5, 8} → False := by
  intro a177 n29
  exact n29 (h.down {0, 3, 5, 8} {0, 5, 8} a177 (by decide) (by decide))

theorem c428 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a177 n141 n162 n187 n196 n198 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 5, 8} {0, 5, 8} a177 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c429 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {0, 5, 8} → False := by
  intro a187 n29
  exact n29 (h.down {0, 4, 5, 8} {0, 5, 8} a187 (by decide) (by decide))

theorem c430 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a187 n141 n162 n177 n196 n198 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 8} {0, 5, 8} a187 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c431 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {0, 5, 8} → False := by
  intro a196 n29
  exact n29 (h.down {0, 5, 6, 8} {0, 5, 8} a196 (by decide) (by decide))

theorem c432 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a196 n141 n162 n177 n187 n198 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 6, 8} {0, 5, 8} a196 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c434 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 8, 9} → False := by
  intro a198 n141 n162 n177 n187 n196 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 7, 8} {0, 5, 8} a198 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n200 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 5, 8} = {0, 5, 8, 9} by decide)) hS)

theorem c435 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {0, 5, 8} → False := by
  intro a200 n29
  exact n29 (h.down {0, 5, 8, 9} {0, 5, 8} a200 (by decide) (by decide))

theorem c436 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → False := by
  intro a200 n141 n162 n177 n187 n196 n198
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 8, 9} {0, 5, 8} a200 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n141 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact n162 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 8} = {0, 2, 5, 8} by decide)) hS)
  · exact n177 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 8} = {0, 3, 5, 8} by decide)) hS)
  · exact n187 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 8} = {0, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c445 (h : TenSystem T Q) :
    Q {0, 4, 5, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {0, 5, 7, 9} → ¬ Q {0, 5, 8, 9} → False := by
  intro a188 n142 n163 n178 n197 n199 n200
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 5, 9} {0, 5, 9} a188 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n142 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n197 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 9} = {0, 5, 7, 9} by decide)) hS)
  · exact n200 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 5, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c448 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → ¬ T {0, 5, 9} → False := by
  intro a199 n30
  exact n30 (h.down {0, 5, 7, 9} {0, 5, 9} a199 (by decide) (by decide))

theorem c450 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {0, 5, 9} → False := by
  intro a200 n30
  exact n30 (h.down {0, 5, 8, 9} {0, 5, 9} a200 (by decide) (by decide))

theorem c451 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 4, 5, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {0, 5, 7, 9} → False := by
  intro a200 n142 n163 n178 n188 n197 n199
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 8, 9} {0, 5, 9} a200 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n142 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 5, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact n163 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 5, 9} = {0, 2, 5, 9} by decide)) hS)
  · exact n178 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 5, 9} = {0, 3, 5, 9} by decide)) hS)
  · exact n188 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 5, 9} = {0, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n197 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 5, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact n199 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 5, 9} = {0, 5, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)

theorem c452 (h : TenSystem T Q) :
    T {0, 6, 7} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 7, 9} → False := by
  intro a31 n143 n164 n179 n189 n195 n201 n202
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 6, 7} a31
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact n164 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact n179 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n189 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n195 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 6, 7} = {0, 6, 7, 8} by decide)) hS)
  · exact n202 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 7} = {0, 6, 7, 9} by decide)) hS)

theorem c454 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 7, 9} → False := by
  intro a143 n164 n179 n189 n195 n201 n202
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 6, 7} {0, 6, 7} a143 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n164 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact n179 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n189 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n195 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 6, 7} = {0, 6, 7, 8} by decide)) hS)
  · exact n202 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 7} = {0, 6, 7, 9} by decide)) hS)

theorem c456 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 7, 9} → False := by
  intro a164 n143 n179 n189 n195 n201 n202
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 6, 7} {0, 6, 7} a164 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n179 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact n189 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 7} = {0, 4, 6, 7} by decide)) hS)
  · exact n195 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 6, 7} = {0, 6, 7, 8} by decide)) hS)
  · exact n202 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 7} = {0, 6, 7, 9} by decide)) hS)

theorem c457 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {0, 6, 7} → False := by
  intro a179 n31
  exact n31 (h.down {0, 3, 6, 7} {0, 6, 7} a179 (by decide) (by decide))

theorem c459 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {0, 6, 7} → False := by
  intro a189 n31
  exact n31 (h.down {0, 4, 6, 7} {0, 6, 7} a189 (by decide) (by decide))

theorem c460 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 2, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 5, 6, 7} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 7, 9} → False := by
  intro a189 n143 n164 n179 n195 n201 n202
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 7} {0, 6, 7} a189 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n143 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact n164 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 7} = {0, 2, 6, 7} by decide)) hS)
  · exact n179 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 7} = {0, 3, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n195 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 7} = {0, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 6, 7} = {0, 6, 7, 8} by decide)) hS)
  · exact n202 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 7} = {0, 6, 7, 9} by decide)) hS)

theorem c467 (h : TenSystem T Q) :
    T {0, 6, 8} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 8, 9} → False := by
  intro a32 n144 n165 n180 n190 n196 n201 n203
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 6, 8} a32
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n144 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 8} = {0, 1, 6, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n196 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 6, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n203 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 8} = {0, 6, 8, 9} by decide)) hS)

theorem c469 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 8, 9} → False := by
  intro a144 n165 n180 n190 n196 n201 n203
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 6, 8} {0, 6, 8} a144 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n165 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact n190 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 8} = {0, 4, 6, 8} by decide)) hS)
  · exact n196 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 6, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n203 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 8} = {0, 6, 8, 9} by decide)) hS)

end BorsukNine.FiniteObstruction

end OAI
