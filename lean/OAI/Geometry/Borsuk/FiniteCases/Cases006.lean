import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c475 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 6, 8, 9} → False := by
  intro a190 n144 n165 n180 n196 n201 n203
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 6, 8} {0, 6, 8} a190 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n144 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 8} = {0, 1, 6, 8} by decide)) hS)
  · exact n165 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 8} = {0, 2, 6, 8} by decide)) hS)
  · exact n180 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 8} = {0, 3, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n196 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 8} = {0, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n201 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 6, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n203 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 6, 8} = {0, 6, 8, 9} by decide)) hS)

theorem c476 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {0, 6, 8} → False := by
  intro a196 n32
  exact n32 (h.down {0, 5, 6, 8} {0, 6, 8} a196 (by decide) (by decide))

theorem c481 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ Q {0, 1, 6, 8} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 3, 6, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 7, 8} → False := by
  intro a203 n144 n165 n180 n190 n196 n201
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 8, 9} {0, 6, 8} a203 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c482 (h : TenSystem T Q) :
    T {0, 6, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {0, 6, 8, 9} → False := by
  intro a33 n145 n166 n181 n191 n197 n202 n203
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 6, 9} a33
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n145 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact n197 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n202 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 6, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact n203 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 6, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c485 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {0, 6, 9} → False := by
  intro a166 n33
  exact n33 (h.down {0, 2, 6, 9} {0, 6, 9} a166 (by decide) (by decide))

theorem c491 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → ¬ T {0, 6, 9} → False := by
  intro a197 n33
  exact n33 (h.down {0, 5, 6, 9} {0, 6, 9} a197 (by decide) (by decide))

theorem c494 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 3, 6, 9} → ¬ Q {0, 4, 6, 9} → ¬ Q {0, 5, 6, 9} → ¬ Q {0, 6, 8, 9} → False := by
  intro a202 n145 n166 n181 n191 n197 n203
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 7, 9} {0, 6, 9} a202 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n145 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 6, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact n166 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 6, 9} = {0, 2, 6, 9} by decide)) hS)
  · exact n181 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 6, 9} = {0, 3, 6, 9} by decide)) hS)
  · exact n191 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 6, 9} = {0, 4, 6, 9} by decide)) hS)
  · exact n197 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 6, 9} = {0, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n203 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 6, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c495 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {0, 6, 9} → False := by
  intro a203 n33
  exact n33 (h.down {0, 6, 8, 9} {0, 6, 9} a203 (by decide) (by decide))

theorem c497 (h : TenSystem T Q) :
    T {0, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 7, 8, 9} → False := by
  intro a34 n146 n167 n182 n192 n198 n201 n204
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 7, 8} a34
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 7, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 7, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n201 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 7, 8} = {0, 7, 8, 9} by decide)) hS)

theorem c501 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 7, 8, 9} → False := by
  intro a167 n146 n182 n192 n198 n201 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 2, 7, 8} {0, 7, 8} a167 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n182 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 7, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n201 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 7, 8} = {0, 7, 8, 9} by decide)) hS)

theorem c503 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 7, 8, 9} → False := by
  intro a182 n146 n167 n192 n198 n201 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 3, 7, 8} {0, 7, 8} a182 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 7, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n192 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 7, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact n201 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 7, 8} = {0, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 7, 8} = {0, 7, 8, 9} by decide)) hS)

theorem c506 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {0, 7, 8} → False := by
  intro a198 n34
  exact n34 (h.down {0, 5, 7, 8} {0, 7, 8} a198 (by decide) (by decide))

theorem c509 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 2, 7, 8} → ¬ Q {0, 3, 7, 8} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 7, 8, 9} → False := by
  intro a201 n146 n167 n182 n192 n198 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 7, 8} {0, 7, 8} a201 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n146 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact n167 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 7, 8} = {0, 2, 7, 8} by decide)) hS)
  · exact n182 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 7, 8} = {0, 3, 7, 8} by decide)) hS)
  · exact n192 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 7, 8} = {0, 4, 7, 8} by decide)) hS)
  · exact n198 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 8} = {0, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (9 : Labels) {0, 7, 8} = {0, 7, 8, 9} by decide)) hS)

theorem c517 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {0, 7, 9} → False := by
  intro a183 n35
  exact n35 (h.down {0, 3, 7, 9} {0, 7, 9} a183 (by decide) (by decide))

theorem c519 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {0, 7, 9} → False := by
  intro a193 n35
  exact n35 (h.down {0, 4, 7, 9} {0, 7, 9} a193 (by decide) (by decide))

theorem c520 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 5, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {0, 7, 8, 9} → False := by
  intro a193 n147 n168 n183 n199 n202 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 4, 7, 9} {0, 7, 9} a193 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n147 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 7, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n199 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 7, 9} = {0, 5, 7, 9} by decide)) hS)
  · exact n202 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 7, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 7, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c522 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {0, 2, 7, 9} → ¬ Q {0, 3, 7, 9} → ¬ Q {0, 4, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {0, 7, 8, 9} → False := by
  intro a199 n147 n168 n183 n193 n202 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 5, 7, 9} {0, 7, 9} a199 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n147 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact n168 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 7, 9} = {0, 2, 7, 9} by decide)) hS)
  · exact n183 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 7, 9} = {0, 3, 7, 9} by decide)) hS)
  · exact n193 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 7, 9} = {0, 4, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n202 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 7, 9} = {0, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (8 : Labels) {0, 7, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c523 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ T {0, 7, 9} → False := by
  intro a202 n35
  exact n35 (h.down {0, 6, 7, 9} {0, 7, 9} a202 (by decide) (by decide))

theorem c525 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → ¬ T {0, 7, 9} → False := by
  intro a204 n35
  exact n35 (h.down {0, 7, 8, 9} {0, 7, 9} a204 (by decide) (by decide))

theorem c527 (h : TenSystem T Q) :
    T {0, 8, 9} → ¬ Q {0, 1, 8, 9} → ¬ Q {0, 2, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {0, 7, 8, 9} → False := by
  intro a36 n148 n169 n184 n194 n200 n203 n204
  obtain ⟨S, hS, hUS⟩ := h.pure {0, 8, 9} a36
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n148 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 8, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact n169 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 8, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n194 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 8, 9} = {0, 4, 8, 9} by decide)) hS)
  · exact n200 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact n203 (Eq.mp (congrArg Q (show insert (6 : Labels) {0, 8, 9} = {0, 6, 8, 9} by decide)) hS)
  · exact n204 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c532 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {0, 8, 9} → False := by
  intro a184 n36
  exact n36 (h.down {0, 3, 8, 9} {0, 8, 9} a184 (by decide) (by decide))

theorem c534 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {0, 8, 9} → False := by
  intro a194 n36
  exact n36 (h.down {0, 4, 8, 9} {0, 8, 9} a194 (by decide) (by decide))

theorem c536 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {0, 8, 9} → False := by
  intro a200 n36
  exact n36 (h.down {0, 5, 8, 9} {0, 8, 9} a200 (by decide) (by decide))

theorem c538 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {0, 8, 9} → False := by
  intro a203 n36
  exact n36 (h.down {0, 6, 8, 9} {0, 8, 9} a203 (by decide) (by decide))

theorem c539 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ Q {0, 1, 8, 9} → ¬ Q {0, 2, 8, 9} → ¬ Q {0, 3, 8, 9} → ¬ Q {0, 4, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {0, 7, 8, 9} → False := by
  intro a203 n148 n169 n184 n194 n200 n204
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 6, 8, 9} {0, 8, 9} a203 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {0, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hv (by decide)
  · exact n148 (Eq.mp (congrArg Q (show insert (1 : Labels) {0, 8, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact n169 (Eq.mp (congrArg Q (show insert (2 : Labels) {0, 8, 9} = {0, 2, 8, 9} by decide)) hS)
  · exact n184 (Eq.mp (congrArg Q (show insert (3 : Labels) {0, 8, 9} = {0, 3, 8, 9} by decide)) hS)
  · exact n194 (Eq.mp (congrArg Q (show insert (4 : Labels) {0, 8, 9} = {0, 4, 8, 9} by decide)) hS)
  · exact n200 (Eq.mp (congrArg Q (show insert (5 : Labels) {0, 8, 9} = {0, 5, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n204 (Eq.mp (congrArg Q (show insert (7 : Labels) {0, 8, 9} = {0, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c540 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → ¬ T {0, 8, 9} → False := by
  intro a204 n36
  exact n36 (h.down {0, 7, 8, 9} {0, 8, 9} a204 (by decide) (by decide))

theorem c543 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {1, 2, 3} → False := by
  intro a121 n37
  exact n37 (h.down {0, 1, 2, 3} {1, 2, 3} a121 (by decide) (by decide))

theorem c544 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ Q {1, 2, 3, 4} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 2, 3, 6} → ¬ Q {1, 2, 3, 7} → ¬ Q {1, 2, 3, 8} → ¬ Q {1, 2, 3, 9} → False := by
  intro a121 n205 n206 n207 n208 n209 n210
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 2, 3} {1, 2, 3} a121 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 3} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n205 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 3} = {1, 2, 3, 4} by decide)) hS)
  · exact n206 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 3} = {1, 2, 3, 5} by decide)) hS)
  · exact n207 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 3} = {1, 2, 3, 6} by decide)) hS)
  · exact n208 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 3} = {1, 2, 3, 7} by decide)) hS)
  · exact n209 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 3} = {1, 2, 3, 8} by decide)) hS)
  · exact n210 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 3} = {1, 2, 3, 9} by decide)) hS)

theorem c557 (h : TenSystem T Q) :
    T {1, 2, 4} → ¬ Q {0, 1, 2, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 2, 4, 6} → ¬ Q {1, 2, 4, 7} → ¬ Q {1, 2, 4, 8} → ¬ Q {1, 2, 4, 9} → False := by
  intro a38 n122 n205 n211 n212 n213 n214 n215
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 4} a38
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n122 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 4} = {0, 1, 2, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n205 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 4} = {1, 2, 4, 5} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 4} = {1, 2, 4, 6} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 4} = {1, 2, 4, 7} by decide)) hS)
  · exact n214 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 4} = {1, 2, 4, 8} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 4} = {1, 2, 4, 9} by decide)) hS)

theorem c558 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {1, 2, 4} → False := by
  intro a122 n38
  exact n38 (h.down {0, 1, 2, 4} {1, 2, 4} a122 (by decide) (by decide))

theorem c560 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {1, 2, 4} → False := by
  intro a205 n38
  exact n38 (h.down {1, 2, 3, 4} {1, 2, 4} a205 (by decide) (by decide))

theorem c562 (h : TenSystem T Q) :
    Q {1, 2, 4, 5} → ¬ T {1, 2, 4} → False := by
  intro a211 n38
  exact n38 (h.down {1, 2, 4, 5} {1, 2, 4} a211 (by decide) (by decide))

theorem c564 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → ¬ T {1, 2, 4} → False := by
  intro a212 n38
  exact n38 (h.down {1, 2, 4, 6} {1, 2, 4} a212 (by decide) (by decide))

theorem c565 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → ¬ Q {0, 1, 2, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 2, 4, 7} → ¬ Q {1, 2, 4, 8} → ¬ Q {1, 2, 4, 9} → False := by
  intro a212 n122 n205 n211 n213 n214 n215
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 4, 6} {1, 2, 4} a212 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n122 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 4} = {0, 1, 2, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n205 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 2, 4} = {1, 2, 4, 5} by decide)) hS)
  · exact hne (by decide)
  · exact n213 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 4} = {1, 2, 4, 7} by decide)) hS)
  · exact n214 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 4} = {1, 2, 4, 8} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 4} = {1, 2, 4, 9} by decide)) hS)

theorem c566 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → ¬ T {1, 2, 4} → False := by
  intro a213 n38
  exact n38 (h.down {1, 2, 4, 7} {1, 2, 4} a213 (by decide) (by decide))

theorem c570 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → ¬ T {1, 2, 4} → False := by
  intro a215 n38
  exact n38 (h.down {1, 2, 4, 9} {1, 2, 4} a215 (by decide) (by decide))

theorem c572 (h : TenSystem T Q) :
    T {1, 2, 5} → ¬ Q {0, 1, 2, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 2, 5, 9} → False := by
  intro a39 n123 n206 n211 n216 n217 n218 n219
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 2, 5} a39
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n123 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 5} = {0, 1, 2, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n206 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 2, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact n211 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 5} = {1, 2, 5, 6} by decide)) hS)
  · exact n217 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 5} = {1, 2, 5, 7} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 5} = {1, 2, 5, 8} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 5} = {1, 2, 5, 9} by decide)) hS)

theorem c573 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {1, 2, 5} → False := by
  intro a123 n39
  exact n39 (h.down {0, 1, 2, 5} {1, 2, 5} a123 (by decide) (by decide))

theorem c575 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {1, 2, 5} → False := by
  intro a206 n39
  exact n39 (h.down {1, 2, 3, 5} {1, 2, 5} a206 (by decide) (by decide))

theorem c576 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ Q {0, 1, 2, 5} → ¬ Q {1, 2, 4, 5} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 2, 5, 9} → False := by
  intro a206 n123 n211 n216 n217 n218 n219
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 3, 5} {1, 2, 5} a206 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 2, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n123 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 2, 5} = {0, 1, 2, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n211 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 2, 5} = {1, 2, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n216 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 2, 5} = {1, 2, 5, 6} by decide)) hS)
  · exact n217 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 2, 5} = {1, 2, 5, 7} by decide)) hS)
  · exact n218 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 2, 5} = {1, 2, 5, 8} by decide)) hS)
  · exact n219 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 2, 5} = {1, 2, 5, 9} by decide)) hS)

theorem c579 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ T {1, 2, 5} → False := by
  intro a216 n39
  exact n39 (h.down {1, 2, 5, 6} {1, 2, 5} a216 (by decide) (by decide))

theorem c581 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {1, 2, 5} → False := by
  intro a217 n39
  exact n39 (h.down {1, 2, 5, 7} {1, 2, 5} a217 (by decide) (by decide))

theorem c583 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → ¬ T {1, 2, 5} → False := by
  intro a218 n39
  exact n39 (h.down {1, 2, 5, 8} {1, 2, 5} a218 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
