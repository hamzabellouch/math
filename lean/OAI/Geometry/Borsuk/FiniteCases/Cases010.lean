import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c838 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {1, 5, 7} → False := by
  intro a254 n56
  exact n56 (h.down {1, 5, 7, 8} {1, 5, 7} a254 (by decide) (by decide))

theorem c839 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 9} → False := by
  intro a254 n140 n217 n232 n242 n251 n255
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 7, 8} {1, 5, 7} a254 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n140 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n217 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n255 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 7} = {1, 5, 7, 9} by decide)) hS)

theorem c841 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ Q {0, 1, 5, 7} → ¬ Q {1, 2, 5, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 4, 5, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 5, 7, 8} → False := by
  intro a255 n140 n217 n232 n242 n251 n254
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 7, 9} {1, 5, 7} a255 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n140 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 7} = {0, 1, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n217 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 7} = {1, 2, 5, 7} by decide)) hS)
  · exact n232 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 7} = {1, 3, 5, 7} by decide)) hS)
  · exact n242 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 7} = {1, 4, 5, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n254 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 7} = {1, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c842 (h : TenSystem T Q) :
    T {1, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a57 n141 n218 n233 n243 n252 n254 n256
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 5, 8} a57
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n141 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n218 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c843 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {1, 5, 8} → False := by
  intro a141 n57
  exact n57 (h.down {0, 1, 5, 8} {1, 5, 8} a141 (by decide) (by decide))

theorem c844 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a141 n218 n233 n243 n252 n254 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 5, 8} {1, 5, 8} a141 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n218 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c846 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a218 n141 n233 n243 n252 n254 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 5, 8} {1, 5, 8} a218 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n141 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c847 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {1, 5, 8} → False := by
  intro a233 n57
  exact n57 (h.down {1, 3, 5, 8} {1, 5, 8} a233 (by decide) (by decide))

theorem c850 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a243 n141 n218 n233 n252 n254 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 8} {1, 5, 8} a243 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n141 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n218 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c851 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {1, 5, 8} → False := by
  intro a252 n57
  exact n57 (h.down {1, 5, 6, 8} {1, 5, 8} a252 (by decide) (by decide))

theorem c853 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {1, 5, 8} → False := by
  intro a254 n57
  exact n57 (h.down {1, 5, 7, 8} {1, 5, 8} a254 (by decide) (by decide))

theorem c854 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ Q {0, 1, 5, 8} → ¬ Q {1, 2, 5, 8} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 4, 5, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 5, 8, 9} → False := by
  intro a254 n141 n218 n233 n243 n252 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 7, 8} {1, 5, 8} a254 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n141 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 8} = {0, 1, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n218 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 8} = {1, 2, 5, 8} by decide)) hS)
  · exact n233 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 8} = {1, 3, 5, 8} by decide)) hS)
  · exact n243 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 8} = {1, 4, 5, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n252 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 5, 8} = {1, 5, 8, 9} by decide)) hS)

theorem c855 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {1, 5, 8} → False := by
  intro a256 n57
  exact n57 (h.down {1, 5, 8, 9} {1, 5, 8} a256 (by decide) (by decide))

theorem c857 (h : TenSystem T Q) :
    T {1, 5, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 4, 5, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 5, 8, 9} → False := by
  intro a58 n142 n219 n234 n244 n253 n255 n256
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 5, 9} a58
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n142 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n219 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n244 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 9} = {1, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n253 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c859 (h : TenSystem T Q) :
    Q {0, 1, 5, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 4, 5, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 5, 8, 9} → False := by
  intro a142 n219 n234 n244 n253 n255 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 5, 9} {1, 5, 9} a142 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n219 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact n244 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 5, 9} = {1, 4, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n253 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c860 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {1, 5, 9} → False := by
  intro a219 n58
  exact n58 (h.down {1, 2, 5, 9} {1, 5, 9} a219 (by decide) (by decide))

theorem c862 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {1, 5, 9} → False := by
  intro a234 n58
  exact n58 (h.down {1, 3, 5, 9} {1, 5, 9} a234 (by decide) (by decide))

theorem c865 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → ¬ Q {0, 1, 5, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 3, 5, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 5, 8, 9} → False := by
  intro a244 n142 n219 n234 n253 n255 n256
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 5, 9} {1, 5, 9} a244 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 5, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n142 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 5, 9} = {0, 1, 5, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n219 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 5, 9} = {1, 2, 5, 9} by decide)) hS)
  · exact n234 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 5, 9} = {1, 3, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n253 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 5, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 5, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 5, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c866 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ T {1, 5, 9} → False := by
  intro a253 n58
  exact n58 (h.down {1, 5, 6, 9} {1, 5, 9} a253 (by decide) (by decide))

theorem c868 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {1, 5, 9} → False := by
  intro a255 n58
  exact n58 (h.down {1, 5, 7, 9} {1, 5, 9} a255 (by decide) (by decide))

theorem c870 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {1, 5, 9} → False := by
  intro a256 n58
  exact n58 (h.down {1, 5, 8, 9} {1, 5, 9} a256 (by decide) (by decide))

theorem c879 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {1, 6, 7} → False := by
  intro a245 n59
  exact n59 (h.down {1, 4, 6, 7} {1, 6, 7} a245 (by decide) (by decide))

theorem c880 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ Q {0, 1, 6, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 6, 7, 8} → ¬ Q {1, 6, 7, 9} → False := by
  intro a245 n143 n220 n235 n251 n257 n258
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 7} {1, 6, 7} a245 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n143 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact n251 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 6, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n257 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 6, 7} = {1, 6, 7, 8} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 6, 7} = {1, 6, 7, 9} by decide)) hS)

theorem c881 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {1, 6, 7} → False := by
  intro a251 n59
  exact n59 (h.down {1, 5, 6, 7} {1, 6, 7} a251 (by decide) (by decide))

theorem c882 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ Q {0, 1, 6, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {1, 6, 7, 8} → ¬ Q {1, 6, 7, 9} → False := by
  intro a251 n143 n220 n235 n245 n257 n258
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 6, 7} {1, 6, 7} a251 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n143 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n245 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n257 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 6, 7} = {1, 6, 7, 8} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 6, 7} = {1, 6, 7, 9} by decide)) hS)

theorem c883 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {1, 6, 7} → False := by
  intro a257 n59
  exact n59 (h.down {1, 6, 7, 8} {1, 6, 7} a257 (by decide) (by decide))

theorem c885 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {1, 6, 7} → False := by
  intro a258 n59
  exact n59 (h.down {1, 6, 7, 9} {1, 6, 7} a258 (by decide) (by decide))

theorem c886 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ Q {0, 1, 6, 7} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {1, 6, 7, 8} → False := by
  intro a258 n143 n220 n235 n245 n251 n257
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 7, 9} {1, 6, 7} a258 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n143 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 7} = {0, 1, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n220 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 7} = {1, 2, 6, 7} by decide)) hS)
  · exact n235 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 7} = {1, 3, 6, 7} by decide)) hS)
  · exact n245 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 7} = {1, 4, 6, 7} by decide)) hS)
  · exact n251 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 6, 7} = {1, 5, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n257 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 6, 7} = {1, 6, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c887 (h : TenSystem T Q) :
    T {1, 6, 8} → ¬ Q {0, 1, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {1, 6, 8, 9} → False := by
  intro a60 n144 n221 n236 n246 n252 n257 n259
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 6, 8} a60
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n144 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 8} = {0, 1, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n221 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n257 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 6, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n259 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 6, 8} = {1, 6, 8, 9} by decide)) hS)

theorem c889 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {1, 6, 8, 9} → False := by
  intro a144 n221 n236 n246 n252 n257 n259
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 6, 8} {1, 6, 8} a144 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n221 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n257 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 6, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n259 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 6, 8} = {1, 6, 8, 9} by decide)) hS)

theorem c894 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {1, 6, 8} → False := by
  intro a246 n60
  exact n60 (h.down {1, 4, 6, 8} {1, 6, 8} a246 (by decide) (by decide))

theorem c896 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {1, 6, 8} → False := by
  intro a252 n60
  exact n60 (h.down {1, 5, 6, 8} {1, 6, 8} a252 (by decide) (by decide))

theorem c901 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ Q {0, 1, 6, 8} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 3, 6, 8} → ¬ Q {1, 4, 6, 8} → ¬ Q {1, 5, 6, 8} → ¬ Q {1, 6, 7, 8} → False := by
  intro a259 n144 n221 n236 n246 n252 n257
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 8, 9} {1, 6, 8} a259 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n144 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 8} = {0, 1, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n221 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 8} = {1, 2, 6, 8} by decide)) hS)
  · exact n236 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 8} = {1, 3, 6, 8} by decide)) hS)
  · exact n246 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 8} = {1, 4, 6, 8} by decide)) hS)
  · exact n252 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 6, 8} = {1, 5, 6, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n257 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 6, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c902 (h : TenSystem T Q) :
    T {1, 6, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {1, 6, 8, 9} → False := by
  intro a61 n145 n222 n237 n247 n253 n258 n259
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 6, 9} a61
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n145 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n222 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 9} = {1, 4, 6, 9} by decide)) hS)
  · exact n253 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 6, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n258 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 6, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 6, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c903 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → ¬ T {1, 6, 9} → False := by
  intro a145 n61
  exact n61 (h.down {0, 1, 6, 9} {1, 6, 9} a145 (by decide) (by decide))

theorem c907 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {1, 6, 9} → False := by
  intro a237 n61
  exact n61 (h.down {1, 3, 6, 9} {1, 6, 9} a237 (by decide) (by decide))

theorem c909 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ T {1, 6, 9} → False := by
  intro a247 n61
  exact n61 (h.down {1, 4, 6, 9} {1, 6, 9} a247 (by decide) (by decide))

theorem c910 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {1, 6, 8, 9} → False := by
  intro a247 n145 n222 n237 n253 n258 n259
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 6, 9} {1, 6, 9} a247 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n145 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n222 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n253 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 6, 9} = {1, 5, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n258 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 6, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 6, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c912 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {1, 6, 8, 9} → False := by
  intro a253 n145 n222 n237 n247 n258 n259
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 5, 6, 9} {1, 6, 9} a253 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 6, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n145 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 6, 9} = {0, 1, 6, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n222 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 6, 9} = {1, 2, 6, 9} by decide)) hS)
  · exact n237 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 6, 9} = {1, 3, 6, 9} by decide)) hS)
  · exact n247 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 6, 9} = {1, 4, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n258 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 6, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 6, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact hv (by decide)

end BorsukNine.FiniteObstruction

end OAI
