import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c913 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {1, 6, 9} → False := by
  intro a258 n61
  exact n61 (h.down {1, 6, 7, 9} {1, 6, 9} a258 (by decide) (by decide))

theorem c916 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ Q {0, 1, 6, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 3, 6, 9} → ¬ Q {1, 4, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {1, 6, 7, 9} → False := by
  intro a259 n145 n222 n237 n247 n253 n258
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 8, 9} {1, 6, 9} a259 (by decide) (by decide)
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
  · exact hne (by decide)
  · exact hv (by decide)

theorem c917 (h : TenSystem T Q) :
    T {1, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {1, 2, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 4, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 6, 7, 8} → ¬ Q {1, 7, 8, 9} → False := by
  intro a62 n146 n223 n238 n248 n254 n257 n260
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 7, 8} a62
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n146 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n223 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 8} = {1, 2, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n248 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 8} = {1, 4, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact n257 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 7, 8} = {1, 7, 8, 9} by decide)) hS)

theorem c922 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {1, 7, 8} → False := by
  intro a238 n62
  exact n62 (h.down {1, 3, 7, 8} {1, 7, 8} a238 (by decide) (by decide))

theorem c926 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {1, 7, 8} → False := by
  intro a254 n62
  exact n62 (h.down {1, 5, 7, 8} {1, 7, 8} a254 (by decide) (by decide))

theorem c928 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {1, 7, 8} → False := by
  intro a257 n62
  exact n62 (h.down {1, 6, 7, 8} {1, 7, 8} a257 (by decide) (by decide))

theorem c929 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ Q {0, 1, 7, 8} → ¬ Q {1, 2, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 4, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 7, 8, 9} → False := by
  intro a257 n146 n223 n238 n248 n254 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 7, 8} {1, 7, 8} a257 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n146 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n223 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 8} = {1, 2, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n248 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 8} = {1, 4, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (9 : Labels) {1, 7, 8} = {1, 7, 8, 9} by decide)) hS)

theorem c931 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → ¬ Q {0, 1, 7, 8} → ¬ Q {1, 2, 7, 8} → ¬ Q {1, 3, 7, 8} → ¬ Q {1, 4, 7, 8} → ¬ Q {1, 5, 7, 8} → ¬ Q {1, 6, 7, 8} → False := by
  intro a260 n146 n223 n238 n248 n254 n257
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 7, 8, 9} {1, 7, 8} a260 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n146 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 8} = {0, 1, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n223 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 8} = {1, 2, 7, 8} by decide)) hS)
  · exact n238 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 8} = {1, 3, 7, 8} by decide)) hS)
  · exact n248 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 8} = {1, 4, 7, 8} by decide)) hS)
  · exact n254 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 8} = {1, 5, 7, 8} by decide)) hS)
  · exact n257 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 8} = {1, 6, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c932 (h : TenSystem T Q) :
    T {1, 7, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a63 n147 n224 n239 n249 n255 n258 n260
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 7, 9} a63
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n147 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n224 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 7, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c934 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a147 n224 n239 n249 n255 n258 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 7, 9} {1, 7, 9} a147 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n224 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 7, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c937 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {1, 7, 9} → False := by
  intro a239 n63
  exact n63 (h.down {1, 3, 7, 9} {1, 7, 9} a239 (by decide) (by decide))

theorem c939 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {1, 7, 9} → False := by
  intro a249 n63
  exact n63 (h.down {1, 4, 7, 9} {1, 7, 9} a249 (by decide) (by decide))

theorem c940 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 6, 7, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a249 n147 n224 n239 n255 n258 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 7, 9} {1, 7, 9} a249 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n147 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n224 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n255 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 7, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c941 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {1, 7, 9} → False := by
  intro a255 n63
  exact n63 (h.down {1, 5, 7, 9} {1, 7, 9} a255 (by decide) (by decide))

theorem c943 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {1, 7, 9} → False := by
  intro a258 n63
  exact n63 (h.down {1, 6, 7, 9} {1, 7, 9} a258 (by decide) (by decide))

theorem c944 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a258 n147 n224 n239 n249 n255 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 6, 7, 9} {1, 7, 9} a258 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n147 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n224 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n260 (Eq.mp (congrArg Q (show insert (8 : Labels) {1, 7, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c946 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → ¬ Q {0, 1, 7, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {1, 5, 7, 9} → ¬ Q {1, 6, 7, 9} → False := by
  intro a260 n147 n224 n239 n249 n255 n258
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 7, 8, 9} {1, 7, 9} a260 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 7, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n147 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 7, 9} = {0, 1, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n224 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 7, 9} = {1, 2, 7, 9} by decide)) hS)
  · exact n239 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 7, 9} = {1, 3, 7, 9} by decide)) hS)
  · exact n249 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 7, 9} = {1, 4, 7, 9} by decide)) hS)
  · exact n255 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 7, 9} = {1, 5, 7, 9} by decide)) hS)
  · exact n258 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 7, 9} = {1, 6, 7, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)

theorem c947 (h : TenSystem T Q) :
    T {1, 8, 9} → ¬ Q {0, 1, 8, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 4, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a64 n148 n225 n240 n250 n256 n259 n260
  obtain ⟨S, hS, hUS⟩ := h.pure {1, 8, 9} a64
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n148 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 8, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n225 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 8, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n250 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 8, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n260 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 8, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c949 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 4, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a148 n225 n240 n250 n256 n259 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {0, 1, 8, 9} {1, 8, 9} a148 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n225 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 8, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact n250 (Eq.mp (congrArg Q (show insert (4 : Labels) {1, 8, 9} = {1, 4, 8, 9} by decide)) hS)
  · exact n256 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n260 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 8, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c950 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a225 n64
  exact n64 (h.down {1, 2, 8, 9} {1, 8, 9} a225 (by decide) (by decide))

theorem c952 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a240 n64
  exact n64 (h.down {1, 3, 8, 9} {1, 8, 9} a240 (by decide) (by decide))

theorem c954 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a250 n64
  exact n64 (h.down {1, 4, 8, 9} {1, 8, 9} a250 (by decide) (by decide))

theorem c955 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ Q {0, 1, 8, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {1, 7, 8, 9} → False := by
  intro a250 n148 n225 n240 n256 n259 n260
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 4, 8, 9} {1, 8, 9} a250 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {1, 8, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n148 (Eq.mp (congrArg Q (show insert (0 : Labels) {1, 8, 9} = {0, 1, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n225 (Eq.mp (congrArg Q (show insert (2 : Labels) {1, 8, 9} = {1, 2, 8, 9} by decide)) hS)
  · exact n240 (Eq.mp (congrArg Q (show insert (3 : Labels) {1, 8, 9} = {1, 3, 8, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n256 (Eq.mp (congrArg Q (show insert (5 : Labels) {1, 8, 9} = {1, 5, 8, 9} by decide)) hS)
  · exact n259 (Eq.mp (congrArg Q (show insert (6 : Labels) {1, 8, 9} = {1, 6, 8, 9} by decide)) hS)
  · exact n260 (Eq.mp (congrArg Q (show insert (7 : Labels) {1, 8, 9} = {1, 7, 8, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)

theorem c956 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a256 n64
  exact n64 (h.down {1, 5, 8, 9} {1, 8, 9} a256 (by decide) (by decide))

theorem c958 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {1, 8, 9} → False := by
  intro a259 n64
  exact n64 (h.down {1, 6, 8, 9} {1, 8, 9} a259 (by decide) (by decide))

theorem c962 (h : TenSystem T Q) :
    T {2, 3, 4} → ¬ Q {0, 2, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {2, 3, 4, 5} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 4, 9} → False := by
  intro a65 n149 n205 n261 n262 n263 n264 n265
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 3, 4} a65
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n149 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact n205 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 4} = {2, 3, 4, 5} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 4} = {2, 3, 4, 6} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 4} = {2, 3, 4, 7} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 4} = {2, 3, 4, 8} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 4} = {2, 3, 4, 9} by decide)) hS)

theorem c963 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {2, 3, 4} → False := by
  intro a149 n65
  exact n65 (h.down {0, 2, 3, 4} {2, 3, 4} a149 (by decide) (by decide))

theorem c968 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → ¬ Q {0, 2, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 4, 9} → False := by
  intro a261 n149 n205 n262 n263 n264 n265
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 5} {2, 3, 4} a261 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n149 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact n205 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 4} = {2, 3, 4, 6} by decide)) hS)
  · exact n263 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 4} = {2, 3, 4, 7} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 4} = {2, 3, 4, 8} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 4} = {2, 3, 4, 9} by decide)) hS)

theorem c969 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {2, 3, 4} → False := by
  intro a262 n65
  exact n65 (h.down {2, 3, 4, 6} {2, 3, 4} a262 (by decide) (by decide))

theorem c970 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ Q {0, 2, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {2, 3, 4, 5} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 4, 9} → False := by
  intro a262 n149 n205 n261 n263 n264 n265
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 6} {2, 3, 4} a262 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n149 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact n205 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 4} = {2, 3, 4, 5} by decide)) hS)
  · exact hne (by decide)
  · exact n263 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 4} = {2, 3, 4, 7} by decide)) hS)
  · exact n264 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 4} = {2, 3, 4, 8} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 4} = {2, 3, 4, 9} by decide)) hS)

theorem c971 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {2, 3, 4} → False := by
  intro a263 n65
  exact n65 (h.down {2, 3, 4, 7} {2, 3, 4} a263 (by decide) (by decide))

theorem c972 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ Q {0, 2, 3, 4} → ¬ Q {1, 2, 3, 4} → ¬ Q {2, 3, 4, 5} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 4, 9} → False := by
  intro a263 n149 n205 n261 n262 n264 n265
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 7} {2, 3, 4} a263 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 4} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n149 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 4} = {0, 2, 3, 4} by decide)) hS)
  · exact n205 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 4} = {1, 2, 3, 4} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 4} = {2, 3, 4, 5} by decide)) hS)
  · exact n262 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 4} = {2, 3, 4, 6} by decide)) hS)
  · exact hne (by decide)
  · exact n264 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 4} = {2, 3, 4, 8} by decide)) hS)
  · exact n265 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 4} = {2, 3, 4, 9} by decide)) hS)

theorem c975 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {2, 3, 4} → False := by
  intro a265 n65
  exact n65 (h.down {2, 3, 4, 9} {2, 3, 4} a265 (by decide) (by decide))

theorem c977 (h : TenSystem T Q) :
    T {2, 3, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {2, 3, 4, 5} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 5, 7} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 3, 5, 9} → False := by
  intro a66 n150 n206 n261 n266 n267 n268 n269
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 3, 5} a66
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n150 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n206 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 5} = {2, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact n266 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 5} = {2, 3, 5, 6} by decide)) hS)
  · exact n267 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 5} = {2, 3, 5, 7} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 5} = {2, 3, 5, 8} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 5} = {2, 3, 5, 9} by decide)) hS)

theorem c983 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → ¬ Q {0, 2, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 5, 7} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 3, 5, 9} → False := by
  intro a261 n150 n206 n266 n267 n268 n269
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 5} {2, 3, 5} a261 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n150 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n206 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n266 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 5} = {2, 3, 5, 6} by decide)) hS)
  · exact n267 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 5} = {2, 3, 5, 7} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 5} = {2, 3, 5, 8} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 5} = {2, 3, 5, 9} by decide)) hS)

theorem c985 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ Q {0, 2, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {2, 3, 4, 5} → ¬ Q {2, 3, 5, 7} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 3, 5, 9} → False := by
  intro a266 n150 n206 n261 n267 n268 n269
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 5, 6} {2, 3, 5} a266 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 5} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n150 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 5} = {0, 2, 3, 5} by decide)) hS)
  · exact n206 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 5} = {1, 2, 3, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n261 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 5} = {2, 3, 4, 5} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n267 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 5} = {2, 3, 5, 7} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 5} = {2, 3, 5, 8} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 5} = {2, 3, 5, 9} by decide)) hS)

theorem c988 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {2, 3, 5} → False := by
  intro a268 n66
  exact n66 (h.down {2, 3, 5, 8} {2, 3, 5} a268 (by decide) (by decide))

theorem c990 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {2, 3, 5} → False := by
  intro a269 n66
  exact n66 (h.down {2, 3, 5, 9} {2, 3, 5} a269 (by decide) (by decide))

theorem c992 (h : TenSystem T Q) :
    T {2, 3, 6} → ¬ Q {0, 2, 3, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 3, 6, 9} → False := by
  intro a67 n151 n207 n262 n266 n270 n271 n272
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 3, 6} a67
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n151 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 6} = {0, 2, 3, 6} by decide)) hS)
  · exact n207 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 6} = {1, 2, 3, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n270 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 6} = {2, 3, 6, 7} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 6} = {2, 3, 6, 8} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 6} = {2, 3, 6, 9} by decide)) hS)

end BorsukNine.FiniteObstruction

end OAI
