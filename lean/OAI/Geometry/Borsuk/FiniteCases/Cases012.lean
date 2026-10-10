import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c993 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {2, 3, 6} → False := by
  intro a151 n67
  exact n67 (h.down {0, 2, 3, 6} {2, 3, 6} a151 (by decide) (by decide))

theorem c995 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {2, 3, 6} → False := by
  intro a207 n67
  exact n67 (h.down {1, 2, 3, 6} {2, 3, 6} a207 (by decide) (by decide))

theorem c996 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ Q {0, 2, 3, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 3, 6, 9} → False := by
  intro a207 n151 n262 n266 n270 n271 n272
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {1, 2, 3, 6} {2, 3, 6} a207 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n151 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 6} = {0, 2, 3, 6} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact n266 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 6} = {2, 3, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n270 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 6} = {2, 3, 6, 7} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 6} = {2, 3, 6, 8} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 6} = {2, 3, 6, 9} by decide)) hS)

theorem c997 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {2, 3, 6} → False := by
  intro a262 n67
  exact n67 (h.down {2, 3, 4, 6} {2, 3, 6} a262 (by decide) (by decide))

theorem c999 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {2, 3, 6} → False := by
  intro a266 n67
  exact n67 (h.down {2, 3, 5, 6} {2, 3, 6} a266 (by decide) (by decide))

theorem c1001 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {2, 3, 6} → False := by
  intro a270 n67
  exact n67 (h.down {2, 3, 6, 7} {2, 3, 6} a270 (by decide) (by decide))

theorem c1006 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → ¬ Q {0, 2, 3, 6} → ¬ Q {1, 2, 3, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 3, 5, 6} → ¬ Q {2, 3, 6, 7} → ¬ Q {2, 3, 6, 8} → False := by
  intro a272 n151 n207 n262 n266 n270 n271
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 6, 9} {2, 3, 6} a272 (by decide) (by decide)
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
  · exact hne (by decide)

theorem c1008 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {2, 3, 7} → False := by
  intro a152 n68
  exact n68 (h.down {0, 2, 3, 7} {2, 3, 7} a152 (by decide) (by decide))

theorem c1010 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {2, 3, 7} → False := by
  intro a208 n68
  exact n68 (h.down {1, 2, 3, 7} {2, 3, 7} a208 (by decide) (by decide))

theorem c1012 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {2, 3, 7} → False := by
  intro a263 n68
  exact n68 (h.down {2, 3, 4, 7} {2, 3, 7} a263 (by decide) (by decide))

theorem c1016 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {2, 3, 7} → False := by
  intro a270 n68
  exact n68 (h.down {2, 3, 6, 7} {2, 3, 7} a270 (by decide) (by decide))

theorem c1020 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ T {2, 3, 7} → False := by
  intro a274 n68
  exact n68 (h.down {2, 3, 7, 9} {2, 3, 7} a274 (by decide) (by decide))

theorem c1022 (h : TenSystem T Q) :
    T {2, 3, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {1, 2, 3, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 5, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {2, 3, 8, 9} → False := by
  intro a69 n153 n209 n264 n268 n271 n273 n275
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 3, 8} a69
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n153 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n209 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 8} = {1, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n264 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact n268 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 8} = {2, 3, 5, 8} by decide)) hS)
  · exact n271 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n275 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 8} = {2, 3, 8, 9} by decide)) hS)

theorem c1025 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {2, 3, 8} → False := by
  intro a209 n69
  exact n69 (h.down {1, 2, 3, 8} {2, 3, 8} a209 (by decide) (by decide))

theorem c1029 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {2, 3, 8} → False := by
  intro a268 n69
  exact n69 (h.down {2, 3, 5, 8} {2, 3, 8} a268 (by decide) (by decide))

theorem c1030 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ Q {0, 2, 3, 8} → ¬ Q {1, 2, 3, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {2, 3, 7, 8} → ¬ Q {2, 3, 8, 9} → False := by
  intro a268 n153 n209 n264 n271 n273 n275
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 5, 8} {2, 3, 8} a268 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n153 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 8} = {0, 2, 3, 8} by decide)) hS)
  · exact n209 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 8} = {1, 2, 3, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n264 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hne (by decide)
  · exact n271 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 8} = {2, 3, 6, 8} by decide)) hS)
  · exact n273 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 8} = {2, 3, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n275 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 3, 8} = {2, 3, 8, 9} by decide)) hS)

theorem c1035 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {2, 3, 8} → False := by
  intro a275 n69
  exact n69 (h.down {2, 3, 8, 9} {2, 3, 8} a275 (by decide) (by decide))

theorem c1037 (h : TenSystem T Q) :
    T {2, 3, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {2, 3, 8, 9} → False := by
  intro a70 n154 n210 n265 n269 n272 n274 n275
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 3, 9} a70
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n154 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n210 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n265 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1038 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a154 n70
  exact n70 (h.down {0, 2, 3, 9} {2, 3, 9} a154 (by decide) (by decide))

theorem c1040 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {2, 3, 9} → False := by
  intro a210 n70
  exact n70 (h.down {1, 2, 3, 9} {2, 3, 9} a210 (by decide) (by decide))

theorem c1042 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {2, 3, 9} → False := by
  intro a265 n70
  exact n70 (h.down {2, 3, 4, 9} {2, 3, 9} a265 (by decide) (by decide))

theorem c1043 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {2, 3, 8, 9} → False := by
  intro a265 n154 n210 n269 n272 n274 n275
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 9} {2, 3, 9} a265 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n154 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n210 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n269 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact n274 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1044 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {2, 3, 9} → False := by
  intro a269 n70
  exact n70 (h.down {2, 3, 5, 9} {2, 3, 9} a269 (by decide) (by decide))

theorem c1047 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 3, 7, 9} → ¬ Q {2, 3, 8, 9} → False := by
  intro a272 n154 n210 n265 n269 n274 n275
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 6, 9} {2, 3, 9} a272 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n154 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n210 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n265 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n274 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 3, 9} = {2, 3, 7, 9} by decide)) hS)
  · exact n275 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1049 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ Q {0, 2, 3, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {2, 3, 8, 9} → False := by
  intro a274 n154 n210 n265 n269 n272 n275
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 7, 9} {2, 3, 9} a274 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 3, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n154 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 3, 9} = {0, 2, 3, 9} by decide)) hS)
  · exact n210 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 3, 9} = {1, 2, 3, 9} by decide)) hS)
  · exact hv (by decide)
  · exact hv (by decide)
  · exact n265 (Eq.mp (congrArg Q (show insert (4 : Labels) {2, 3, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact n269 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 3, 9} = {2, 3, 5, 9} by decide)) hS)
  · exact n272 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 3, 9} = {2, 3, 6, 9} by decide)) hS)
  · exact hne (by decide)
  · exact n275 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 3, 9} = {2, 3, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1050 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {2, 3, 9} → False := by
  intro a275 n70
  exact n70 (h.down {2, 3, 8, 9} {2, 3, 9} a275 (by decide) (by decide))

theorem c1053 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → ¬ T {2, 4, 5} → False := by
  intro a155 n71
  exact n71 (h.down {0, 2, 4, 5} {2, 4, 5} a155 (by decide) (by decide))

theorem c1059 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {2, 4, 5} → False := by
  intro a276 n71
  exact n71 (h.down {2, 4, 5, 6} {2, 4, 5} a276 (by decide) (by decide))

theorem c1063 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → ¬ T {2, 4, 5} → False := by
  intro a278 n71
  exact n71 (h.down {2, 4, 5, 8} {2, 4, 5} a278 (by decide) (by decide))

theorem c1067 (h : TenSystem T Q) :
    T {2, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → False := by
  intro a72 n156 n212 n262 n276 n280 n281 n282
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 4, 6} a72
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n156 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n276 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n280 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 6} = {2, 4, 6, 7} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 6} = {2, 4, 6, 8} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 6} = {2, 4, 6, 9} by decide)) hS)

theorem c1073 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ Q {0, 2, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → False := by
  intro a262 n156 n212 n276 n280 n281 n282
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 3, 4, 6} {2, 4, 6} a262 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n156 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n276 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n280 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 6} = {2, 4, 6, 7} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 6} = {2, 4, 6, 8} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 6} = {2, 4, 6, 9} by decide)) hS)

theorem c1076 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {2, 4, 6} → False := by
  intro a280 n72
  exact n72 (h.down {2, 4, 6, 7} {2, 4, 6} a280 (by decide) (by decide))

theorem c1077 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ Q {0, 2, 4, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {2, 4, 5, 6} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → False := by
  intro a280 n156 n212 n262 n276 n281 n282
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 7} {2, 4, 6} a280 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 6} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n156 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 6} = {0, 2, 4, 6} by decide)) hS)
  · exact n212 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 6} = {1, 2, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n262 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 6} = {2, 3, 4, 6} by decide)) hS)
  · exact hv (by decide)
  · exact n276 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 6} = {2, 4, 5, 6} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)
  · exact n281 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 6} = {2, 4, 6, 8} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 6} = {2, 4, 6, 9} by decide)) hS)

theorem c1078 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ T {2, 4, 6} → False := by
  intro a281 n72
  exact n72 (h.down {2, 4, 6, 8} {2, 4, 6} a281 (by decide) (by decide))

theorem c1082 (h : TenSystem T Q) :
    T {2, 4, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 4, 7, 8} → ¬ Q {2, 4, 7, 9} → False := by
  intro a73 n157 n213 n263 n277 n280 n283 n284
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 4, 7} a73
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n157 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n263 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n277 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 4, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n283 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 7} = {2, 4, 7, 8} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 7} = {2, 4, 7, 9} by decide)) hS)

theorem c1091 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {2, 4, 7} → False := by
  intro a280 n73
  exact n73 (h.down {2, 4, 6, 7} {2, 4, 7} a280 (by decide) (by decide))

theorem c1092 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ Q {0, 2, 4, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {2, 4, 7, 8} → ¬ Q {2, 4, 7, 9} → False := by
  intro a280 n157 n213 n263 n277 n283 n284
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 6, 7} {2, 4, 7} a280 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n157 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n263 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n277 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact hne (by decide)
  · exact hv (by decide)
  · exact n283 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 7} = {2, 4, 7, 8} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 7} = {2, 4, 7, 9} by decide)) hS)

theorem c1095 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {2, 4, 7} → False := by
  intro a284 n73
  exact n73 (h.down {2, 4, 7, 9} {2, 4, 7} a284 (by decide) (by decide))

theorem c1096 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ Q {0, 2, 4, 7} → ¬ Q {1, 2, 4, 7} → ¬ Q {2, 3, 4, 7} → ¬ Q {2, 4, 5, 7} → ¬ Q {2, 4, 6, 7} → ¬ Q {2, 4, 7, 8} → False := by
  intro a284 n157 n213 n263 n277 n280 n283
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 7, 9} {2, 4, 7} a284 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 7} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n157 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 7} = {0, 2, 4, 7} by decide)) hS)
  · exact n213 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 7} = {1, 2, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n263 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 7} = {2, 3, 4, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n277 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 7} = {2, 4, 5, 7} by decide)) hS)
  · exact n280 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 4, 7} = {2, 4, 6, 7} by decide)) hS)
  · exact hv (by decide)
  · exact n283 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 7} = {2, 4, 7, 8} by decide)) hS)
  · exact hne (by decide)

theorem c1097 (h : TenSystem T Q) :
    T {2, 4, 8} → ¬ Q {0, 2, 4, 8} → ¬ Q {1, 2, 4, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 7, 8} → ¬ Q {2, 4, 8, 9} → False := by
  intro a74 n158 n214 n264 n278 n281 n283 n285
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 4, 8} a74
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n158 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n214 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 8} = {1, 2, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n264 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n278 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 4, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n283 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 8} = {2, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n285 (Eq.mp (congrArg Q (show insert (9 : Labels) {2, 4, 8} = {2, 4, 8, 9} by decide)) hS)

theorem c1111 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → ¬ Q {0, 2, 4, 8} → ¬ Q {1, 2, 4, 8} → ¬ Q {2, 3, 4, 8} → ¬ Q {2, 4, 5, 8} → ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 7, 8} → False := by
  intro a285 n158 n214 n264 n278 n281 n283
  obtain ⟨S, hS, hUS, hne⟩ := h.no_boundary {2, 4, 8, 9} {2, 4, 8} a285 (by decide) (by decide)
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 8} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n158 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 8} = {0, 2, 4, 8} by decide)) hS)
  · exact n214 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 8} = {1, 2, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n264 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 8} = {2, 3, 4, 8} by decide)) hS)
  · exact hv (by decide)
  · exact n278 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 8} = {2, 4, 5, 8} by decide)) hS)
  · exact n281 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 4, 8} = {2, 4, 6, 8} by decide)) hS)
  · exact n283 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 8} = {2, 4, 7, 8} by decide)) hS)
  · exact hv (by decide)
  · exact hne (by decide)

theorem c1112 (h : TenSystem T Q) :
    T {2, 4, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {2, 3, 4, 9} → ¬ Q {2, 4, 5, 9} → ¬ Q {2, 4, 6, 9} → ¬ Q {2, 4, 7, 9} → ¬ Q {2, 4, 8, 9} → False := by
  intro a75 n159 n215 n265 n279 n282 n284 n285
  obtain ⟨S, hS, hUS⟩ := h.pure {2, 4, 9} a75
  obtain ⟨v, hv, rfl⟩ := tetra_extension hUS (h.tetra_card S hS) (show ( {2, 4, 9} : Finset Labels).card = 3 by decide)
  fin_cases v
  · exact n159 (Eq.mp (congrArg Q (show insert (0 : Labels) {2, 4, 9} = {0, 2, 4, 9} by decide)) hS)
  · exact n215 (Eq.mp (congrArg Q (show insert (1 : Labels) {2, 4, 9} = {1, 2, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n265 (Eq.mp (congrArg Q (show insert (3 : Labels) {2, 4, 9} = {2, 3, 4, 9} by decide)) hS)
  · exact hv (by decide)
  · exact n279 (Eq.mp (congrArg Q (show insert (5 : Labels) {2, 4, 9} = {2, 4, 5, 9} by decide)) hS)
  · exact n282 (Eq.mp (congrArg Q (show insert (6 : Labels) {2, 4, 9} = {2, 4, 6, 9} by decide)) hS)
  · exact n284 (Eq.mp (congrArg Q (show insert (7 : Labels) {2, 4, 9} = {2, 4, 7, 9} by decide)) hS)
  · exact n285 (Eq.mp (congrArg Q (show insert (8 : Labels) {2, 4, 9} = {2, 4, 8, 9} by decide)) hS)
  · exact hv (by decide)

theorem c1113 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {2, 4, 9} → False := by
  intro a159 n75
  exact n75 (h.down {0, 2, 4, 9} {2, 4, 9} a159 (by decide) (by decide))

end BorsukNine.FiniteObstruction

end OAI
