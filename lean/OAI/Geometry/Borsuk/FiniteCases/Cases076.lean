import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases001
import OAI.Geometry.Borsuk.FiniteCases.Cases006

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c29971 (h : TenSystem T Q) :
    Q {4, 6, 7, 8} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 5} → False := by
  intro a322 a1 a9 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 8} {0, 2} {1, 3, 5} a322 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c29979 (h : TenSystem T Q) :
    Q {4, 6, 7, 8} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 5} → False := by
  intro a322 a2 a9 a17
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 8} {0, 3} {1, 2, 5} a322 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)

theorem c29986 (h : TenSystem T Q) :
    Q {4, 6, 7, 8} → ¬ T {0, 1, 5} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → False := by
  intro a322 n4 n11 n17
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 6, 7, 8} {0, 5} {1, 2, 3} a322 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)

theorem c30103 (h : TenSystem T Q) :
    Q {4, 6, 7, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 5} → False := by
  intro a323 a1 a2 a4
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 9} {0, 1} {2, 3, 5} a323 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)

theorem c30111 (h : TenSystem T Q) :
    Q {4, 6, 7, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 5} → False := by
  intro a323 a1 a9 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 9} {0, 2} {1, 3, 5} a323 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c30119 (h : TenSystem T Q) :
    Q {4, 6, 7, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 5} → False := by
  intro a323 a2 a9 a17
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 7, 9} {0, 3} {1, 2, 5} a323 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)

theorem c30126 (h : TenSystem T Q) :
    Q {4, 6, 7, 9} → ¬ T {0, 1, 5} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → False := by
  intro a323 n4 n11 n17
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 6, 7, 9} {0, 5} {1, 2, 3} a323 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)

theorem c30243 (h : TenSystem T Q) :
    Q {4, 6, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 5} → False := by
  intro a324 a1 a2 a4
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 8, 9} {0, 1} {2, 3, 5} a324 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)

theorem c30251 (h : TenSystem T Q) :
    Q {4, 6, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 5} → False := by
  intro a324 a1 a9 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 8, 9} {0, 2} {1, 3, 5} a324 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c30259 (h : TenSystem T Q) :
    Q {4, 6, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 5} → False := by
  intro a324 a2 a9 a17
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 6, 8, 9} {0, 3} {1, 2, 5} a324 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)

theorem c30266 (h : TenSystem T Q) :
    Q {4, 6, 8, 9} → ¬ T {0, 1, 5} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → False := by
  intro a324 n4 n11 n17
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 6, 8, 9} {0, 5} {1, 2, 3} a324 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)

theorem c30383 (h : TenSystem T Q) :
    Q {4, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 5} → False := by
  intro a325 a1 a2 a4
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 7, 8, 9} {0, 1} {2, 3, 5} a325 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)

theorem c30391 (h : TenSystem T Q) :
    Q {4, 7, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 5} → False := by
  intro a325 a1 a9 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 7, 8, 9} {0, 2} {1, 3, 5} a325 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c30399 (h : TenSystem T Q) :
    Q {4, 7, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 5} → False := by
  intro a325 a2 a9 a17
  obtain ⟨w, hw, ht⟩ := three_neg h {4, 7, 8, 9} {0, 3} {1, 2, 5} a325 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)

theorem c30406 (h : TenSystem T Q) :
    Q {4, 7, 8, 9} → ¬ T {0, 1, 5} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → False := by
  intro a325 n4 n11 n17
  obtain ⟨w, hw, ht⟩ := three_pos h {4, 7, 8, 9} {0, 5} {1, 2, 3} a325 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)

theorem c30523 (h : TenSystem T Q) :
    Q {5, 6, 7, 8} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a326 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 8} {0, 1} {2, 3, 4} a326 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

theorem c30531 (h : TenSystem T Q) :
    Q {5, 6, 7, 8} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a326 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 8} {0, 2} {1, 3, 4} a326 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

theorem c30539 (h : TenSystem T Q) :
    Q {5, 6, 7, 8} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a326 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 8} {0, 3} {1, 2, 4} a326 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

theorem c30546 (h : TenSystem T Q) :
    Q {5, 6, 7, 8} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a326 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {5, 6, 7, 8} {0, 4} {1, 2, 3} a326 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)

theorem c30663 (h : TenSystem T Q) :
    Q {5, 6, 7, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a327 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 9} {0, 1} {2, 3, 4} a327 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

theorem c30671 (h : TenSystem T Q) :
    Q {5, 6, 7, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a327 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 9} {0, 2} {1, 3, 4} a327 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

theorem c30679 (h : TenSystem T Q) :
    Q {5, 6, 7, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a327 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 7, 9} {0, 3} {1, 2, 4} a327 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

theorem c30686 (h : TenSystem T Q) :
    Q {5, 6, 7, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a327 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {5, 6, 7, 9} {0, 4} {1, 2, 3} a327 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)

theorem c30803 (h : TenSystem T Q) :
    Q {5, 6, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a328 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 8, 9} {0, 1} {2, 3, 4} a328 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

theorem c30811 (h : TenSystem T Q) :
    Q {5, 6, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a328 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 8, 9} {0, 2} {1, 3, 4} a328 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

theorem c30819 (h : TenSystem T Q) :
    Q {5, 6, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a328 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 6, 8, 9} {0, 3} {1, 2, 4} a328 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

theorem c30826 (h : TenSystem T Q) :
    Q {5, 6, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a328 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {5, 6, 8, 9} {0, 4} {1, 2, 3} a328 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)

private theorem c30943 (h : TenSystem T Q) :
    Q {5, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a329 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 7, 8, 9} {0, 1} {2, 3, 4} a329 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

private theorem c30951 (h : TenSystem T Q) :
    Q {5, 7, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a329 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 7, 8, 9} {0, 2} {1, 3, 4} a329 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

private theorem c30959 (h : TenSystem T Q) :
    Q {5, 7, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a329 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {5, 7, 8, 9} {0, 3} {1, 2, 4} a329 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

private theorem c30966 (h : TenSystem T Q) :
    Q {5, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a329 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {5, 7, 8, 9} {0, 4} {1, 2, 3} a329 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)

private theorem c31083 (h : TenSystem T Q) :
    Q {6, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 3} → T {0, 1, 4} → False := by
  intro a330 a1 a2 a3
  obtain ⟨w, hw, ht⟩ := three_neg h {6, 7, 8, 9} {0, 1} {2, 3, 4} a330 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)

private theorem c31091 (h : TenSystem T Q) :
    Q {6, 7, 8, 9} → T {0, 1, 2} → T {0, 2, 3} → T {0, 2, 4} → False := by
  intro a330 a1 a9 a10
  obtain ⟨w, hw, ht⟩ := three_neg h {6, 7, 8, 9} {0, 2} {1, 3, 4} a330 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)

private theorem c31099 (h : TenSystem T Q) :
    Q {6, 7, 8, 9} → T {0, 1, 3} → T {0, 2, 3} → T {0, 3, 4} → False := by
  intro a330 a2 a9 a16
  obtain ⟨w, hw, ht⟩ := three_neg h {6, 7, 8, 9} {0, 3} {1, 2, 4} a330 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)

private theorem c31106 (h : TenSystem T Q) :
    Q {6, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → False := by
  intro a330 n3 n10 n16
  obtain ⟨w, hw, ht⟩ := three_pos h {6, 7, 8, 9} {0, 4} {1, 2, 3} a330 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)

theorem c31202 (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 1, 2, 3} → False := by
  intro n121
  exact n121 h0
theorem c31203 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 1, 2} → False := by
  classical
  intro n1
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c3 h u0_121 n1

theorem c31204 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 1, 3} → False := by
  classical
  intro n2
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c18 h u0_121 n2

theorem c31205 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 2, 3} → False := by
  classical
  intro n9
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c123 h u0_121 n9

theorem c31206 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 3} → False := by
  classical
  intro n37
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c543 h u0_121 n37

theorem c31207 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {6, 7, 8, 9} → False := by
  classical
  intro a330
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c31083 h a330 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31091 h a330 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c31099 h a330 u1_2 u2_9 hv
  exact c31106 h a330 u3_3 u4_10 u5_16

theorem c31208 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {5, 7, 8, 9} → False := by
  classical
  intro a329
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c30943 h a329 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c30951 h a329 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c30959 h a329 u1_2 u2_9 hv
  exact c30966 h a329 u3_3 u4_10 u5_16

end BorsukNine.FiniteObstruction

end OAI
