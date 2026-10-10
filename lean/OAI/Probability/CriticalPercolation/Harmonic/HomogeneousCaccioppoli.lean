import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry
import OAI.Probability.CriticalPercolation.Harmonic.CayleyCaccioppoli

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {X : Type*} (W : Geometry X)

lemma sum_neighbor_rows (F : Finset X) (x : X) (f : X → ℝ)
    (hF : ∀ y∈W.neighbors x, y∈F) :
    (∑ y∈F, if W.graph.Adj x y then f y else 0)=∑ y∈W.neighbors x, f y := by
  rw [←Finset.sum_filter]
  apply Finset.sum_congr
  · ext y
    simp only [Finset.mem_filter,W.mem_neighbors]
    exact ⟨And.right,fun h => ⟨hF y (W.mem_neighbors.mpr h),h⟩⟩
  · intros; rfl

lemma sum_neighbor_rows_le (F : Finset X) (x : X) (f : X → ℝ)
    (hf : ∀ y, 0≤f y) :
    (∑ y∈F, if W.graph.Adj x y then f y else 0)≤∑ y∈W.neighbors x, f y := by
  rw [←Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro y hy; exact W.mem_neighbors.mpr (Finset.mem_filter.mp hy).2
  · intros; apply hf

lemma cutoff_neighbor_mem_ball (R : ℕ) {x : X} (hx : W.cutoff R x≠0)
    {y : X} (hy : y∈W.neighbors x) : y∈W.ball (2*R+1) := by
  apply W.length_le_iff.mp
  have hl := W.cutoff_ne_zero_length R hx
  have hh := (W.length_adj (W.mem_neighbors.mp hy)).2
  omega

theorem caccioppoli (u : X → ℝ) (hu : W.IsHarmonic u) (R : ℕ) :
    (R:ℝ)^2*W.energy (W.ball R) u ≤
      4*(W.degree:ℝ)*squareMass (W.ball (2*R+1)) u := by
  let F := W.ball (2*R+1)
  let w : F → F → ℝ := fun x y => if W.graph.Adj x.val y.val then 1 else 0
  let η : F → ℝ := fun x => W.cutoff R x.val
  have hw (x y : F) : w x y=w y x := by
    dsimp [w]
    exact if_congr (W.graph.adj_comm _ _) rfl rfl
  have hw0 (x y : F) : 0≤w x y := by dsimp [w]; split <;> positivity
  have hh (x : F) : η x=0 ∨ (∑ y:F, w x y*(u x.val-u y.val))=0 := by
    by_cases hx : η x=0
    · exact Or.inl hx
    right
    have hx' : W.cutoff R x.val≠0 := hx
    simp only [w,ite_mul,one_mul,zero_mul]
    rw [Finset.sum_coe_sort F (fun y : X =>
      if W.graph.Adj x.val y then u x.val-u y else 0)]
    rw [W.sum_neighbor_rows F x.val (fun y => u x.val-u y)
      (fun s hs => W.cutoff_neighbor_mem_ball R hx' hs)]
    exact hu x.val
  have hc := finite_caccioppoli w hw hw0 (fun x:F => u x.val) η hh
  have hL : (R:ℝ)^2*W.energy (W.ball R) u ≤
      ∑ x:F, ∑ y:F, w x y*(η x)^2*(u x.val-u y.val)^2 := by
    simp only [w,η,ite_mul,one_mul,zero_mul]
    rw [show (∑ x:F, ∑ y:F, if W.graph.Adj x.val y.val then
      (W.cutoff R x.val)^2*(u x.val-u y.val)^2 else 0) =
      ∑ x∈F, ∑ y∈F, if W.graph.Adj x y then
      (W.cutoff R x)^2*(u x-u y)^2 else 0 from
      sum_subtype_pair F (fun x y => if W.graph.Adj x y then
        (W.cutoff R x)^2*(u x-u y)^2 else 0)]
    have hsub : W.ball R⊆F := W.ball_mono (by omega)
    calc
      _ = ∑ x∈W.ball R, (R:ℝ)^2*(∑ y∈W.neighbors x, (u x-u y)^2) := by
        unfold energy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ ≤ ∑ x∈W.ball R, (W.cutoff R x)^2*(∑ y∈W.neighbors x, (u x-u y)^2) := by
        apply Finset.sum_le_sum
        intro x hx
        apply mul_le_mul_of_nonneg_right
        · exact sq_le_sq₀ (by positivity) (W.cutoff_nonneg R x) |>.mpr (W.cutoff_large R hx)
        · exact Finset.sum_nonneg (fun s _ => sq_nonneg _)
      _ = ∑ x∈W.ball R, ∑ y∈F,
          if W.graph.Adj x y then (W.cutoff R x)^2*(u x-u y)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [W.sum_neighbor_rows]
        · exact Finset.mul_sum _ _ _
        · intro y hy
          apply W.length_le_iff.mp
          have hlx := W.length_le_iff.mpr hx
          have hhx := (W.length_adj (W.mem_neighbors.mp hy)).2
          omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro x hx hxn
        exact Finset.sum_nonneg (fun y hy => by split <;> positivity))
  have hU : (∑ x:F, ∑ y:F, w x y*(u x.val)^2*(η x-η y)^2) ≤
      (W.degree:ℝ)*squareMass F u := by
    simp only [w,η,ite_mul,one_mul,zero_mul]
    rw [show (∑ x:F, ∑ y:F, if W.graph.Adj x.val y.val then
      (u x.val)^2*(W.cutoff R x.val-W.cutoff R y.val)^2 else 0) =
      ∑ x∈F, ∑ y∈F, if W.graph.Adj x y then
      (u x)^2*(W.cutoff R x-W.cutoff R y)^2 else 0 from
      sum_subtype_pair F (fun x y => if W.graph.Adj x y then
        (u x)^2*(W.cutoff R x-W.cutoff R y)^2 else 0)]
    unfold squareMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    calc
      _ ≤ ∑ y∈F, if W.graph.Adj x y then (u x)^2 else 0 := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hs : W.graph.Adj x y
        · simp only [ite_eq_left hs]
          have ha := W.cutoff_lipschitz R hs
          rw [abs_sub_comm] at ha
          have hsquare := (sq_le_one_iff_abs_le_one _).mpr ha
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hsquare (sq_nonneg (u x))
        · simp only [ite_eq_right hs,le_refl]
      _ ≤ ∑ y∈W.neighbors x, (u x)^2 := W.sum_neighbor_rows_le _ _ _ (by intro y; positivity)
      _ = _ := by simp [W.neighbors_card]
  have hU' := mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ)≤4)
  change _≤4*(W.degree:ℝ)*squareMass F u
  calc
    _ ≤ _ := hL.trans hc
    _ ≤ _ := by simpa only [mul_assoc] using hU'

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
