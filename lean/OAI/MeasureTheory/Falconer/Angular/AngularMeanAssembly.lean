import OAI.MeasureTheory.Falconer.Angular.AngularProfileSum

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem stripHitBound_sum_diagonal {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι) (v : ι → Plane) (ha : v a = 0)
    (hv : ∀ i ∈ S.erase a, v i ≠ 0) {W : ℝ} (hW : 0 ≤ W) :
    ∑ i ∈ S, stripHitBound W (v i) ≤
      ENNReal.ofReal (2*Real.pi+4*Real.pi*W*(∑ i ∈ S.erase a, 1/‖v i‖)) := by
  have hh : ∑ i ∈ S.erase a, stripHitBound W (v i) ≤
      ∑ i ∈ S.erase a, ENNReal.ofReal (4*Real.pi*W*(1/‖v i‖)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [stripHitBound,ite_eq_right (hv i hi)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ 4*Real.pi*(W/‖v i‖) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by ring
  have he : (∑ i ∈ S.erase a, ENNReal.ofReal (4*Real.pi*W*(1/‖v i‖))) =
      ENNReal.ofReal (4*Real.pi*W*(∑ i ∈ S.erase a, 1/‖v i‖)) := by
    rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
    intro i _; positivity
  rw [he] at hh
  calc
    _ ≤ ∑ i ∈ insert a (S.erase a), stripHitBound W (v i) :=
      Finset.sum_le_sum_of_subset (by intro i hi; by_cases h : i=a <;> simp [h,hi])
    _ = ENNReal.ofReal (2*Real.pi) + ∑ i ∈ S.erase a, stripHitBound W (v i) := by
      rw [Finset.sum_insert (Finset.notMem_erase a S),ha]
      simp [stripHitBound]
    _ ≤ _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add_right hh _

theorem parallel_strip_sum_inverse (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (g p : ℕ) {P : CellPath} (hP : P.length = p)
    {W : ℝ} (hW : 0 ≤ W) :
    ∑ c ∈ parallelTestCells Q ρ g p P,
      stripHitBound W (quarterTurn ((Q.descendant c).center-(Q.descendant P).center)) ≤
      ENNReal.ofReal (2*Real.pi+4*Real.pi*W*
        (∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
          1/dist (Q.descendant c).center (Q.descendant P).center)) := by
  classical
  have hh := stripHitBound_sum_diagonal (parallelTestCells Q ρ g p P) P
    (fun c => quarterTurn ((Q.descendant c).center-(Q.descendant P).center))
    (by simp [quarterTurn]) ?_ hW
  · simpa only [norm_quarterTurn,dist_eq_norm] using hh
  intro c hc hz
  have hl := (mem_dyadicPaths p c).mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)).1
  have hs := dyadic_centers_separated Q hQ hl hP (Finset.ne_of_mem_erase hc)
  have hn : dist (Q.descendant c).center (Q.descendant P).center = 0 := by
    rw [dist_eq_norm,← norm_quarterTurn,hz,norm_zero]
  rw [hn] at hs
  exact (not_le_of_gt (by positivity : 0 < Q.side/(2:ℝ)^p)) hs

end PlanarFalconer

end OAI
