import OAI.Analysis.FreeEntropy.GUEFock

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped Classical Topology
namespace FiniteEntropySeparation
 theorem gueMatrix_norm_tail64 {n d : ℕ} (hd : 0<d) (i : Fin n) :
    (productGaussian (MatrixIndex n d)).real {x | 64 < matrixOpNorm (gueMatrix x i)} ≤ 4*Real.exp (-64*(d:ℝ)) := by
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9)
  calc
    _ ≤ 4*9^(4*d)*Real.exp (-((d:ℝ)*64^2)/32) := gueMatrix_norm_tail hd i (by norm_num)
    _ = 4*Real.exp ((4*(d:ℝ))*Real.log 9 - (d:ℝ)*64^2/32) := by
      rw [show (9:ℝ)^(4*d)=Real.exp ((4*(d:ℝ))*Real.log 9) by rw [show 4*(d:ℝ)=((4*d:ℕ):ℝ) by push_cast; rfl, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<9)]]
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ _ := by
      gcongr
      have hd' : 0 ≤ (d:ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hd' (show 0 ≤ 8-Real.log 9 by linarith)]
 theorem gueMatrix_norm_probability_tendsto {n : ℕ} {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop) (i : Fin n) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real {x | 64 < matrixOpNorm (gueMatrix x i)}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => gueMatrix_norm_tail64 (hD0 k) i)
  have ht : Tendsto (fun k => (64:ℝ)*(D k:ℝ)) atTop atTop := (tendsto_natCast_atTop_atTop.comp hD).const_mul_atTop (by norm_num)
  simpa only [neg_mul, mul_zero,Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul 4
 def gueBad (n m d : ℕ) (ε : ℝ) : Set (MatrixIndex n d → ℝ) :=
    {x | (∃ i,64 < matrixOpNorm (gueMatrix x i)) ∨ ∃ w : List (Fin n), w.length ≤ m ∧ ε ≤ ‖matrixTraceWord (gueMatrix x) w-FreeSeries.fockMoments n w‖}
 theorem gueBad_probability_tendsto (n m : ℕ) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (k+1))).real (gueBad n m (k+1) ε)) atTop (𝓝 0) := by
  let W := (List.finite_length_le (Fin n) m).toFinset
  have hD : Tendsto (fun k : ℕ => k+1) atTop atTop := tendsto_add_atTop_nat 1
  have hn : Tendsto (fun k => ∑ i : Fin n, (productGaussian (MatrixIndex n (k+1))).real {x | 64 < matrixOpNorm (gueMatrix x i)}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ (fun i _ => gueMatrix_norm_probability_tendsto (fun _ => Nat.succ_pos _) hD i)
  have hw : Tendsto (fun k => ∑ w ∈ W, (productGaussian (MatrixIndex n (k+1))).real {x | ε ≤ ‖matrixTraceWord (gueMatrix x) w-FreeSeries.fockMoments n w‖}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum W (fun w _ => gueTraceWord_probability_tendsto (fun _ => Nat.succ_pos _) hD w hε)
  apply squeeze_zero (fun k => measureReal_nonneg) _ (by simpa using hn.add hw)
  intro k
  have he : gueBad n m (k+1) ε =
      (⋃ i ∈ (univ : Finset (Fin n)), {x | 64 < matrixOpNorm (gueMatrix x i)}) ∪
      (⋃ w ∈ W, {x | ε ≤ ‖matrixTraceWord (gueMatrix x) w-FreeSeries.fockMoments n w‖}) := by
    ext x
    simp [gueBad,W]
  rw [he]
  exact (measureReal_union_le _ _).trans (add_le_add (measureReal_biUnion_finset_le _ _) (measureReal_biUnion_finset_le _ _))
 theorem exists_gue_model (n m K : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ d, K<d ∧ ∃ x : MatrixIndex n d → ℝ, (∀ i,matrixOpNorm (gueMatrix x i) ≤ 64) ∧
      ∀ w : List (Fin n), w.length ≤ m → ‖matrixTraceWord (gueMatrix x) w-FreeSeries.fockMoments n w‖ < ε := by
  have ht := (gueBad_probability_tendsto n m hε).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨k,hp⟩ := (eventually_atTop.mp ht)
  let q := max k K
  have hq : (productGaussian (MatrixIndex n (q+1))).real (gueBad n m (q+1) ε)<1 := hp q (le_max_left _ _)
  have hx : ∃ x : MatrixIndex n (q+1) → ℝ, x ∉ gueBad n m (q+1) ε := by
    by_contra hh
    have he : gueBad n m (q+1) ε = univ := by ext x; simp only [mem_univ,iff_true]; exact not_not.mp (not_exists.mp hh x)
    simp [he] at hq
  obtain ⟨x,hx⟩ := hx
  refine ⟨q+1,by dsimp [q]; omega,x,?_,?_⟩
  · intro i; by_contra hi; exact hx (Or.inl ⟨i,not_le.mp hi⟩)
  · intro w hw; by_contra hh; exact hx (Or.inr ⟨w,hw,not_lt.mp hh⟩)
end FiniteEntropySeparation

end

end OAI
