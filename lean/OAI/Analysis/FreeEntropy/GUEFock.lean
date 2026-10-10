import OAI.Analysis.FreeEntropy.MatrixHeatLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
open FreeSeries
variable {n d : ℕ}
 theorem matrixTraceWord_gue_map (x : MatrixIndex n d → ℝ) (w : List (Fin n)) :
    matrixTraceWord (jointMatrix (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) x) (w.map Sum.inr) = matrixTraceWord (gueMatrix x) w := by
  rw [matrixTraceWord_map]
  rfl
 theorem gueTraceWord_stein_pure (hd : 0 < d) (i : Fin n) (w : List (Fin n)) :
    (∫ x, matrixTraceWord (gueMatrix x) (i::w) ∂productGaussian (MatrixIndex n d)) =
      ∑ r : Fin w.length, if w[r.val]=i then
        ∫ x, matrixTraceWord (gueMatrix x) (w.take r.val)*matrixTraceWord (gueMatrix x) (w.drop (r.val+1)) ∂productGaussian (MatrixIndex n d) else 0 := by
  have h := gueTraceWord_stein hd (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) i (w.map Sum.inr)
  have he : Sum.inr i::w.map (Sum.inr (α := Empty)) = (i::w).map Sum.inr := rfl
  rw [he] at h
  simp only [matrixTraceWord_gue_map] at h
  rw [h]
  apply Fintype.sum_equiv (finCongr (List.length_map (as := w) (Sum.inr (α := Empty))))
  intro r
  simp only [finCongr_apply,Fin.val_cast,List.getElem_map,Sum.inr.injEq,← List.map_take,← List.map_drop,matrixTraceWord_gue_map]
 theorem gueTraceWord_expected_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop) (w : List (Fin n)) :
    Tendsto (fun k => ∫ x, matrixTraceWord (gueMatrix x) w ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 (fockMoments n w)) := by
  induction w using FreeSeries.length_induction with
  | h w ih =>
    cases w with
    | nil =>
      have he (k : ℕ) (x : MatrixIndex n (D k) → ℝ) : matrixTraceWord (gueMatrix x) [] = 1 := by
        simp [matrixTraceWord,matrixWord,ne_of_gt (hD0 k)]
      simp [he,fockMoments]
    | cons i w =>
      have hf : fockMoments n (i::w) = ∑ r : Fin w.length, if w[r.val]=i then fockMoments n (w.take r.val)*fockMoments n (w.drop (r.val+1)) else 0 :=
        Fock.semicircular_integration_by_parts i w
      simp only [gueTraceWord_stein_pure (hD0 _), hf]
      apply tendsto_finsetSum
      intro r _
      split_ifs with hr
      · have hc := matrixTraceWord_covariance_tendsto hD0 hD (fun k (_ : Empty) => (0 : Matrix (Fin (D k)) (Fin (D k)) ℂ)) (R := 0) le_rfl (by intro k a; exact a.elim) ((w.take r.val).map Sum.inr) ((w.drop (r.val+1)).map Sum.inr)
        simp only [matrixTraceWord_gue_map,expectedMatrixWord] at hc
        apply tendsto_of_sub_zero hc
        exact (ih (w.take r.val) (by simp)).mul (ih (w.drop (r.val+1)) (by simp))
      · exact tendsto_const_nhds
 theorem gueTraceWord_probability_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (w : List (Fin n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real {x | ε ≤ ‖matrixTraceWord (gueMatrix x) w-fockMoments n w‖}) atTop (𝓝 0) := by
  have hm : Tendsto (fun k => expectedMatrixWord (fun k (_ : Empty) => (0 : Matrix (Fin (D k)) (Fin (D k)) ℂ)) k (w.map Sum.inr)) atTop (𝓝 (fockMoments n w)) := by
    simpa only [expectedMatrixWord,matrixTraceWord_gue_map] using gueTraceWord_expected_tendsto hD0 hD w
  simpa only [matrixTraceWord_gue_map] using matrixTraceWord_probability_tendsto hD0 hD _ (R := 0) le_rfl (by intro k a; exact a.elim) (w.map Sum.inr) hm hε
end FiniteEntropySeparation

end

end OAI
