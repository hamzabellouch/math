import OAI.Analysis.FreeEntropy.GaussianL2Limit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
open FreeSeries
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
def sumJointMoment (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N)
    (w : List (Fin n ⊕ Fin n)) : ℂ :=
  wordMoment (tracialVector B N G) (jointTuple X σ) (w.map finSumFinEquiv)
 theorem sumJointMoment_cyclic (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (σ : Fin n → N) (u v : List (Fin n ⊕ Fin n)) :
    sumJointMoment X σ (u++v)=sumJointMoment X σ (v++u) := by
  simp only [sumJointMoment,List.map_append]
  exact (wordMoment_cyclic (tracialVector B N G) _ (jointTuple_mem J X hX σ)).append _ _
 theorem sumJointMoment_left (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N) (u : List (Fin n)) :
    sumJointMoment X σ (u.map Sum.inl)=wordMoment (tracialVector B N G) X u := by
  simp only [sumJointMoment,wordMoment,wordEval,List.map_map]
  congr 3
  funext i
  exact jointTuple_left X σ i
 theorem sumJointMoment_noise (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (σ : Fin n → N) (hσ : Function.Injective σ)
    (hs : ∀ i, σ i ∉ J) (i : Fin n) (w : List (Fin n ⊕ Fin n)) :
    sumJointMoment X σ (Sum.inr i::w)= ∑ r : Fin w.length,
      if w[r.val]=Sum.inr i then sumJointMoment X σ (w.take r.val)*sumJointMoment X σ (w.drop (r.val+1)) else 0 := by
  have h := congrFun (jointTuple_noise_deriv J X hX σ hσ hs i) (w.map finSumFinEquiv)
  rw [← derivativeMoment_series] at h
  change wordMoment (tracialVector B N G) (jointTuple X σ) (rightIndex i::w.map finSumFinEquiv)=_ at h
  change wordMoment (tracialVector B N G) (jointTuple X σ) (rightIndex i::w.map finSumFinEquiv) = _
  rw [h]
  dsimp only
  simp only [derivativeMoment]
  apply Fintype.sum_equiv (finCongr (List.length_map (as := w) finSumFinEquiv))
  intro r
  simp only [finCongr_apply, Fin.val_cast, List.getElem_map, ← List.map_take, ← List.map_drop]
  have he : finSumFinEquiv w[r.val] = rightIndex i ↔ w[r.val]=Sum.inr i :=
    by change finSumFinEquiv w[r.val] = finSumFinEquiv (Sum.inr i) ↔ _; exact finSumFinEquiv.injective.eq_iff
  simp only [he,sumJointMoment]
 theorem expectedMatrixWord_free_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → Fin n → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k i, matrixOpNorm (A k i) ≤ R)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (hbase : ∀ u, Tendsto (fun k => matrixTraceWord (A k) u) atTop (𝓝 (wordMoment (tracialVector B N G) X u)))
    (w : List (Fin n ⊕ Fin n)) :
    Tendsto (fun k => expectedMatrixWord A k w) atTop (𝓝 (sumJointMoment X σ w)) := by
  apply expectedMatrixWord_tendsto hD0 hD A hR hA _ (sumJointMoment_cyclic J X hX σ)
  · intro u
    simpa only [sumJointMoment_left] using hbase u
  · intro i v
    classical
    exact (sumJointMoment_noise J X hX σ hσ hs i v).trans (by
      apply sum_congr rfl
      intro r _
      split_ifs <;> rfl)
end FreeTensor
end FiniteEntropySeparation

end

end OAI
