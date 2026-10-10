import OAI.Analysis.TriangularHilbert.StarInsertion

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def heatCost (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w : Three) : ℝ :=
  hessianCost (localGram A h u p σ v w) (localFirst A h u p σ v w)

def heatMixed (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (v w z : Three) : ℝ :=
  hessianPair (localGram A h u p σ v w) (localFirst A h u p σ v w)
    (localFirst A h u p σ v z)

def heatScores (u : ι → ℝ) (p σ : Three → ℝ) : Three → Matrix ι ι ℂ :=
  fun w => Matrix.diagonal (fun i => (score (u i) (p w) (σ w) : ℂ))

lemma fixedBase_update_other (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (q : ℝ) :
    fixedBase A (heatWeights h u (Function.update p z q) σ) v w =
      fixedBase A (heatWeights h u p σ) v w := by
  simp only [fixedBase, ite_eq_right hw]
  apply colBare_congr
  intro i
  simp only [heatWeights, Function.update_of_ne (Ne.symm hz)]

lemma heatFirst_hasDerivAt_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    HasDerivAt (fun q => heatFirst A h u (Function.update p z q) σ v w)
      (heatMixed A h u p σ v w z) (p z) := by
  have hd := groupEnergyFirst_hasDerivAt_other (colBare A (heatWeights h u p σ) v)
    hh (fun a : BlockSpace ι => u a.2) Prod.fst p hσ hwz
  simp only [heatMixed, localGram, localFirst, fixedBase, ite_eq_right hw, ite_eq_right hz]
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro q
  dsimp only
  unfold heatFirst localGram localFirst
  rw [fixedBase_update_other A h u p σ hw hz q]
  simp only [fixedBase, ite_eq_right hw]

lemma two_heatMixed_le (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) :
    2 * heatMixed A h u p σ v w z ≤ heatCost A h u p σ v w + heatCost A h u p σ v z := by
  simp only [heatMixed, heatCost, localGram, localFirst, fixedBase, ite_eq_right hw, ite_eq_right hz]
  exact two_hessianPair_weightedGram_le _ (groupWeight_pos hh _ _ p hσ) _ _

lemma localGram_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    localGram A h u p σ v v = starGram (heatArray A h u p σ) v := by
  simp only [localGram, fixedBase, ite_true]
  exact (starGram_weightedArray A _ (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v).symm

lemma localGram_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    localGram A h u p σ v w = rowStar (heatArray A h u p σ) v *
      (rowStar (heatArray A h u p σ) v)ᴴ := by
  simp only [localGram, fixedBase, ite_eq_right hw]
  exact (centerGram_weightedArray_padded A _
    (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v).symm

omit [Fintype ι] [DecidableEq ι] in
lemma groupFirst_eq_insert (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (w : Three) :
    groupFirst h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w =
      fun a : BlockSpace ι => heatWeights h u p σ a.1 a.2 *
        (if a.1 = w then score (u a.2) (p a.1) (σ a.1) else 0) := by
  funext a
  simp only [groupFirst, heatWeights]
  split_ifs with ha
  · rw [ha, mul_comm]
  · rw [mul_zero]

lemma localFirst_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    localFirst A h u p σ v v =
      starInsert (heatArray A h u p σ) (heatScores u p σ) v := by
  simp only [localFirst, fixedBase, ite_true, groupFirst_eq_insert]
  rw [rowBare_insert A (heatWeights h u p σ)
    (fun w i => if w = v then score (u i) (p w) (σ w) else 0)
    (fun w i => (weight_pos hh (hσ w) (u i) (p w)).le) v]
  rw [starInsert_eq_insertRow, starInsert_eq_insertRow]
  simp only [heatArray, heatScores, ite_true]

lemma localFirst_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    localFirst A h u p σ v w = rowStar (heatArray A h u p σ) v *
      blockD (fun a => if a = w then heatScores u p σ w else 0) *
      (rowStar (heatArray A h u p σ) v)ᴴ := by
  simp only [localFirst, fixedBase, ite_eq_right hw, groupFirst_eq_insert]
  rw [colBare_insert A (heatWeights h u p σ)
    (fun a i => if a = w then score (u i) (p a) (σ a) else 0)
    (fun a i => (weight_pos hh (hσ a) (u i) (p a)).le) v]
  congr 2
  congr 1
  funext a
  by_cases ha : a = w
  · subst a
    simp [heatScores]
  · simp [ha]

lemma heatCost_center (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    heatCost A h u p σ v v = hessianCost (starGram (heatArray A h u p σ) v)
      (starInsert (heatArray A h u p σ) (heatScores u p σ) v) := by
  rw [heatCost, localGram_center A hh u p hσ, localFirst_center A hh u p hσ]

lemma heatCost_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w : Three} (hw : w ≠ v) :
    heatCost A h u p σ v w = hessianCost (centerGram (heatArray A h u p σ) v)
      ((triangleBlocks (heatArray A h u p σ) w v)ᴴ * heatScores u p σ w *
        triangleBlocks (heatArray A h u p σ) w v) := by
  rw [heatCost, localGram_other A hh u p hσ hw, localFirst_other A hh u p hσ hw]
  exact hessianCost_rowStar_singleBlock _ _ v w

lemma heatCost_nonneg (A : Three → Matrix ι ι ℂ) (h : ℝ)
    (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :
    0 ≤ heatCost A h u p σ v w := by
  unfold heatCost hessianCost rootCost
  apply mul_nonneg (by norm_num)
  by_cases hb : BddAbove (Set.range (variation (CFC.sqrt (localGram A h u p σ v w))
      (localFirst A h u p σ v w)))
  · apply le_csSup hb
    exact ⟨0, by simp [variation, penalty]⟩
  · rw [Real.sSup_of_not_bddAbove hb]

lemma heatCost_neighbors (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (w : Three) :
    (∑ v, if v = w then 0 else heatCost A h u p σ v w) ≤
      Real.sqrt 2 * heatCost A h u p σ w w := by
  rw [heatCost_center A hh u p hσ]
  convert neighbor_comparison (heatArray A h u p σ) (heatScores u p σ) w using 1
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = w
  · subst v
    simp [triangleBlocks_diag, hessianCost_zero_direction]
  · rw [ite_eq_right hv, heatCost_other A hh u p hσ (Ne.symm hv)]

end
end TriangularHilbert.Heat
end

end OAI
