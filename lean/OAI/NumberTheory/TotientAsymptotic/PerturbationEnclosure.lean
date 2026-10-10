import OAI.NumberTheory.TotientAsymptotic.AdditiveShellUnion

namespace OAI

/-! The difference between the perturbed and exact witness regions lies
in the retained full-dimensional slack slices. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_perturbedTailPrefixRegion (x : ℝ) (H : ℕ) (η : TailDatum H) :
    MeasurableSet (perturbedTailPrefixRegion x H η) := by
  unfold perturbedTailPrefixRegion
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (by fun_prop))
  · exact measurableSet_le (by fun_prop) measurable_const

lemma joined_witness_prefixLinear {x : ℝ} {H : ℕ} (η : TailDatum H)
    (hPH : P H ≤ H) (hHm : H ≤ m x) (u : Fin (R x H) → ℝ) (i : Fin (R x H)) :
    prefixLinear (R x H+(H-P H))
      (joinCoordinates (R x H) (H-P H) (u,tailVector η)) (Fin.castAdd (H-P H) i) =
      prefixLinear (R x H) u i-D (m x-(i.val+1)) η := by
  simp only [prefixLinear_apply, Fin.val_castAdd, joinCoordinates_left]
  rw [joined_prefix_row, ← prefix_D_tailVector η hPH hHm]
  ring

lemma row_cube_error_le_boxSlack {x : ℝ} {N : ℕ} (hN : N < m x) (i : Fin N) :
    ((N-i.val : ℕ) : ℝ)^2 ≤ boxSlackError x (i.val+1) := by
  have hi := i.isLt
  have hh : ((N-i.val : ℕ) : ℝ) ≤ (m x-(i.val+1) : ℕ) := by
    exact_mod_cast (show N-i.val ≤ m x-(i.val+1) by omega)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (N-i.val) (α := ℝ)) hh 2
  have hp : 0 ≤ (xi x (i.val+1)-1)*((11/10 : ℝ)*bandScale x (i.val+1)) :=
    mul_nonneg (xi_sub_one_pos _ _).le (mul_nonneg (by norm_num) (bandScale_nonneg _ _))
  dsimp [boxSlackError]
  nlinarith [sq_nonneg (((m x-(i.val+1) : ℕ) : ℝ))]

lemma top_cube_error_le_boxTop {x : ℝ} {N : ℕ} (hB : 0 ≤ B x) (hN : N ≤ m x) :
    (N : ℝ)^2 ≤ boxTopError x := by
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg N (α := ℝ))
    (show (N : ℝ) ≤ m x by exact_mod_cast hN) 2
  have ht := topPerturbation_nonneg hB
  dsimp [boxTopError]
  nlinarith [sq_nonneg (m x : ℝ)]

lemma perturbed_loss_enclosure {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hB : 0 ≤ B x) (hP : 1 ≤ P H) (hPH : P H < H) (hHm : H ≤ m x)
    (hη : IsWitness H (theta x) η)
    {u : Fin (R x H) → ℝ}
    (hu : u ∈ (perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \
      tailPrefixRegion x H η)
    {v : Fin (H-P H) → ℝ} (hv : ∀ i, |tailVector η i-v i| ≤ 1) :
    joinCoordinates (R x H) (H-P H) (u,v) ∈
      additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _) := by
  let z := joinCoordinates (R x H) (H-P H) (u,tailVector η)
  let y := joinCoordinates (R x H) (H-P H) (u,v)
  have hN : R x H+(H-P H) < m x := by unfold R; omega
  have hz := join_witness_perturbed_enlarged hη hPH hHm hu.1.1 hu.1.2
  have hb := join_witness_band_upper hη hPH.le hHm hu.1.2
  have hd : ∀ i, |z i-y i| ≤ 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [z, y, joinCoordinates_left]
    · simpa only [z, y, joinCoordinates_right] using hv j
  have hy : y ∈ additiveBoxSimplex x (R x H+(H-P H)) :=
    banded_simplex_cube_additive hN hz hb hd
  change y ∈ _
  by_cases htop : (∑ i, a (i.val+1)*u i) ≤ B x-D (m x) η
  · have hfail : ∃ i, prefixLinear (R x H) u i < D (m x-(i.val+1)) η := by
      by_contra! hall
      exact hu.2 ⟨hall, htop⟩
    obtain ⟨i, hi⟩ := hfail
    have he : Fin.castLE (Nat.le_add_right (R x H) (H-P H)) i =
        Fin.castAdd (H-P H) i := Fin.ext rfl
    have hzneg : prefixLinear (R x H+(H-P H)) z (Fin.castAdd (H-P H) i) < 0 := by
      rw [joined_witness_prefixLinear η hPH.le hHm]
      linarith
    have hdiff := (neg_le_abs _).trans (prefixLinear_cube_error z y hd (Fin.castAdd (H-P H) i))
    have hrow := row_cube_error_le_boxSlack hN (Fin.castAdd (H-P H) i)
    have hstrict : prefixLinear (R x H+(H-P H)) y (Fin.castAdd (H-P H) i) <
        boxSlackError x (i.val+1) := by
      simp only [Fin.val_castAdd] at hrow hdiff
      linarith
    apply Or.inr
    refine Set.mem_iUnion.mpr ⟨i, hy, ?_⟩
    intro hgood
    have hh := hgood.1 (Fin.castLE (Nat.le_add_right _ _) i)
    rw [raiseThreshold, Function.update_self, he] at hh
    simp only [Fin.val_castAdd] at hh
    linarith
  · apply Or.inl
    refine ⟨hy, ?_⟩
    intro hgood
    have hzgt : B x < ∑ j, a (j.val+1)*z j := by
      dsimp [z]
      rw [joined_budget, ← top_D_tailVector η hPH.le hHm]
      linarith
    have hdiff := (le_abs_self _).trans (prefixBudget_cube_error z y hd)
    have herr := top_cube_error_le_boxTop hB hN.le
    have hh := hgood.2
    linarith

end TotientAsymptotic

end

end OAI
