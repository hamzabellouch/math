import OAI.Analysis.SeparableQuotients.BlockApproximation

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical
variable {f : Family} (z : BlockSequence f)

lemma BlockSequence.blockProjection_embed (n j : ℕ) :
    intervalProjection (ordinalHull (z.vector n).support (Finsupp.support_nonempty_iff.mpr (z.nonzero n)))
      (ordinalHull_connected _ _) (z.embed j) = if j = n then z.embed n else 0 := by
  by_cases hj : j = n
  · subst j
    rw [ite_eq_left rfl]
    exact intervalProjection_fixed _ _ _ (fun _ ha => mem_ordinalHull _ ha)
  · rw [ite_eq_right hj]
    apply intervalProjection_eq_zero
    intro a ha haI
    rcases lt_or_gt_of_ne hj with hj | hj
    · have hlt := (z.successive j n hj a ha _ ((z.vector n).support.min'_mem (Finsupp.support_nonempty_iff.mpr (z.nonzero n)))).1
      exact (not_lt_of_ge haI.1) hlt
    · have hlt := (z.successive n j hj _ ((z.vector n).support.max'_mem (Finsupp.support_nonempty_iff.mpr (z.nonzero n))) a ha).1
      exact (not_lt_of_ge haI.2) hlt

lemma BlockSequence.coefficient_bound (hz : ∀ n, (1/2 : ℝ) ≤ ‖z.embed n‖)
    (c : ℕ →₀ ℝ) (n : ℕ) : |c n| ≤ 4*‖c.sum (fun i a => a • z.embed i)‖ := by
  let P := intervalProjection
    (ordinalHull (z.vector n).support (Finsupp.support_nonempty_iff.mpr (z.nonzero n)))
      (ordinalHull_connected _ _)
  have he : P (c.sum (fun i a => a • z.embed i)) = c n • z.embed n := by
    rw [Finsupp.sum,map_sum]
    simp only [map_smul,P,BlockSequence.blockProjection_embed]
    by_cases hn : n ∈ c.support
    · rw [Finset.sum_eq_single_of_mem n hn]
      · simp
      · intro j _ hj
        simp [hj]
    · have hc : c n = 0 := Finsupp.notMem_support_iff.mp hn
      rw [hc,zero_smul]
      apply Finset.sum_eq_zero
      intro j hj
      have hjn : j ≠ n := fun hh => hn (hh ▸ hj)
      simp [hjn]
  have hp : ‖P (c.sum (fun i a => a • z.embed i))‖ ≤ ‖c.sum (fun i a => a • z.embed i)‖ :=
    norm_projection_le _ _
  rw [he,norm_smul,Real.norm_eq_abs] at hp
  have := mul_le_mul_of_nonneg_left (hz n) (abs_nonneg (c n))
  nlinarith [norm_nonneg (c.sum (fun i a => a • z.embed i))]

/-- The small-perturbation inequality for finite block combinations. -/
lemma BlockSequence.finite_perturbation (hz : ∀ n, (1/2 : ℝ) ≤ ‖z.embed n‖)
    (h : ℕ → E) (ε : ℕ → ℝ) (_hε : ∀ n, 0 ≤ ε n)
    (he : ∀ n, ‖h n-z.embed n‖ ≤ ε n) (B : ℝ)
    (hs : ∀ s : Finset ℕ, ∑ n ∈ s, ε n ≤ B) (c : ℕ →₀ ℝ) :
    ‖c.sum (fun i a => a • h i) - c.sum (fun i a => a • z.embed i)‖ ≤
      (4*B)*‖c.sum (fun i a => a • z.embed i)‖ := by
  let x := c.sum (fun i a => a • z.embed i)
  calc
    _ = ‖∑ i ∈ c.support, c i • (h i-z.embed i)‖ := by
      congr 1
      simp only [Finsupp.sum,smul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ c.support, |c i| *‖h i-z.embed i‖ := by
      simpa only [norm_smul,Real.norm_eq_abs] using
        norm_sum_le c.support (fun i => c i • (h i-z.embed i))
    _ ≤ ∑ i ∈ c.support, (4*‖x‖)*ε i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (z.coefficient_bound hz c i) (he i) (norm_nonneg _) (by positivity)
    _ = (4*‖x‖)*(∑ i ∈ c.support, ε i) := (Finset.mul_sum _ _ _).symm
    _ ≤ (4*‖x‖)*B := mul_le_mul_of_nonneg_left (hs c.support) (by positivity)
    _ = _ := by ring

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology
variable {F : Submodule ℝ E} (R : BranchReduction F)

lemma evaluateArray_familyP (γ : Cut) (f : Family) (x : E) (d : Array)
    (ho : ∀ a ∈ d.support, (a : Cut) < γ)
    (hc : ∀ k, f = .pure k → ∀ a ∈ d.support, Colors.color a = k) :
    norming.evaluateArray (familyP γ f x) d = norming.evaluateArray x d := by
  simp only [norming.evaluateArray_eq]
  apply Finset.sum_congr rfl
  intro a ha
  cases hf : f with
  | mixed => simp only [familyP,coordinate_initialP,ho a ha,ite_true]
  | pure k =>
    simp only [familyP,ContinuousLinearMap.comp_apply,coordinate_colorP,coordinate_initialP,
      ho a ha,hc k hf a ha,ite_true]

namespace BlockApprox

lemma pair_below (i : ℕ) (a : Γ)
    (ha : a ∈ (TreeNode.node (blocks R) i).pair.piece.value.support) :
    (a : Cut) < R.cut := by
  let e := (TreeNode.node (blocks R) i).pair
  have hα : a ∈ (vectorCrop e.vector e.nonzero).ordinal := by
    have h := e.support a ha
    have hh (A : Crop) (f : Family) (hb : a ∈ A.set f) : a ∈ A.ordinal := by
      cases f with
      | pure k => exact hb
      | mixed => exact hb.1
    exact hh _ _ h
  have hb := (blocks R).support_mem_tail _ e.mem_tail
    ((e.vector.support.max'_mem (Finsupp.support_nonempty_iff.mpr e.nonzero)))
  obtain ⟨n,_,hn⟩ := hb
  exact (WithTop.coe_le_coe.mpr hα.2).trans_lt (blocks_below R n _ hn)

lemma pair_color (k : ℕ) (hk : R.family = .pure k) (i : ℕ) (a : Γ)
    (ha : a ∈ (TreeNode.node (blocks R) i).pair.piece.value.support) : Colors.color a = k := by
  have hm := (TreeNode.node (blocks R) i).pair.piece.mem_family
    (TreeNode.node (blocks R) i).pair.child_mem
  have hp : (TreeNode.node (blocks R) i).pair.piece.value ∈ Norming.Pure k := by
    simpa only [hk,Family.norming,Family.base,Norming.Pure] using hm
  by_contra hn
  exact Finsupp.mem_support_iff.mp ha (pure_vanish k _ hp a hn)

lemma pathPartial_familyP (b : ℕ → Bool) (n : ℕ) (x : E) :
    pathPartial (TreeNode.branchPath (blocks R) b) n (familyP R.cut R.family x) =
      pathPartial (TreeNode.branchPath (blocks R) b) n x := by
  simp only [pathPartial,← norming.evaluateArray_eq_functional]
  change norming.evaluateArray _ (∑ j : Fin (n+1), (TreeNode.node (blocks R) (BinaryNodes.branch b j)).pair.piece.value) =
    norming.evaluateArray _ (∑ j : Fin (n+1), (TreeNode.node (blocks R) (BinaryNodes.branch b j)).pair.piece.value)
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact evaluateArray_familyP R.cut R.family x _ (pair_below R _) (fun k hk => pair_color R k hk _)

lemma pathFunctional_familyP (b : ℕ → Bool) (x : E) :
    pathFunctional (TreeNode.branchPath (blocks R) b) (familyP R.cut R.family x) =
      pathFunctional (TreeNode.branchPath (blocks R) b) x :=
  tendsto_nhds_unique (pathPartial_tendsto _ _) ((pathPartial_tendsto _ x).congr
    (fun n => (pathPartial_familyP R b n x).symm))

lemma pair_coefficients (i : ℕ) : ∃ c : ℕ →₀ ℝ,
    c.sum (fun n a => a • (blocks R).embed n) =
      norming.includeFinite (TreeNode.node (blocks R) i).pair.vector := by
  have hm := (blocks R).tailSpan_mono (Nat.zero_le _) (TreeNode.node (blocks R) i).pair.mem_tail
  change _ ∈ Submodule.span ℝ (Set.range (fun n => (blocks R).vector (n+0))) at hm
  simp only [Nat.add_zero] at hm
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  refine ⟨c,?_⟩
  rw [← hc]
  simp only [Finsupp.sum,map_sum,map_smul,BlockSequence.embed]

lemma pair_approximation (i : ℕ) : ∃ h : R.H,
    ‖h‖ ≤ 501 ∧
      ‖(h : E)-norming.includeFinite (TreeNode.node (blocks R) i).pair.vector‖ ≤ 1/16 := by
  obtain ⟨c,hc⟩ := pair_coefficients R i
  let h : R.H := c.sum (fun n a => a • (node R n).x)
  have he : ‖(h : E)-norming.includeFinite (TreeNode.node (blocks R) i).pair.vector‖ ≤ 1/16 := by
    have hp := (blocks R).finite_perturbation (blocks_norm R)
      (fun n => ((node R n).x : E)) error (fun n => (error_pos n).le)
      (fun n => (node R n).approx.le) (1/32000) error_sum c
    have hh : (h : E) = c.sum (fun n a => a • ((node R n).x : E)) := by
      simp only [h,Finsupp.sum,Submodule.coe_sum,Submodule.coe_smul_of_tower]
    rw [← hh,hc] at hp
    have hn := (TreeNode.node (blocks R) i).pair.norm_le
    linarith
  refine ⟨h,?_,he⟩
  have ht := norm_le_norm_sub_add ((h : E)) (norming.includeFinite (TreeNode.node (blocks R) i).pair.vector)
  have hn := (TreeNode.node (blocks R) i).pair.norm_le
  change ‖(h : E)‖ ≤ 501
  linarith

lemma separated_on_reduction {b c : ℕ → Bool} (hbc : b ≠ c) :
    ∃ h : R.H, ‖h‖ ≤ 501 ∧ 1/4 ≤
      pathFunctional (TreeNode.branchPath (blocks R) b) (h : E) -
      pathFunctional (TreeNode.branchPath (blocks R) c) (h : E) := by
  obtain ⟨n,hn⟩ := BinaryNodes.exists_separating_node hbc
  let i := BinaryNodes.branch b n
  let y := norming.includeFinite (TreeNode.node (blocks R) i).pair.vector
  obtain ⟨h,hh,he⟩ := pair_approximation R i
  let P := pathFunctional (TreeNode.branchPath (blocks R) b)
  let Q := pathFunctional (TreeNode.branchPath (blocks R) c)
  have hy : 1/2 ≤ P y - Q y := by
    rw [show Q y = 0 from TreeNode.pathFunctional_other (blocks R) c _ (fun j => (hn j).symm),sub_zero]
    exact TreeNode.pathFunctional_node (blocks R) b n
  have hb : ‖P ((h : E)-y)‖ ≤ 1/16 := by
    exact (P.le_opNorm _).trans ((mul_le_mul (norm_pathFunctional_le _) he (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hc : ‖Q ((h : E)-y)‖ ≤ 1/16 := by
    exact (Q.le_opNorm _).trans ((mul_le_mul (norm_pathFunctional_le _) he (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  rw [map_sub,Real.norm_eq_abs] at hb hc
  refine ⟨h,hh,?_⟩
  change 1/4 ≤ P (h : E)-Q (h : E)
  have hb' := (abs_le.mp hb).1
  have hc' := (abs_le.mp hc).2
  linarith

/-- Uniformly separated path restrictions on an arbitrary closed infinite-dimensional subspace. -/
theorem restricted_separated {b c : ℕ → Bool} (hbc : b ≠ c) :
    (1/(2004*(‖R.U‖+1)) : ℝ) ≤
      ‖(pathFunctional (TreeNode.branchPath (blocks R) b)).comp F.subtypeL -
        (pathFunctional (TreeNode.branchPath (blocks R) c)).comp F.subtypeL‖ := by
  obtain ⟨h,hh,he⟩ := separated_on_reduction R hbc
  let T := (pathFunctional (TreeNode.branchPath (blocks R) b)).comp F.subtypeL -
    (pathFunctional (TreeNode.branchPath (blocks R) c)).comp F.subtypeL
  have hb (b : ℕ → Bool) : pathFunctional (TreeNode.branchPath (blocks R) b) (h : E) =
      pathFunctional (TreeNode.branchPath (blocks R) b) (R.U h : E) := by
    rw [← R.lift h,pathFunctional_familyP]
  rw [hb b,hb c] at he
  have hn : ‖R.U h‖ ≤ ‖R.U‖*501 := (R.U.le_opNorm h).trans (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
  have hop := (T.le_opNorm (R.U h)).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg T))
  have he' : 1/4 ≤ T (R.U h) := he
  rw [Real.norm_eq_abs] at hop
  have hp := le_abs_self (T (R.U h))
  have hd : 0 < 2004*(‖R.U‖+1) := by positivity
  apply (div_le_iff₀ hd).mpr
  change 1 ≤ ‖T‖*(2004*(‖R.U‖+1))
  nlinarith [norm_nonneg T]

end BlockApprox
end SeparableQuotient.ActualSpace

end

end OAI
