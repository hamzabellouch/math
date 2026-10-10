import OAI.NumberTheory.DukePrimeDegree.Geometry.RootHorosphereGroup
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingDiagonal

namespace OAI

/-!
# Diagonal normalization and contraction of the root horosphere

The closed group of shearing limits is normalized by the diagonal
group, and the two-coordinate shearing diagonal contracts it. These
are the group facts needed to construct its conditional measures.
-/

noncomputable section
open Set Filter Matrix
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootHorosphereShape_diagonal_conjugate
    {n : ℕ} {i j : Fin n} (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0)
    (g : G n) (hg : RootHorosphereShape i j g) (t : ℝ) :
    RootHorosphereShape i j
      (diagonalOneParameter ell hell t * g * diagonalOneParameter ell hell (-t)) := by
  intro r s hrs
  rw [conjugation_entry, hg r s hrs]
  by_cases h : r = s
  · subst s
    simp
  · simp [h]

theorem rootHorosphereShape_transvection
    {n : ℕ} {i j a b : Fin n} (hab : a ≠ b) (ha : a = i ∨ b = j) (t : ℝ) :
    RootHorosphereShape i j (Matrix.SpecialLinearGroup.transvection hab t) := by
  intro r s hrs
  by_cases hra : r = a <;> by_cases hsb : s = b
  · subst r; subst s
    rcases hrs with hrs | heq
    · rcases ha with ha | hb
      · exact (hrs.1 ha).elim
      · exact (hrs.2 hb).elim
    · exact (hab heq).elim
  all_goals simp_all [Matrix.SpecialLinearGroup.transvection_coe, eq_comm]

theorem rootHorosphere_tendsto_one
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hg : RootHorosphereShape i j g) :
    Tendsto (fun t : ℝ => rootPairConjugate i j t g) atTop (𝓝 1) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro s
  have hentry (t : ℝ) : (rootPairConjugate i j t g).val r s =
      Real.exp ((rootPairWeights i j r - rootPairWeights i j s) * t) * g.val r s := by
    simp only [rootPairConjugate, rootPairFlow, conjugation_entry]
  simp_rw [hentry]
  by_cases hrs : r = s
  · subst s
    have hdiag := hg r r (Or.inr rfl)
    simp only [sub_self, zero_mul, Real.exp_zero, one_mul, hdiag]
    change Tendsto (fun _ : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) r r)
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) r r))
    exact tendsto_const_nhds
  have hone : (1 : G n).val r s = 0 := by simp [Matrix.SpecialLinearGroup.coe_one, hrs]
  rw [hone]
  by_cases hri : r = i
  · subst r
    by_cases hsj : s = j
    · subst s
      have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id)
      have h := ht.mul_const (g.val i j)
      simpa only [Function.comp_def, id_eq, rootPairWeights_row hij, rootPairWeights_col hij,
        show (-1 : ℝ) - 1 = -2 by norm_num, neg_mul, zero_mul] using h
    · have hsi : s ≠ i := Ne.symm hrs
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (g.val i s)
      simpa only [rootPairWeights_row hij, rootPairWeights_other hsi hsj,
        sub_zero, neg_one_mul, zero_mul] using h
  · by_cases hsj : s = j
    · subst s
      have hrj : r ≠ j := hrs
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (g.val r j)
      simpa only [rootPairWeights_other hri hrj, rootPairWeights_col hij,
        zero_sub, neg_one_mul, zero_mul] using h
    · have hzero : g.val r s = 0 := by
        simpa only [Matrix.one_apply, hrs, ite_false] using hg r s (Or.inl ⟨hri, hsj⟩)
      simp only [hzero, mul_zero]
      exact tendsto_const_nhds

end DukePrimeDegree

end

end OAI
