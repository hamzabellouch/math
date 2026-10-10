import OAI.NumberTheory.DukePrimeDegree.Geometry.RootWeights
import OAI.NumberTheory.DukePrimeDegree.Dynamics.HopfTranslationOrbits

namespace OAI

/-!
# Contraction of root pairs under neutral diagonal flows

The acting root group is the additive real line. If a diagonal direction
expands the corresponding root character, forward right translation
contracts the relative root parameter. This supplies the geometric
hypothesis of the Hopf lemma even when the orbit leaves compact sets.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The real root group acts on the lattice space by right translation. -/
@[instance_reducible] def rootTranslationAction {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MulAction (Multiplicative ℝ) (X n) where
  smul t x := rightAction x (Matrix.SpecialLinearGroup.transvection hij t.toAdd)
  one_smul x := by
    change rightAction x (Matrix.SpecialLinearGroup.transvection hij 0) = x
    simp
  mul_smul t u x := by
    change rightAction x (Matrix.SpecialLinearGroup.transvection hij (t.toAdd + u.toAdd)) =
      rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij u.toAdd))
        (Matrix.SpecialLinearGroup.transvection hij t.toAdd)
    rw [rightAction_mul, ← Matrix.SpecialLinearGroup.transvection_add, add_comm]

lemma rootTranslationAction_continuous {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    let := rootTranslationAction hij
    ContinuousSMul (Multiplicative ℝ) (X n) := by
  let := rootTranslationAction hij
  constructor
  have hu : Continuous (fun t : Multiplicative ℝ =>
      Matrix.SpecialLinearGroup.transvection hij t.toAdd) := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro r
    apply continuous_pi
    intro s
    change Continuous (fun t : Multiplicative ℝ => Matrix.transvection i j t.toAdd r s)
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  exact (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk (hu.comp continuous_fst))

lemma root_pair_diagonal_translate {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (x : X n) (s t : ℝ) :
    rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij s))
      (diagonalOneParameter ell hell t) =
    rightAction (rightAction x (diagonalOneParameter ell hell t))
      (Matrix.SpecialLinearGroup.transvection hij (Real.exp ((ell j - ell i) * t) * s)) := by
  rw [rightAction_mul, rightAction_mul]
  congr 1
  have hc := diagonal_conjugation_transvection ell hell hij s (-t)
  rw [neg_neg] at hc
  have he : (ell i - ell j) * -t = (ell j - ell i) * t := by ring
  rw [he] at hc
  calc
    _ = diagonalOneParameter ell hell t *
        (diagonalOneParameter ell hell (-t) *
          Matrix.SpecialLinearGroup.transvection hij s * diagonalOneParameter ell hell t) := by
      rw [diagonalOneParameter_neg]
      simp [mul_assoc]
    _ = _ := by rw [hc]

lemma diagonal_right_iterate {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0)
    (m : ℕ) (x : X n) :
    (fun y => rightAction y (diagonalOneParameter ell hell 1))^[m] x =
      rightAction x (diagonalOneParameter ell hell (m : ℝ)) := by
  induction m with
  | zero => simp [diagonalOneParameter_zero]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, rightAction_mul,
      ← diagonalOneParameter_add, Nat.cast_add, Nat.cast_one]

/-- With root weight one, the relative root parameter decays exponentially. -/
lemma root_parameter_contracts {n : ℕ} {i j : Fin n}
    (ell : Fin n → ℝ) (hweight : ell i - ell j = 1) (s : ℝ) :
    Tendsto (fun m : ℕ =>
      Multiplicative.ofAdd (Real.exp ((ell j - ell i) * (m : ℝ)) * s))
      atTop (𝓝 1) := by
  have hneg : ell j - ell i = -1 := by linarith
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).mul_const s
  apply (show Continuous (Multiplicative.ofAdd : ℝ → Multiplicative ℝ) from continuous_id).tendsto 0 |>.comp
  simpa only [hneg, neg_one_mul, zero_mul, Function.comp_apply] using h

end DukePrimeDegree

end

end OAI
