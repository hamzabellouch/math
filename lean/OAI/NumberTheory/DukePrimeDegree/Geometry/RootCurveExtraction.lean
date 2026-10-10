import OAI.NumberTheory.DukePrimeDegree.Dynamics.ConnectedBlockContainment
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-!
# Extracting a root from a differentiable curve

A diagonal with a unique maximal root rescales a curve at the identity.
Its limit is the elementary matrix given by that root component of the
velocity. Closedness then puts this actual root element in the subgroup.
This is a direct matrix argument, with no Lie-subgroup classification.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def rootIsolationWeights {n : ℕ} (i j : Fin n) (a : Fin n) : ℝ :=
  (if a = i then 1 else 0) - (if a = j then 1 else 0)

lemma rootIsolationWeights_sum {n : ℕ} (i j : Fin n) :
    ∑ a, rootIsolationWeights i j a = 0 := by
  simp [rootIsolationWeights, Finset.sum_sub_distrib]

lemma rootIsolationWeights_peak {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    rootIsolationWeights i j i - rootIsolationWeights i j j = 2 := by
  norm_num [rootIsolationWeights, hij, Ne.symm hij]

lemma rootIsolationWeights_lt_peak {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (a b : Fin n) (hab : ¬ (a = i ∧ b = j)) :
    rootIsolationWeights i j a - rootIsolationWeights i j b < 2 := by
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j
  all_goals simp_all [rootIsolationWeights] <;> norm_num

lemma diagonal_conjugate_matrix_entry {n : ℕ} (ell : Fin n → ℝ)
    (hsum : ∑ a, ell a = 0) (t : ℝ) (g : G n) (a b : Fin n) :
    (diagonalOneParameter ell hsum t * g *
      diagonalOneParameter ell hsum (-t)).val a b =
        Real.exp ((ell a - ell b) * t) * g.val a b := by
  exact conjugation_entry ell hsum g t a b

/-- Entrywise velocity at the identity; the parameter approaches zero
through positive real values, exactly as in the rescaling argument. -/
def HasMatrixVelocity {n : ℕ} (γ : ℝ → G n)
    (V : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ a b, Tendsto (fun t : ℝ => ((γ t).val a b - (1 : Matrix (Fin n) (Fin n) ℝ) a b) / t)
    (𝓝[>] 0) (𝓝 (V a b))

lemma hasMatrixVelocity_of_hasDerivAt {n : ℕ} (γ : ℝ → G n)
    (hzero : γ 0 = 1) (V : Matrix (Fin n) (Fin n) ℝ)
    (hderiv : ∀ a b, HasDerivAt (fun t => (γ t).val a b) (V a b) 0) :
    HasMatrixVelocity γ V := by
  intro a b
  have he := (hderiv a b).tendsto_slope_zero_right
  simpa only [zero_add, hzero, Matrix.SpecialLinearGroup.coe_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using he

/-- Rescaling isolates a single root component of a curve's velocity. -/
theorem tendsto_diagonal_rescale_curve {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (γ : ℝ → G n)
    (V : Matrix (Fin n) (Fin n) ℝ) (hvelocity : HasMatrixVelocity γ V) :
    Tendsto (fun m : ℕ =>
      diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j) (m : ℝ) *
        γ (Real.exp (-2 * (m : ℝ))) *
        diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j) (-(m : ℝ)))
      atTop (𝓝 (Matrix.SpecialLinearGroup.transvection hij (V i j))) := by
  let ell := rootIsolationWeights i j
  let τ : ℕ → ℝ := fun m => Real.exp (-2 * (m : ℝ))
  have hτ : Tendsto τ atTop (𝓝[>] 0) :=
    Real.tendsto_exp_atBot_nhdsGT.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by norm_num))
  have hslope (a b : Fin n) : Tendsto
      (fun m => ((γ (τ m)).val a b - (1 : Matrix (Fin n) (Fin n) ℝ) a b) / τ m)
      atTop (𝓝 (V a b)) := (hvelocity a b).comp hτ
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  let c := ell a - ell b - 2
  have hentry (m : ℕ) :
      (diagonalOneParameter ell (rootIsolationWeights_sum i j) (m : ℝ) *
        γ (τ m) * diagonalOneParameter ell (rootIsolationWeights_sum i j) (-(m : ℝ))).val a b =
      (1 : Matrix (Fin n) (Fin n) ℝ) a b + Real.exp (c * (m : ℝ)) *
        (((γ (τ m)).val a b - (1 : Matrix (Fin n) (Fin n) ℝ) a b) / τ m) := by
    rw [diagonal_conjugate_matrix_entry]
    have he : Real.exp (c * (m : ℝ)) / τ m = Real.exp ((ell a - ell b) * (m : ℝ)) := by
      dsimp [τ]
      rw [← Real.exp_sub]
      congr 1
      dsimp [c]
      ring
    have hbase : Real.exp ((ell a - ell b) * (m : ℝ)) *
        (1 : Matrix (Fin n) (Fin n) ℝ) a b = (1 : Matrix (Fin n) (Fin n) ℝ) a b := by
      by_cases hab : a = b
      · subst b
        simp
      · simp [Matrix.one_apply_ne hab]
    calc
      _ = Real.exp ((ell a - ell b) * (m : ℝ)) * (1 : Matrix (Fin n) (Fin n) ℝ) a b +
          Real.exp ((ell a - ell b) * (m : ℝ)) *
            ((γ (τ m)).val a b - (1 : Matrix (Fin n) (Fin n) ℝ) a b) := by ring
      _ = _ := by rw [hbase, ← he]; ring
  suffices H : Tendsto (fun m : ℕ =>
      (1 : Matrix (Fin n) (Fin n) ℝ) a b + Real.exp (c * (m : ℝ)) *
        (((γ (τ m)).val a b - (1 : Matrix (Fin n) (Fin n) ℝ) a b) / τ m))
      atTop (𝓝 ((Matrix.SpecialLinearGroup.transvection hij (V i j)).val a b)) by
    exact H.congr' (Filter.Eventually.of_forall (fun m => (hentry m).symm))
  by_cases hpeak : a = i ∧ b = j
  · obtain ⟨hai, hbj⟩ := hpeak
    subst a
    subst b
    have hc : c = 0 := by dsimp [c, ell]; rw [rootIsolationWeights_peak i j hij]; norm_num
    simpa [hc, Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection,
      Matrix.one_apply_ne hij] using hslope i j
  · have hc : c < 0 := sub_neg.mpr (rootIsolationWeights_lt_peak i j hij a b hpeak)
    have hdecay : Tendsto (fun m : ℕ => Real.exp (c * (m : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hc)
    have hpeak' : ¬ (i = a ∧ j = b) := by
      rintro ⟨hia, hjb⟩
      exact hpeak ⟨hia.symm, hjb.symm⟩
    have hlim := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (1 : Matrix (Fin n) (Fin n) ℝ) a b) atTop
      (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) a b))).add (hdecay.mul (hslope a b))
    simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection,
      Matrix.single_apply, hpeak', zero_mul, add_zero] using hlim

/-- A closed subgroup normalized by all split diagonals contains each
root component isolated from one of its curves at the identity. -/
theorem root_mem_of_matrix_velocity {n : ℕ}
    (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (hnormal : ∀ (ell : Fin n → ℝ) (hsum : ∑ a, ell a = 0) (t : ℝ),
      ∀ g ∈ L, diagonalOneParameter ell hsum t * g * diagonalOneParameter ell hsum (-t) ∈ L)
    (γ : ℝ → G n) (hγ : ∀ t, γ t ∈ L)
    (V : Matrix (Fin n) (Fin n) ℝ) (hvelocity : HasMatrixVelocity γ V)
    (i j : Fin n) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.transvection hij (V i j) ∈ L := by
  apply hclosed.mem_of_tendsto (tendsto_diagonal_rescale_curve i j hij γ V hvelocity)
  exact Filter.Eventually.of_forall fun m => hnormal _ _ _ _ (hγ _)

end DukePrimeDegree

end

end OAI
