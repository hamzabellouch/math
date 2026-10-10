import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Module.Submodule.Basic

namespace OAI

/-!
# The homogeneous space and diagonal flow

We use the column-lattice convention `SL(n,ℝ) / SL(n,ℤ)`. Inversion
identifies this with the manuscript's row-lattice convention
`SL(n,ℤ) \ SL(n,ℝ)` and turns right diagonal translations into left
translations by the inverse. No packet or Haar probability is assumed
to have been constructed by these definitions.
-/

open Matrix MeasureTheory
open scoped BigOperators

namespace DukePrimeDegree

abbrev RealSL (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) ℝ

instance (n : ℕ) : SecondCountableTopology (RealSL n) := by
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.isInducing.secondCountableTopology

/-- The integer special linear group inside the real group. -/
def integralSL (n : ℕ) : Subgroup (RealSL n) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).range

instance integralSL_closed (n : ℕ) : IsClosed (integralSL n : Set (RealSL n)) := by
  change IsClosed (Set.range (Matrix.SpecialLinearGroup.map (n := Fin n) (Int.castRingHom ℝ)))
  exact Int.isClosedEmbedding_coe_real.specialLinearGroup_map.isClosed_range

/-- The unimodular lattice space, with its quotient topology. -/
abbrev LatticeSpace (n : ℕ) := RealSL n ⧸ integralSL n

instance (n : ℕ) : MeasurableSpace (LatticeSpace n) := borel (LatticeSpace n)

instance (n : ℕ) : BorelSpace (LatticeSpace n) := ⟨rfl⟩

instance (n : ℕ) : T2Space (LatticeSpace n) := inferInstance

instance (n : ℕ) : SecondCountableTopology (LatticeSpace n) := inferInstance

/-- Deleted-log-coordinate-free parametrization of the positive diagonal group. -/
def diagonalParameters (n : ℕ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {u | ∑ i, u i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq] at hu hv ⊢
    simpa only [Pi.add_apply, Finset.sum_add_distrib, hu, hv] using (zero_add (0 : ℝ))
  smul_mem' := by
    intro a u hu
    change ∑ i, a * u i = 0
    rw [← Finset.mul_sum, hu, mul_zero]

/-- The determinant-one exponential diagonal matrix. -/
noncomputable def diagonalExp {n : ℕ} (u : diagonalParameters n) : RealSL n :=
  ⟨Matrix.diagonal (fun i => Real.exp (u.val i)), by
    rw [Matrix.det_diagonal, ← Real.exp_sum, u.property, Real.exp_zero]⟩

@[simp] lemma diagonalExp_zero (n : ℕ) : diagonalExp (0 : diagonalParameters n) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [diagonalExp]

lemma diagonalExp_add {n : ℕ} (u v : diagonalParameters n) :
    diagonalExp (u + v) = diagonalExp u * diagonalExp v := by
  apply Subtype.ext
  change Matrix.diagonal (fun i => Real.exp (u.val i + v.val i)) =
    Matrix.diagonal (fun i => Real.exp (u.val i)) *
      Matrix.diagonal (fun i => Real.exp (v.val i))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.exp_add _ _

/-- The positive diagonal action, encoded as a homomorphism to the ambient group. -/
noncomputable def diagonalHom (n : ℕ) :
    Multiplicative (diagonalParameters n) →* RealSL n where
  toFun u := diagonalExp u.toAdd
  map_one' := diagonalExp_zero n
  map_mul' u v := diagonalExp_add u.toAdd v.toAdd

noncomputable instance (n : ℕ) :
    MulAction (Multiplicative (diagonalParameters n)) (LatticeSpace n) :=
  MulAction.compHom (LatticeSpace n) (diagonalHom n)

/-- Time `t` of the one-parameter diagonal flow associated with `u`. -/
noncomputable def diagonalFlow {n : ℕ} (u : diagonalParameters n)
    (t : ℝ) (x : LatticeSpace n) : LatticeSpace n :=
  diagonalExp (t • u) • x

@[simp] lemma diagonalFlow_zero {n : ℕ} (u : diagonalParameters n)
    (x : LatticeSpace n) : diagonalFlow u 0 x = x := by
  simp [diagonalFlow]

lemma diagonalFlow_add {n : ℕ} (u : diagonalParameters n)
    (s t : ℝ) (x : LatticeSpace n) :
    diagonalFlow u (s + t) x = diagonalFlow u s (diagonalFlow u t x) := by
  simp only [diagonalFlow, add_smul, diagonalExp_add, mul_smul]

lemma continuous_diagonalFlow {n : ℕ} (u : diagonalParameters n) (t : ℝ) :
    Continuous (diagonalFlow u t) := continuous_const_smul _

lemma measurable_diagonalFlow {n : ℕ} (u : diagonalParameters n) (t : ℝ) :
    Measurable (diagonalFlow u t) := (continuous_diagonalFlow u t).measurable

end DukePrimeDegree

end OAI
