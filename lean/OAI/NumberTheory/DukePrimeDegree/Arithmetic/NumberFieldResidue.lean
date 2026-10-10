import Mathlib.NumberTheory.NumberField.DedekindZeta
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ResidueComparison

namespace OAI

/-!
# The regularized Dedekind zeta function

The analytic class number formula gives a positive residue and the
one-sided limit of the regularized Dedekind zeta function at its pole.
-/

open Filter Set
open scoped Topology

namespace DukePrimeDegree

variable (K : Type*) [Field K] [NumberField K]

/-- The real regularized zeta function, filled in at its pole by the
positive class-number-formula residue. -/
noncomputable def regularizedZeta (σ : ℝ) : ℝ :=
  if σ = 1 then NumberField.dedekindZeta_residue K
  else (σ - 1) * (NumberField.dedekindZeta K σ).re

@[simp] lemma regularizedZeta_one :
    regularizedZeta K 1 = NumberField.dedekindZeta_residue K := by
  simp [regularizedZeta]

lemma regularizedZeta_one_pos : 0 < regularizedZeta K 1 := by
  simpa using NumberField.dedekindZeta_residue_pos K

lemma regularizedZeta_of_ne_one {σ : ℝ} (hσ : σ ≠ 1) :
    regularizedZeta K σ = (σ - 1) * (NumberField.dedekindZeta K σ).re := by
  simp [regularizedZeta, hσ]

/-- Continuity at the residue from the half-plane of absolute convergence. -/
lemma regularizedZeta_continuousWithinAt_one :
    ContinuousWithinAt (regularizedZeta K) (Ioi 1) 1 := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  change Tendsto (regularizedZeta K) (𝓝[>] 1) (𝓝 (regularizedZeta K 1))
  rw [regularizedZeta_one]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [regularizedZeta_of_ne_one K (ne_of_gt hσ)]
  simp

end DukePrimeDegree

end OAI
