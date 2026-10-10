import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDuhamelDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedSemigroup
import Mathlib.Analysis.Calculus.Deriv.Add

namespace OAI

/-! # The generator identity for the constructed linearized flow

This derives the bounded-potential perturbation identity from the actual
finite-slab Duhamel construction. No generator-domain assumption is added.
-/

open Set Filter Topology
open scoped NNReal

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

section

variable (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (m : ℕ) (q : HomogeneousY a k)

local notation "B" => homogeneousLinearizedPotential a k ha ha1 hk m q
local notation "S" => homogeneousLinearizedStep a b k ha ha1 hk m q

noncomputable def homogeneousLinearizedHistory (u : HomogeneousY a k) :
    ℝ → HomogeneousY a k := fun t => B (S t.toNNReal u)

theorem continuous_homogeneousLinearizedHistory (u : HomogeneousY a k) :
    Continuous (homogeneousLinearizedHistory a b k ha ha1 hk m q u) := by
  exact (B).continuous.comp
    (((continuous_homogeneousLinearizedStep_apply a b k ha ha1 hk m q).curry_left (y := u)).comp
      continuous_real_toNNReal)

@[simp] theorem homogeneousLinearizedHistory_zero (u : HomogeneousY a k) :
    homogeneousLinearizedHistory a b k ha ha1 hk m q u 0 = B u := by
  simp only [homogeneousLinearizedHistory, Real.toNNReal_zero,
    homogeneousLinearizedStep_zero, ContinuousLinearMap.id_apply]

theorem homogeneousLinearizedStep_duhamel (t : ℝ≥0) (u : HomogeneousY a k) :
    S t u = homogeneousFreeOperator a b k t ha ha1 hk u +
      homogeneousDuhamel a b k ha ha1 hk t
        (homogeneousLinearizedHistory a b k ha ha1 hk m q u) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.2
  let v := homogeneousLinearizedTrajectory a b k t ha ha1 hk ht m q u
  have hD : homogeneousDuhamel a b k ha ha1 hk t
      (homogeneousPotentialHistory t ht B v) =
      homogeneousDuhamel a b k ha ha1 hk t
        (homogeneousLinearizedHistory a b k ha ha1 hk m q u) := by
    apply homogeneousDuhamel_congr_on a b k t ha ha1 hk ht
    intro s hs
    change B (v (projIcc (0 : ℝ) (t : ℝ) ht s)) = B (S s.toNNReal u)
    rw [projIcc_of_mem ht hs]
    congr 1
    have he := homogeneousLinearizedStep_eq_slab a b k ha ha1 hk m q
      t ht s.toNNReal (by simpa only [Real.coe_toNNReal s hs.1] using hs.2) u
    simpa only [Real.coe_toNNReal s hs.1, v] using he.symm
  calc
    S t u = v ⟨t, ht, le_rfl⟩ :=
      homogeneousLinearizedStep_eq_slab a b k ha ha1 hk m q t ht t le_rfl u
    _ = homogeneousFreeOperator a b k t ha ha1 hk u +
        homogeneousDuhamel a b k ha ha1 hk t
          (homogeneousPotentialHistory t ht B v) :=
      homogeneousLinearizedTrajectory_eq a b k t ha ha1 hk ht m q u _
    _ = _ := congrArg (fun z => homogeneousFreeOperator a b k t ha ha1 hk u + z) hD

/-- Every strong right derivative of the actual flow identifies the free
generator after subtracting the actual linearized potential. -/
theorem homogeneousFree_derivWithin_of_linearized (u v : HomogeneousY a k)
    (hu : HasDerivWithinAt (fun t : ℝ => S t.toNNReal u) v (Ici 0) 0) :
    HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk u)
      (v - B u) (Ici 0) 0 := by
  have hD := (hasDerivAt_homogeneousDuhamel_zero a b k ha ha1 hk
    (homogeneousLinearizedHistory a b k ha ha1 hk m q u)
    (continuous_homogeneousLinearizedHistory a b k ha ha1 hk m q u)).hasDerivWithinAt
      (s := Ici 0)
  rw [homogeneousLinearizedHistory_zero] at hD
  apply (hu.sub hD).congr
  · intro t ht
    have he := homogeneousLinearizedStep_duhamel a b k ha ha1 hk m q t.toNNReal u
    have he' : S t.toNNReal u = homogeneousFreeOperator a b k t ha ha1 hk u +
        homogeneousDuhamel a b k ha ha1 hk t
          (homogeneousLinearizedHistory a b k ha ha1 hk m q u) := by
      simpa only [Real.coe_toNNReal t ht] using he
    exact (eq_sub_iff_add_eq.mpr he'.symm)
  · simp only [homogeneousFreeOperator_zero, Real.toNNReal_zero,
      homogeneousLinearizedStep_zero, ContinuousLinearMap.id_apply,
      Pi.sub_apply, homogeneousDuhamel, intervalIntegral.integral_same, sub_zero]

end

end DefocusingNLS

end OAI
