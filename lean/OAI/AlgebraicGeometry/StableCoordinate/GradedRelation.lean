import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# The exact leading relation for the negative-degree presentation

These lemmas check the elementary input to Section 3 of the source:
`Hstar` has integer weighted degree one for weights `(-1,0,0,1,1)`,
is not divisible by `p`, and none of the five generator classes vanishes
in its principal quotient.  The source polynomial `H` has degree-one
component exactly `Hstar`.  No associated-graded identification is assumed.
-/

noncomputable section
namespace StableCoordinate.Obstruction
variable (k : Type*) [CommRing k]
open MvPolynomial
variable [Nontrivial k]
/-- Reduction at `p=s=u=F=0, J=1` shows `p ∤ Hstar`. -/
theorem p_not_dvd_Hstar : ¬ (X 0 : P k 5) ∣ Hstar k := by
  intro h
  have he := map_dvd (MvPolynomial.eval ![(0:k),0,0,0,1]) h
  simp [Hstar, xP] at he

/-- Each coordinate has a point on `Hstar=0` where it is one. -/
theorem Hstar_not_dvd_X (i : Fin 5) : ¬ Hstar k ∣ (X i : P k 5) := by
  fin_cases i
  · intro h
    have he := map_dvd (MvPolynomial.eval ![(1:k),0,0,0,0]) h
    simp [Hstar, xP] at he
  · intro h
    have he := map_dvd (MvPolynomial.eval ![(0:k),1,0,0,0]) h
    simp [Hstar, xP] at he
  · intro h
    have he := map_dvd (MvPolynomial.eval ![(0:k),0,1,0,0]) h
    simp [Hstar, xP] at he
  · intro h
    have he := map_dvd (MvPolynomial.eval ![(0:k),0,0,1,0]) h
    simp [Hstar, xP] at he
  · intro h
    have he := map_dvd (MvPolynomial.eval ![(-1:k),0,0,0,1]) h
    simp [Hstar, xP] at he

/-- The five named generators in the graded presentation remain nonzero. -/
theorem gX_ne_zero (i : Fin 5) : gX k i ≠ 0 := by
  intro h
  apply Hstar_not_dvd_X k i
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)

end StableCoordinate.Obstruction

namespace StableCoordinate.Obstruction
open MvPolynomial
variable (k : Type*) [CommRing k]

/-- Homogeneity is preserved by subtraction over a ring. -/
theorem weighted_sub {σ : Type*} {w : σ → ℤ} {f g : MvPolynomial σ k} {n : ℤ}
    (hf : f.IsWeightedHomogeneous w n) (hg : g.IsWeightedHomogeneous w n) :
    (f - g).IsWeightedHomogeneous w n :=
  (weightedHomogeneousSubmodule k w n).sub_mem hf hg

/-- The determinant invariant has presentation weight zero. -/
theorem xP_homogeneous : (xP k).IsWeightedHomogeneous presentationWeight 0 := by
  have hp := isWeightedHomogeneous_X k presentationWeight (0 : Fin 5)
  have hs := isWeightedHomogeneous_X k presentationWeight (1 : Fin 5)
  have hu := isWeightedHomogeneous_X k presentationWeight (2 : Fin 5)
  have hF := isWeightedHomogeneous_X k presentationWeight (3 : Fin 5)
  have hs2 : ((X 1 : P k 5)^2).IsWeightedHomogeneous presentationWeight 0 := by
    simpa [presentationWeight] using hs.pow 2
  have hu2 : ((X 2 : P k 5)^2).IsWeightedHomogeneous presentationWeight 0 := by
    simpa [presentationWeight] using hu.pow 2
  have hpF : ((X 0 : P k 5) * X 3).IsWeightedHomogeneous presentationWeight 0 := by
    simpa [presentationWeight] using hp.mul hF
  exact (weighted_sub k hs2 hu2).add hpF

/-- The highest relation is homogeneous of presentation weight one. -/
theorem Hstar_homogeneous : (Hstar k).IsWeightedHomogeneous presentationWeight 1 := by
  have hp := isWeightedHomogeneous_X k presentationWeight (0 : Fin 5)
  have hs := isWeightedHomogeneous_X k presentationWeight (1 : Fin 5)
  have hF := isWeightedHomogeneous_X k presentationWeight (3 : Fin 5)
  have hJ := isWeightedHomogeneous_X k presentationWeight (4 : Fin 5)
  have hx := xP_homogeneous k
  have hfirst : (((xP k)^2) * X 3).IsWeightedHomogeneous presentationWeight 1 := by
    simpa [presentationWeight] using (hx.pow 2).mul hF
  have hmid : ((1 + 2 * X 1 * xP k) * X 4).IsWeightedHomogeneous presentationWeight 1 := by
    have ht : (2 * (X 1 : P k 5) * xP k).IsWeightedHomogeneous presentationWeight 0 := by
      simpa only [map_ofNat, presentationWeight, Matrix.cons_val_one, Matrix.cons_val_zero,
        zero_add] using ((hs.C_mul (2 : k)).mul hx)
    simpa [presentationWeight] using ((isWeightedHomogeneous_one k presentationWeight).add ht).mul hJ
  have hlast : ((X 0 : P k 5) * (X 4)^2).IsWeightedHomogeneous presentationWeight 1 := by
    simpa [presentationWeight] using hp.mul (hJ.pow 2)
  exact weighted_sub k (weighted_sub k hfirst hmid) hlast

/-- The weight-one relation is nonzero, hence its weighted degree is one. -/
theorem Hstar_degree [Nontrivial k] :
    weightedTotalDegree' presentationWeight (Hstar k) = (1 : WithBot ℤ) := by
  apply (Hstar_homogeneous k).weighted_total_degree
  intro h
  exact p_not_dvd_Hstar k (h ▸ dvd_zero _)

/-- The degree-one component of the original relation is exactly `Hstar`. -/
theorem H_degree_one_component :
    weightedHomogeneousComponent presentationWeight 1 (H k) = Hstar k := by
  unfold H
  rw [map_sub, (Hstar_homogeneous k).weightedHomogeneousComponent_same]
  have hu : (X 2 : P k 5).IsWeightedHomogeneous presentationWeight 0 := by
    simpa [presentationWeight] using isWeightedHomogeneous_X k presentationWeight (2 : Fin 5)
  rw [hu.weightedHomogeneousComponent_ne (1 : ℤ) (by decide), sub_zero]

end StableCoordinate.Obstruction

namespace StableCoordinate.Obstruction

open MvPolynomial
variable (k : Type*) [CommRing k]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The principal ideal of the highest relation is homogeneous for the
source's actual integer grading, including its negative weight. -/
theorem idealG_homogeneous :
    (idealG k).IsHomogeneous (weightedHomogeneousSubmodule k presentationWeight) := by
  apply Ideal.homogeneous_span
  intro q hq
  simp only [Set.mem_singleton_iff] at hq
  subst q
  exact ⟨1, Hstar_homogeneous k⟩

end StableCoordinate.Obstruction

end

end OAI
