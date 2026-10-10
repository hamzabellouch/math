import Mathlib
import OAI.Analysis.HardSphere.Orbitals.Profile
import OAI.Analysis.HardSphere.Geometry.FinsetProd

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma bump_separated {S : Type*} {L : Length} (c : S → Torus L)
    (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v)) (z v : S) (hzv : z≠v) (y : Torus L) :
    bump L (8*(1/100)) (c z) y=0 ∨ bump L (8*(1/100)) (c v) y=0 := by
  by_contra hn
  push Not at hn
  have hbz := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<8*(1/100)) (c z)
    (bump_support (by norm_num) (c z) (subset_closure hn.1))
  have hbv := TightCutoff.near_subset_box L.val (by norm_num : (0:ℝ)<8*(1/100)) (c v)
    (bump_support (by norm_num) (c v) (subset_closure hn.2))
  have hd : dist (c z) (c v) ≤ (32:ℝ)/100 := by
    apply (dist_pi_le_iff (by norm_num)).mpr
    intro j
    have hzj : dist (y j) (c z j) ≤ 2*(8*(1/100)) := Set.mem_univ_pi.mp hbz j
    have hvj : dist (y j) (c v j) ≤ 2*(8*(1/100)) := Set.mem_univ_pi.mp hbv j
    have ht := dist_triangle (c z j) (y j) (c v j)
    rw [dist_comm (c z j) (y j)] at ht
    linarith
  linarith [hc z v hzv]

lemma cutoff_partials_disjoint {S : Type*} {n : ℕ} {L : Length} (c : S → Torus L)
    (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v)) (h : ℝ) (z v : S) (hzv : z≠v)
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (cutoff n L (1/100) (c z) h).toFun p X=0 ∨
    coordDerivative n L (cutoff n L (1/100) (c v) h).toFun p X=0 := by
  rcases bump_separated c hc z v hzv (X p.1) with hz | hv
  · left
    simp only [cutoff_partial,countMultiplier_partial,chiOne_partial,hz,Complex.ofReal_zero,mul_zero,zero_mul]
  · right
    simp only [cutoff_partial,countMultiplier_partial,chiOne_partial,hv,Complex.ofReal_zero,mul_zero,zero_mul]

def joint {S : Type*} [DecidableEq S] (n : ℕ) (L : Length) (c : S → Torus L) (h : ℝ) (A : Finset S) :
    SmoothMultiplier n L := SmoothMultiplier.finsetProd A (fun s ↦ cutoff n L (1/100) (c s) h)

lemma joint_apply {S : Type*} [DecidableEq S] (n : ℕ) (L : Length) (c : S → Torus L)
    (h : ℝ) (A : Finset S) (X : Configuration n L) :
    (joint n L c h A).toFun X=(∏ s∈A, (profile h (count L (1/100) (c s) X) : ℂ)) := by
  change (∏ s∈A, (cutoff n L (1/100) (c s) h).toFun X)=_
  simp_rw [cutoff_apply]

lemma joint_real {S : Type*} [DecidableEq S] (n : ℕ) (L : Length) (c : S → Torus L)
    (h : ℝ) (A : Finset S) (X : Configuration n L) :
    conj ((joint n L c h A).toFun X)=(joint n L c h A).toFun X := by
  simp only [joint_apply,map_prod,Complex.conj_ofReal]

lemma joint_partial {S : Type*} [DecidableEq S] (n : ℕ) (L : Length) (c : S → Torus L)
    (h : ℝ) (A : Finset S) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (joint n L c h A).toFun p X=
      ∑ s∈A, (joint n L c h (A.erase s)).toFun X*
        coordDerivative n L (cutoff n L (1/100) (c s) h).toFun p X := by
  exact SmoothMultiplier.partial_finsetProd A _ p X

lemma joint_gradient_le {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h M : ℝ}
    (hh : 0<h) (hM : 0 ≤ M) (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M)
    (c : S → Torus L) (hc : ∀ z v, z≠v → 1 ≤ dist (c z) (c v))
    (A : Finset S) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (joint n L c h A).toFun p X‖^2) ≤
      ((2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*(1/100))^2))))/h)*
        ∑ s∈A, ‖(joint n L c h (A.erase s)).toFun X‖^2 := by
  have he (p : Direction n) :
      ‖coordDerivative n L (joint n L c h A).toFun p X‖^2=
      ∑ s∈A, ‖(joint n L c h (A.erase s)).toFun X‖^2*
        ‖coordDerivative n L (cutoff n L (1/100) (c s) h).toFun p X‖^2 := by
    rw [joint_partial,norm_sq_sum_of_disjoint]
    · simp_rw [norm_mul,mul_pow]
    · intro z hz v hv hzv
      rcases cutoff_partials_disjoint c hc h z v hzv p X with h1 | h2
      · exact Or.inl (by rw [h1,mul_zero])
      · exact Or.inr (by rw [h2,mul_zero])
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  calc
    _ ≤ ‖(joint n L c h (A.erase s)).toFun X‖^2 * ((2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*(1/100))^2))))/h) :=
      mul_le_mul_of_nonneg_left (cutoff_gradient_le (δ:=1/100) (by norm_num) hh hM hb (c s) X) (sq_nonneg _)
    _ = _ := mul_comm _ _

end HardSphere.CellOrbital

end

end OAI
