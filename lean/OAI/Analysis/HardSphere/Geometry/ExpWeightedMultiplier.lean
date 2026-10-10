import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.SpatialCloseScale
import OAI.Analysis.HardSphere.Geometry.SmoothSiteWeight

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory
open scoped ComplexConjugate
noncomputable section

def expWeightedMultiplier (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ) : SmoothMultiplier n L :=
  (smoothWeightedCountMultiplier n L A).realComp (fun x ↦ Real.exp (t*x/2))
    (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).div_const 2))

lemma expWeightedMultiplier_apply (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ) (X : Configuration n L) :
    (expWeightedMultiplier n L A t).toFun X=(Real.exp (t*smoothWeightedCount L A X/2):ℂ) := by
  change (Real.exp (t*((smoothWeightedCountMultiplier n L A).toFun X).re/2):ℂ)=_
  rw [smoothWeightedCountMultiplier_apply,Complex.ofReal_re]

lemma expWeightedMultiplier_real (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ) (X : Configuration n L) :
    conj ((expWeightedMultiplier n L A t).toFun X)=(expWeightedMultiplier n L A t).toFun X := by
  rw [expWeightedMultiplier_apply,Complex.conj_ofReal]

lemma expWeightedMultiplier_norm_sq (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ) (X : Configuration n L) :
    ‖(expWeightedMultiplier n L A t).toFun X‖^2=Real.exp (t*smoothWeightedCount L A X) := by
  rw [expWeightedMultiplier_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs,←Real.exp_nat_mul]
  congr 1
  ring

lemma expWeightedMultiplier_partial_sq (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ)
    (p : Direction n) (X : Configuration n L) :
    ‖coordDerivative n L (expWeightedMultiplier n L A t).toFun p X‖^2=
      (t^2/4)*Real.exp (t*smoothWeightedCount L A X)*
        ‖coordDerivative n L (smoothWeightedCountMultiplier n L A).toFun p X‖^2 := by
  rw [expWeightedMultiplier,SmoothMultiplier.partial_realComp _ _ _ (smoothWeightedCountMultiplier_real n L A)]
  have hd (x : ℝ) : deriv (fun x : ℝ ↦ Real.exp (t*x/2)) x=(t/2)*Real.exp (t*x/2) := by
    simpa [mul_comm] using ((((hasDerivAt_id x).const_mul t).div_const 2).exp).deriv
  rw [hd,smoothWeightedCountMultiplier_apply,Complex.ofReal_re,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,←Real.exp_nat_mul]
  congr 1
  congr 1
  · ring
  · congr 1; ring

lemma expWeightedMultiplier_gradient (n : ℕ) (L : Length) (A : Finset (Torus L)) (t : ℝ)
    (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (expWeightedMultiplier n L A t).toFun p X‖^2)≤
      (t^2/4)*(3*(spatialMetricConstant:ℝ)^2*Real.exp 1)*
        (smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X)) := by
  simp_rw [expWeightedMultiplier_partial_sq,←Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (smoothWeightedCount_gradient L A X)
    (by positivity : 0≤t^2/4*Real.exp (t*smoothWeightedCount L A X))).trans_eq
  ring

lemma SmoothMultiplier.error_integrable {n : ℕ} {L : Length} (f : SmoothMultiplier n L) (u : ScalarL2 n L) :
    Integrable (fun X ↦ (∑ p : Direction n, ‖coordDerivative n L f.toFun p X‖^2)*‖u X‖^2) volume := by
  have hi (p : Direction n) : Integrable (fun X ↦ ‖(f.derivativeScalar p u) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  apply (integrable_finsetSum Finset.univ (fun p _ ↦ hi p)).congr
  have hc : ∀ᵐ X ∂volume, ∀ p, (f.derivativeScalar p u) X=coordDerivative n L f.toFun p X*u X :=
    ae_all_iff.mpr (fun p ↦ f.coe_derivativeScalar p u)
  filter_upwards [hc] with X hX
  simp_rw [hX,norm_mul,mul_pow,Finset.sum_mul]

lemma SmoothMultiplier.error_integral {n : ℕ} {L : Length} (f : SmoothMultiplier n L) (u : ScalarL2 n L) :
    (∑ p : Direction n, ‖f.derivativeScalar p u‖^2)=
      ∫ X, (∑ p : Direction n, ‖coordDerivative n L f.toFun p X‖^2)*‖u X‖^2 := by
  simpa using SmoothMultiplier.partition_error_integral (fun _ : Unit ↦ f) u

lemma SmoothMultiplier.weighted_norm_integral {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (u : ScalarL2 n L) (F : Configuration n L → ℝ) :
    (∫ X, F X*‖(f.onScalar u) X‖^2)=∫ X, F X*‖f.toFun X‖^2*‖u X‖^2 := by
  apply integral_congr_ae
  filter_upwards [f.coe_onScalar u] with X hX
  rw [hX,norm_mul,mul_pow,mul_assoc]

lemma expWeightedMultiplier_mass {n : ℕ} {L : Length} (A : Finset (Torus L)) (t : ℝ) (g : Jet n L) :
    ‖(expWeightedMultiplier n L A t).onScalar g.1‖^2=
      mgf (smoothWeightedCount L A) (groundPositionLaw n L g) t := by
  rw [IndicatorStrong.norm_sq_integral,mgf,groundPositionLaw_integral]
  apply integral_congr_ae
  filter_upwards [(expWeightedMultiplier n L A t).coe_onScalar g.1] with X hX
  rw [hX,norm_mul,mul_pow,expWeightedMultiplier_norm_sq]

lemma smoothWeightedCount_exp_integrable {n : ℕ} {L : Length} (A : Finset (Torus L)) (t : ℝ) (g : Jet n L) :
    Integrable (fun X ↦ (smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X))*‖g.1 X‖^2) volume := by
  let G := smoothWeightedCount (n:=n) L A
  let B := Real.exp 1*(n:ℝ)
  have hb (X : Configuration n L) : |G X| ≤ B := by
    rw [abs_of_nonneg (smoothWeightedCount_nonneg L A X)]
    exact smoothWeightedCount_le L A X
  apply L2_bounded_weight_integrable g.1
    ((smoothWeightedCount_continuous L A).measurable.mul
      (((smoothWeightedCount_continuous L A).measurable.const_mul t).exp))
  intro X
  change |G X*Real.exp (t*G X)| ≤ _
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (hb X) (Real.exp_le_exp.mpr (calc
    t*G X ≤ |t*G X| := le_abs_self _
    _ = |t| *|G X| := abs_mul _ _
    _ ≤ |t| *B := mul_le_mul_of_nonneg_left (hb X) (abs_nonneg t)))
    (Real.exp_pos _).le (by dsimp [B]; positivity)

lemma expWeightedMultiplier_defect {n : ℕ} {L : Length} {r : ℝ} (A : Finset (Torus L)) (t : ℝ)
    {g : Jet n L} (hg : IsGroundVector n L r g) :
    energy ((expWeightedMultiplier n L A t).onJet g)-energy g*‖(expWeightedMultiplier n L A t).onScalar g.1‖^2≤
      (t^2/4)*(3*(spatialMetricConstant:ℝ)^2*Real.exp 1)*
        (∫ X, smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X) ∂groundPositionLaw n L g) := by
  rw [hg.smooth_multiplier_identity _ (expWeightedMultiplier_real n L A t),
    SmoothMultiplier.error_integral,groundPositionLaw_integral,←integral_const_mul]
  apply integral_mono ((expWeightedMultiplier n L A t).error_integrable g.1)
    ((smoothWeightedCount_exp_integrable A t g).const_mul _)
  intro X
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (expWeightedMultiplier_gradient n L A t X) (sq_nonneg ‖g.1 X‖)

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory
open scoped ComplexConjugate
noncomputable section

lemma weighted_count_penalty : ∃ C : ℝ, 0 < C ∧
    ∀ (n K : ℕ) (L : Length) (_hL : L.val=(K:ℝ)) (r D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0<r → 1≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)) (u : Jet n L), u∈dirichletDomain n L r →
      (D*r)*((∫ X, weightedSiteCount L A X*‖u.1 X‖^2)-C*D*(A.card:ℝ)*‖u.1‖^2)≤
        energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,c,hC,hc,h⟩ := weighted_local_penalty
  refine ⟨C,hC,?_⟩
  intro n K L hL r D hDeq hD hα hr hsize hsmall g hg A u hu
  by_cases hA : A.Nonempty
  · have hp := h n K L hL r (1/10) D hDeq hD hα hr (by norm_num) (by norm_num)
      (by norm_num; exact hsize) hsmall g hg A hA u hu
    have hi : 0≤∫ X, ((localizedNearLabels L A (1/10) X).card:ℝ)*‖u.1 X‖^2 :=
      integral_nonneg (fun X ↦ by positivity)
    have hn : 0≤c*r/(1/10:ℝ)^3*(∫ X, ((localizedNearLabels L A (1/10) X).card:ℝ)*‖u.1 X‖^2) :=
      mul_nonneg (by positivity) hi
    linarith only [hp,hn]
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp only [weightedSiteCount,Finset.not_nonempty_empty,ite_false,Finset.card_empty,Nat.cast_zero,
      mul_zero,zero_mul,integral_zero,sub_zero]
    exact sub_nonneg.mpr (hg.rayleigh_all u hu)

lemma exp_neg_one_mul_exp_one : Real.exp (-1)*Real.exp 1=1 := by rw [←Real.exp_add]; norm_num

lemma exp_one_mul_exp_neg_one : Real.exp 1*Real.exp (-1)=1 := by rw [mul_comm,exp_neg_one_mul_exp_one]

lemma smoothWeightedCount_lower_for_penalty {n : ℕ} (L : Length) (A : Finset (Torus L))
    (hA : A.Nonempty) (X : Configuration n L) :
    Real.exp (-1)*smoothWeightedCount L A X ≤ weightedSiteCount L A X := by
  have h := mul_le_mul_of_nonneg_left (smoothWeightedCount_bounds L A hA X).2 (Real.exp_pos (-1)).le
  rwa [←mul_assoc,exp_neg_one_mul_exp_one,one_mul] at h

lemma weightedSiteCount_le_smooth {n : ℕ} (L : Length) (A : Finset (Torus L))
    (hA : A.Nonempty) (X : Configuration n L) :
    weightedSiteCount L A X ≤ Real.exp 1*smoothWeightedCount L A X := by
  have h := mul_le_mul_of_nonneg_left (smoothWeightedCount_bounds L A hA X).1 (Real.exp_pos 1).le
  rwa [←mul_assoc,exp_one_mul_exp_neg_one,one_mul] at h

lemma expWeightedMultiplier_weight_integrable {n : ℕ} {L : Length} (A : Finset (Torus L))
    (t : ℝ) (g : Jet n L) :
    Integrable (fun X ↦ weightedSiteCount L A X*Real.exp (t*smoothWeightedCount L A X)*‖g.1 X‖^2) volume := by
  apply (weightedSiteCount_integrable L A ((expWeightedMultiplier n L A t).onScalar g.1)).congr
  filter_upwards [(expWeightedMultiplier n L A t).coe_onScalar g.1] with X hX
  rw [hX,norm_mul,mul_pow,expWeightedMultiplier_norm_sq,mul_assoc]

lemma expWeightedMultiplier_weight_lower {n : ℕ} {L : Length} (A : Finset (Torus L)) (hA : A.Nonempty)
    (t : ℝ) (g : Jet n L) :
    Real.exp (-1)*(∫ X, smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X) ∂groundPositionLaw n L g)≤
      ∫ X, weightedSiteCount L A X*‖((expWeightedMultiplier n L A t).onScalar g.1) X‖^2 := by
  rw [groundPositionLaw_integral,←integral_const_mul,SmoothMultiplier.weighted_norm_integral]
  simp_rw [expWeightedMultiplier_norm_sq]
  apply integral_mono ((smoothWeightedCount_exp_integrable A t g).const_mul _)
    (expWeightedMultiplier_weight_integrable A t g)
  intro X
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (smoothWeightedCount_lower_for_penalty L A hA X) (Real.exp_pos (t*smoothWeightedCount L A X)).le)
    (sq_nonneg ‖g.1 X‖)
  simpa only [mul_assoc] using h

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
