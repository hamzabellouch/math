import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarAverageCalculus

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

structure BoundedScalar (g : ℝ → ℝ) : Prop where
  continuous : Continuous g
  bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |g x| ≤ B

theorem BoundedScalar.const (c : ℝ) : BoundedScalar (fun _ => c) :=
  ⟨continuous_const,|c|,abs_nonneg _,fun _ => le_rfl⟩

theorem BoundedScalar.add {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x+h x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  obtain ⟨C,hC,hc⟩ := hh.bounded
  exact ⟨hg.continuous.add hh.continuous,B+C,add_nonneg hB hC,
    fun x => (abs_add_le _ _).trans (add_le_add (hb x) (hc x))⟩

theorem BoundedScalar.const_mul {g : ℝ → ℝ} (hg : BoundedScalar g) (c : ℝ) :
    BoundedScalar (fun x => c*g x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  refine ⟨continuous_const.mul hg.continuous,|c| * B,mul_nonneg (abs_nonneg _) hB,fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

theorem BoundedScalar.sub {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x-h x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hg.add (hh.const_mul (-1))

theorem BoundedScalar.sq {g : ℝ → ℝ} (hg : BoundedScalar g) :
    BoundedScalar (fun x => (g x)^2) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  refine ⟨hg.continuous.pow 2,B^2,sq_nonneg _,fun x => ?_⟩
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hb x) _

theorem ScalarSpinConvex.gradient_bounded {f : ℝ → ℝ} (h : ScalarSpinConvex f)
    (hf : BoundedDerivs f) : BoundedScalar (rootGradient 0 f) :=
  ⟨rootGradient_continuous 0 hf,1,zero_le_one,fun x => (h.bounds x).1⟩

theorem ScalarSpinConvex.hessian_bounded {f : ℝ → ℝ} (h : ScalarSpinConvex f)
    (hf : BoundedDerivs f) : BoundedScalar (rootHessian 0 f) :=
  ⟨rootHessian_continuous 0 hf,1,zero_le_one,fun x => (h.bounds x).2⟩

theorem BoundedScalar.scalarStepAverage {f g : ℝ → ℝ} (hg : BoundedScalar g)
    (hf : BoundedDerivs f) (m v : ℝ) : BoundedScalar (scalarStepAverage m v f g) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  exact ⟨scalarStepAverage_continuous hf hg.continuous hB hb m v,B,hB,
    scalarStepAverage_bound hf hb m v⟩

theorem scalarHierarchyAverage_bounded {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) :
    BoundedScalar (scalarHierarchyAverage n m v f g) := by
  induction n generalizing f g with
  | zero => exact hg
  | succ n ih => exact ih (scalarStep_regular hf _ _) (hg.scalarStepAverage hf _ _) _ _

theorem scalarHierarchyAverage_integrable {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    Integrable (fun z => g (x+coordinateLinear n v z))
      (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) := by
  obtain ⟨B,_,hb⟩ := hg.bounded
  apply hierarchyPathLaw_integrable n m _ _ ((hf.translate x).compCLM (coordinateLinear n v))
    (hg.continuous.comp (continuous_const.add (coordinateLinear n v).continuous))
  exact fun z => hb _

theorem scalarHierarchyAverage_integral {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f g x=
      ∫ z, g (x+coordinateLinear n v z) ∂hierarchyPathLaw n m
        (fun z => f (x+coordinateLinear n v z)) 0 := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  exact scalarHierarchyAverage_eq_integral n m v hf hg.continuous hB hb x

theorem scalarHierarchyAverage_const_mul {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x c : ℝ) :
    scalarHierarchyAverage n m v f (fun y => c*g y) x=c*scalarHierarchyAverage n m v f g x := by
  rw [scalarHierarchyAverage_integral hf (hg.const_mul c),scalarHierarchyAverage_integral hf hg,
    integral_const_mul]

theorem scalarHierarchyAverage_add {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => g y+h y) x=
      scalarHierarchyAverage n m v f g x+scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf (hg.add hh),scalarHierarchyAverage_integral hf hg,
    scalarHierarchyAverage_integral hf hh,integral_add
    (scalarHierarchyAverage_integrable hf hg n m v x) (scalarHierarchyAverage_integrable hf hh n m v x)]

theorem scalarHierarchyAverage_sub {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => g y-h y) x=
      scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf (hg.sub hh),scalarHierarchyAverage_integral hf hg,
    scalarHierarchyAverage_integral hf hh,integral_sub
    (scalarHierarchyAverage_integrable hf hg n m v x) (scalarHierarchyAverage_integrable hf hh n m v x)]

theorem scalarHierarchyAverage_mono {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (hle : ∀ x, g x ≤ h x)
    (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f g x ≤ scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf hg,scalarHierarchyAverage_integral hf hh]
  exact integral_mono (scalarHierarchyAverage_integrable hf hg n m v x)
    (scalarHierarchyAverage_integrable hf hh n m v x) (fun z => hle _)

theorem scalarHierarchyAverage_nonneg {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hle : ∀ x, 0 ≤ g x) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    0 ≤ scalarHierarchyAverage n m v f g x := by
  rw [scalarHierarchyAverage_integral hf hg]
  exact integral_nonneg (fun z => hle _)

theorem scalarHierarchyAverage_sq {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    (scalarHierarchyAverage n m v f g x)^2 ≤ scalarHierarchyAverage n m v f (fun y => (g y)^2) x := by
  rw [scalarHierarchyAverage_integral hf hg,scalarHierarchyAverage_integral hf hg.sq]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  obtain ⟨B,_,hb⟩ := hg.bounded
  have H : MemLp (fun z => g (x+coordinateLinear n v z)) 2
      (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    MemLp.of_bound (hg.continuous.comp (continuous_const.add (coordinateLinear n v).continuous)).aestronglyMeasurable
      B (ae_of_all _ (fun z => hb _))
  have HP := variance_nonneg (X:=fun z => g (x+coordinateLinear n v z))
    (μ:=hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0)
  rw [variance_eq_sub H] at HP
  exact sub_nonneg.mp HP

end SK.Analytic

end
end

end OAI
