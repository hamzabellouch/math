import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarOneAtom
import OAI.Probability.SKBarriers.Scalar.DyadicSpin
import OAI.Probability.SKBarriers.Scalar.UniformDerivativeLimit

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarCDFValue (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => dyadicScalar β α n s t scalarSpinTerminal x)

def scalarCDFGradient (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal) x)

def scalarCDFHessian (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => rootHessian 0 (dyadicScalar β α n s t scalarSpinTerminal) x)

theorem scalarSpinTerminal_regular : BoundedDerivs scalarSpinTerminal :=
  scalarHierarchy_spin_regular 0 Fin.elim0 Fin.elim0

theorem dyadicScalar_value_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => dyadicScalar β α n s t scalarSpinTerminal)
      (scalarCDFValue β α s t) atTop :=
  (geometric_uniform_limit (fun k => dyadicScalar β α k s t scalarSpinTerminal) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    (fun n x => dyadicScalar_successive_geometric scalarSpinTerminal_regular
      scalarSpinTerminal_lipschitz β hα hmono n s t ht x)).1

theorem dyadicScalar_value_error (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (n : ℕ) (x : ℝ) :
    |dyadicScalar β α n s t scalarSpinTerminal x-scalarCDFValue β α s t x| ≤
      2*scalarTimeMassConstant β*(1/2:ℝ)^n := by
  have H := (geometric_uniform_limit (fun k => dyadicScalar β α k s t scalarSpinTerminal) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    (fun n x => dyadicScalar_successive_geometric scalarSpinTerminal_regular
      scalarSpinTerminal_lipschitz β hα hmono n s t ht x)).2 n x
  dsimp [scalarCDFValue]
  convert H using 1; ring

theorem dyadicScalar_gradient_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal))
      (scalarCDFGradient β α s t) atTop := by
  apply uniformCauchySeq_limUnder
  apply uniformCauchySeq_derivative 1
    (fun n x => scalarTimeChain_spin_hasDerivAt β (dyadicIntervals α n s t) x)
    (fun n => scalarTimeChain_spin_gradient_lipschitz β (dyadicIntervals α n s t)
      (fun _ hp => dyadicIntervals_mass_bounds hα n s t hp))
  exact (tendstoUniformlyOn_univ.mpr (dyadicScalar_value_uniform β hα hmono s t ht)).uniformCauchySeqOn

theorem dyadicScalar_hessian_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => rootHessian 0 (dyadicScalar β α n s t scalarSpinTerminal))
      (scalarCDFHessian β α s t) atTop := by
  apply uniformCauchySeq_limUnder
  apply uniformCauchySeq_derivative susceptibilityLipschitzConstant
    (fun n x => scalarTimeChain_spin_gradient_hasDerivAt β (dyadicIntervals α n s t) x)
    (fun n => scalarTimeChain_spin_hessian_lipschitz β (dyadicIntervals α n s t)
      (fun _ hp => dyadicIntervals_mass_bounds hα n s t hp) (dyadicIntervals_pairwise hmono n s t))
  exact (tendstoUniformlyOn_univ.mpr (dyadicScalar_gradient_uniform β hα hmono s t ht)).uniformCauchySeqOn

theorem scalarCDFValue_hasDerivAt (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    HasDerivAt (scalarCDFValue β α s t) (scalarCDFGradient β α s t x) x :=
  hasDerivAt_of_tendstoUniformly (dyadicScalar_gradient_uniform β hα hmono s t ht)
    (Eventually.of_forall (fun n z => scalarTimeChain_spin_hasDerivAt β (dyadicIntervals α n s t) z))
    (fun z => (dyadicScalar_value_uniform β hα hmono s t ht).tendsto_at z) x

theorem scalarCDFGradient_hasDerivAt (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    HasDerivAt (scalarCDFGradient β α s t) (scalarCDFHessian β α s t x) x :=
  hasDerivAt_of_tendstoUniformly (dyadicScalar_hessian_uniform β hα hmono s t ht)
    (Eventually.of_forall (fun n z => scalarTimeChain_spin_gradient_hasDerivAt β (dyadicIntervals α n s t) z))
    (fun z => (dyadicScalar_gradient_uniform β hα hmono s t ht).tendsto_at z) x

theorem scalarCDF_derivative_bounds (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFGradient β α s t x| ≤ 1 ∧ 0 ≤ scalarCDFHessian β α s t x ∧
      scalarCDFHessian β α s t x ≤ 1-(scalarCDFGradient β α s t x)^2 := by
  have hG := (dyadicScalar_gradient_uniform β hα hmono s t ht).tendsto_at x
  have hH := (dyadicScalar_hessian_uniform β hα hmono s t ht).tendsto_at x
  refine ⟨le_of_tendsto hG.abs (Eventually.of_forall (fun n =>
    (dyadicScalar_spin_bounds β hα n s t x).1)),?_,?_⟩
  · exact ge_of_tendsto hH (Eventually.of_forall (fun n =>
      (dyadicScalar_spin_bounds β hα n s t x).2.1.le))
  · exact le_of_tendsto_of_tendsto hH (tendsto_const_nhds.sub (hG.pow 2))
      (Eventually.of_forall (fun n => (dyadicScalar_spin_bounds β hα n s t x).2.2))

theorem scalarCDFHessian_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ s, α s ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    LipschitzWith susceptibilityLipschitzConstant (scalarCDFHessian β α s t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have H (n) := (scalarTimeChain_spin_hessian_lipschitz β (dyadicIntervals α n s t)
    (fun _ hp => dyadicIntervals_mass_bounds hα n s t hp)
    (dyadicIntervals_pairwise hmono n s t)).dist_le_mul x y
  exact le_of_tendsto
    (((dyadicScalar_hessian_uniform β hα hmono s t ht).tendsto_at x).dist
      ((dyadicScalar_hessian_uniform β hα hmono s t ht).tendsto_at y)) (Eventually.of_forall H)

end SK.Analytic

end
end

end OAI
