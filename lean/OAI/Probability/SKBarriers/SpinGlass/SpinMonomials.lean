import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.GaugeSymmetry
import OAI.Probability.SKBarriers.Hierarchy.HierarchyJointMoment

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK
open Analytic

def spinMonomial {N : ℕ} (x : Config N) (I : Finset (Fin N)) : ℝ :=
  ∏ i ∈ I, spin (x i)

@[simp] theorem spinMonomial_sq {N : ℕ} (x : Config N) (I : Finset (Fin N)) :
    (spinMonomial x I)^2 = 1 := by
  simp only [spinMonomial,← Finset.prod_pow,spin_sq,Finset.prod_const_one]

theorem spinMonomial_gauge {N : ℕ} (v x : Config N) (I : Finset (Fin N)) :
    spinMonomial (gaugeConfig v x) I = spinMonomial v I*spinMonomial x I := by
  simp only [spinMonomial,gaugeConfig,spin_beq,Finset.prod_mul_distrib]

def monomialSign {N : ℕ} (v : Config N) (I : Finset (Fin N)) : Bool :=
  decide (spinMonomial v I = -1)

theorem scalarSign_monomial {N : ℕ} (v : Config N) (I : Finset (Fin N)) (z : ℝ) :
    scalarSign (monomialSign v I) z = spinMonomial v I*z := by
  have hh : spinMonomial v I = 1 ∨ spinMonomial v I = -1 :=
    (sq_eq_one_iff).mp (spinMonomial_sq v I)
  rcases hh with h | h <;> norm_num [monomialSign,h,scalarSign]

def spinExponent {N : ℕ} (d : ℕ) (a : Fin d → ℝ) (I : Fin d → Finset (Fin N))
    (s : Config N) : ParameterSpace d →L[ℝ] ℝ :=
  coordinateLinear d (fun j => a j*spinMonomial s (I j))

theorem spinExponent_axis {N : ℕ} (d : ℕ) (a : Fin d → ℝ) (I : Fin d → Finset (Fin N))
    (s : Config N) : spinExponent d a I s (parameterAxis d) = 0 :=
  coordinateLinear_axis _ _

theorem spinExponent_gauge {N : ℕ} (d : ℕ) (a : Fin d → ℝ) (I : Fin d → Finset (Fin N))
    (v s : Config N) (z : ParameterSpace d) :
    spinExponent d a I s (coordinateSign d (fun j => monomialSign v (I j)) z) =
      spinExponent d a I (gaugeConfig v s) z := by
  simp only [spinExponent,coordinateLinear_apply,coordinateProjection_sign,scalarSign_monomial,
    spinMonomial_gauge]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spinExponent_sq_le {N : ℕ} (d : ℕ) (a : Fin d → ℝ) (I : Fin d → Finset (Fin N))
    (s : Config N) (z : ParameterSpace d) :
    (spinExponent d a I s z)^2 ≤ (∑ j, (a j)^2)*coordinateSquare d z := by
  have h := coordinateLinear_sq_le d (fun j => a j*spinMonomial s (I j)) z
  simpa only [spinExponent,mul_pow,spinMonomial_sq,mul_one] using h

theorem hierarchy_spin_variance {N : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hmu : ∀ j, m j ≤ 1) (hmono : Monotone m)
    (a b : Fin d → ℝ) (I : Fin d → Finset (Fin N)) :
    let U := spinExponent d a I
    let L := spinExponent d b I
    hierarchyJointMoment d m U L 2 / hierarchyJointMoment d m U L 0 -
      (hierarchyJointMoment d m U L 1 / hierarchyJointMoment d m U L 0)^2 ≤ ∑ j, (b j)^2 := by
  apply hierarchy_gauge_linear_variance d m hm hmu hmono
    (spinExponent d a I) (spinExponent d b I) (spinExponent_axis d a I) (spinExponent_axis d b I)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (spinExponent_sq_le d b I)
    (fun _ : Fin N => true) (fun s j => monomialSign s (I j)) gaugeConfigEquiv
  · exact gaugeConfig_self
  · exact spinExponent_gauge d a I
  · intro s z
    simpa only [gaugeConfig_self] using spinExponent_gauge d b I s s z

end SK

end
end
end
end
end
end

end OAI
