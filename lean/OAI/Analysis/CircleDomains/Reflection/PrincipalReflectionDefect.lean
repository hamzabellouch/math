import OAI.Analysis.CircleDomains.Reflection.AnalyticReflectionData
import OAI.Analysis.CircleDomains.Reflection.RoundReflectionMeasure

namespace OAI

/-! The actual mollified coefficients' reflection defects are uniformly
bounded and tend almost everywhere to zero. The smooth conjugate's exact
antiholomorphic derivative is expressed using this defect. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def reflectionDefect (D : AnalyticReflectionData C) (i : I) (n : ℕ) (z : ℂ) : ℂ :=
  circleReflectionPhase (D.center i) z *
    star (D.approximation.coefficient (D.limitData.index n)
      (roundReflectionPlane (D.center i) (D.radius i) z)) -
    D.approximation.coefficient (D.limitData.index n) z

lemma reflectionDefect_measurable (D : AnalyticReflectionData C) (i : I) (n : ℕ) :
    Measurable (D.reflectionDefect i n) :=
  ((circleReflectionPhase_measurable (D.center i)).mul
    (Complex.continuous_conj.measurable.comp
      ((D.approximation.coefficient _).continuous.measurable.comp
        (roundReflectionPlane_measurable _ _)))).sub
    (D.approximation.coefficient _).continuous.measurable

lemma reflectionDefect_bound (D : AnalyticReflectionData C) (i : I) (n : ℕ) (z : ℂ) :
    ‖D.reflectionDefect i n z‖≤2*D.bound := by
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_star,circleReflectionPhase_norm,one_mul]
  linarith [D.approximation.coefficient_bound (D.limitData.index n) z,
    D.approximation.coefficient_bound (D.limitData.index n)
      (roundReflectionPlane (D.center i) (D.radius i) z)]

lemma reflectionDefect_tendsto (D : AnalyticReflectionData C) (i : I) :
    ∀ᵐz ∂volume,Tendsto (fun n => D.reflectionDefect i n z) atTop (𝓝 0) := by
  have hR := roundReflectionPlane_quasiMeasurePreserving (D.center i) (D.radius_pos i).ne'
  filter_upwards [D.coefficient_tendsto,hR.ae D.coefficient_tendsto,volume.ae_ne (D.center i)]
    with z hz hRz hzc
  have he := D.extension_invariant i (z : Sphere)
  rw [roundDiskReflection_coe (D.center i) (D.radius_pos i) hzc] at he
  change D.extension (z : Sphere)=circleReflectionPhase (D.center i) z*
    star (D.extension (roundReflectionPlane (D.center i) (D.radius i) z : Sphere)) at he
  have ht := ((hRz.comp D.limitData.index_strict.tendsto_atTop).star.const_mul
    (circleReflectionPhase (D.center i) z)).sub
    (hz.comp D.limitData.index_strict.tendsto_atTop)
  simpa only [reflectionDefect,Function.comp_def,←he,sub_self] using ht

def reflectedApproximation (D : AnalyticReflectionData C) (i : I) (n : ℕ) (z : ℂ) : ℂ :=
  star (D.approximation.map (D.limitData.index n)
    (roundReflectionPlane (D.center i) (D.radius i)
      ((D.approximation.map (D.limitData.index n)).symm z)))

lemma reflectedApproximation_error (D : AnalyticReflectionData C) (i : I) (n : ℕ)
    {z : ℂ} (hz : z≠D.center i) :
    partialBar (D.reflectedApproximation i n) (D.approximation.map (D.limitData.index n) z)=
      star (partialZ (D.approximation.map (D.limitData.index n))
        (roundReflectionPlane (D.center i) (D.radius i) z))*
      star (partialBar (roundReflectionPlane (D.center i) (D.radius i)) z)*
      D.reflectionDefect i n z*
      star (partialZ (D.approximation.map (D.limitData.index n)).symm
        (D.approximation.map (D.limitData.index n) z)) := by
  exact smooth_reflection_conjugate_phase_error _
    ((D.approximation.smooth _).differentiable (by simp))
    ((D.approximation.inverse_smooth _).differentiable (by simp))
    _ (D.approximation.equation _) (roundReflectionPlane_differentiable hz)
    (roundReflectionPlane_partials hz).1 _ (roundReflectionPlane_phase hz)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
