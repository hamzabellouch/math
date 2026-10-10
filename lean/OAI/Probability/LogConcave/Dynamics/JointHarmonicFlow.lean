import Mathlib
import OAI.Probability.LogConcave.Sampling.HarmonicKernel
import OAI.Probability.LogConcave.Dynamics.HarmonicFlow

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators RealInnerProductSpace NNReal
open TensorEnergy

theorem exists_joint_harmonic_flow {d : ℕ} {H : Point d → ℝ} {L : ℝ≥0}
    (hH : ContDiff ℝ 2 H) (htail : HasGaussianLowerTail H)
    (hL : LipschitzWith L (gradient H)) :
    ∃Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y) ∧ Ξ y 0=y) ∧
      (∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (productPotential H (fun z : Point d => ‖z‖^2/2))
          (harmonicSkew d) (Ξ y t)) (Icc (0:ℝ) 1) t) ∧
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) ∧
      (∀t∈Icc (0:ℝ) 1,(gibbs (productPotential H (fun z : Point d => ‖z‖^2/2))).map
        (fun y => Ξ y t)=gibbs (productPotential H (fun z : Point d => ‖z‖^2/2))) := by
  obtain ⟨Ψ,hΨ,hc,hlaw⟩ := exists_harmonic_flow hH htail hL (by norm_num : (0:ℝ)≤1)
  let E := productPointEquiv d d
  let τ : ℝ → ℝ := fun t => min (max t 0) 1
  have hτ : Continuous τ := (continuous_id.max continuous_const).min continuous_const
  have hτmem (t : ℝ) : τ t∈Icc (0:ℝ) 1 :=
    ⟨le_min (le_max_right _ _) (by norm_num),min_le_right _ _⟩
  have hτeq (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : τ t=t := by
    exact (min_eq_left (by rw [max_eq_left ht.1]; exact ht.2)).trans (max_eq_left ht.1)
  let Ξ : Point (d+d) → ℝ → Point (d+d) := fun y t => E.symm (Ψ (E y) (τ t))
  have hΞc (y : Point (d+d)) : Continuous (Ξ y) := E.symm.continuous.comp ((hΨ (E y)).1.comp hτ)
  have hΞs (t : ℝ) : Continuous (fun y => Ξ y t) := E.symm.continuous.comp ((hc (τ t) (hτmem t)).comp E.continuous)
  let μ := gibbs (productPotential H (fun z : Point d => ‖z‖^2/2))
  let ν := (gibbs H).prod (stdGaussian (Point d))
  have hm : μ.map E=ν := by
    rw [productPotential_gibbs hH.continuous (gaussianPotential_polySmooth d).smooth.continuous,
      gaussianPotential_gibbs]
  have hmi : ν.map E.symm=μ := by
    rw [←hm,Measure.map_map E.symm.continuous.measurable E.continuous.measurable]
    simp only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply,Measure.map_id']
  refine ⟨Ξ,fun y => ⟨hΞc y,?_⟩,?_,?_,?_⟩
  · dsimp [Ξ]
    rw [hτeq 0 ⟨le_rfl,by norm_num⟩,(hΨ (E y)).2.1,E.symm_apply_apply]
  · intro y t ht
    have hd := E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t ((hΨ (E y)).2.2 t ht)
    have hfield := harmonicSkew_field (hH.differentiable (by norm_num)) (E.symm (Ψ (E y) t))
    change E _=((E (E.symm (Ψ (E y) t))).2,-gradient H (E (E.symm (Ψ (E y) t))).1) at hfield
    rw [E.apply_symm_apply] at hfield
    have he := congrArg E.symm hfield
    rw [E.symm_apply_apply] at he
    change HasDerivWithinAt (fun u => E.symm (Ψ (E y) u))
      (E.symm ((Ψ (E y) t).2,-gradient H (Ψ (E y) t).1)) _ _ at hd
    rw [←he] at hd
    have hde := hd.congr (f₁:=Ξ y) (fun u hu => by dsimp [Ξ]; rw [hτeq u hu])
      (by dsimp [Ξ]; rw [hτeq t ht])
    simpa only [Ξ,hτeq t ht] using hde
  · exact measurable_uncurry_of_continuous_of_measurable hΞc (fun t => (hΞs t).measurable)
  · intro t ht
    change μ.map (fun y => E.symm (Ψ (E y) (τ t)))=μ
    rw [hτeq t ht]
    have hc' := hc t ht
    calc
      _ = ((μ.map E).map (fun p => Ψ p t)).map E.symm := by
        rw [Measure.map_map E.symm.continuous.measurable hc'.measurable,
          Measure.map_map (E.symm.continuous.measurable.comp hc'.measurable) E.continuous.measurable]
        rfl
      _ = ν.map E.symm := by rw [hm,hlaw t ht]
      _ = μ := hmi
end LogConcaveSampling

end

end

end

end OAI
