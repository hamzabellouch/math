import Mathlib
import OAI.Geometry.PrescribedPotential.ChartParametrix
import OAI.Geometry.PrescribedPotential.LocalRegularity
import OAI.Geometry.PrescribedPotential.SmoothDistributions

namespace OAI

/-! Smooth Chart Inverse. -/

section

 

noncomputable section
open Filter Set Topology MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ComplexOrder MatrixOrder Matrix.Norms.Elementwise ContDiff

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma temperateDistribution_sum {ι : Type*} [Fintype ι] (f : ι → E → ℂ)
    (hf : ∀ i, (f i).HasTemperateGrowth) :
    (Function.HasTemperateGrowth.sum (s := Finset.univ) (fun i _ => hf i)).toTemperedDistribution volume =
      ∑ i, (hf i).toTemperedDistribution volume := by
  simp only [temperateDistribution_eq_smul_volume]
  rw [smulLeftCLM_sum (fun i _ => hf i)]
  simp

lemma temperateDistribution_mul {f g : E → ℂ} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) :
    (hf.mul hg).toTemperedDistribution volume =
      smulLeftCLM ℂ f (hg.toTemperedDistribution volume) := by
  simp only [temperateDistribution_eq_smul_volume]
  rw [smulLeftCLM_smulLeftCLM_apply hg hf, mul_comm]

end SobolevChart

namespace MetricLocalization
open EllipticKernel FrozenPoisson SobolevChart
variable {n : ℕ}

def classicalDifferential (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (f : EC n → ℂ) : EC n → ℂ := fun x =>
  ∑ k, ∑ l, c k l x * directionDerivative (stdOrthonormalBasis ℝ (EC n) k)
    (directionDerivative (stdOrthonormalBasis ℝ (EC n) l) f) x

lemma classicalDifferential_temperate
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ k l, (c k l : EC n → ℂ).HasTemperateGrowth)
    {f : EC n → ℂ} (hf : f.HasTemperateGrowth) :
    (classicalDifferential c f).HasTemperateGrowth := by
  apply Function.HasTemperateGrowth.sum
  intro k _
  apply Function.HasTemperateGrowth.sum
  intro l _
  exact (hc k l).mul (temperate_directionDerivative _ (temperate_directionDerivative _ hf))

lemma classicalDifferential_distribution
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ k l, (c k l : EC n → ℂ).HasTemperateGrowth)
    {f : EC n → ℂ} (hf : f.HasTemperateGrowth) :
    (classicalDifferential_temperate c hc hf).toTemperedDistribution volume =
      chartDifferential c (hf.toTemperedDistribution volume) := by
  let b := stdOrthonormalBasis ℝ (EC n)
  have hg k l := (hc k l).mul
    (temperate_directionDerivative (b k) (temperate_directionDerivative (b l) hf))
  change (Function.HasTemperateGrowth.sum
    (s := Finset.univ) (fun k _ => Function.HasTemperateGrowth.sum
      (s := Finset.univ) (fun l _ => hg k l))).toTemperedDistribution volume = _
  rw [temperateDistribution_sum
    (fun k x => ∑ l, c k l x * directionDerivative (b k) (directionDerivative (b l) f) x)
    (fun k => Function.HasTemperateGrowth.sum (fun l _ => hg k l))]
  simp only [chartDifferential, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [temperateDistribution_sum
    (fun l x => c k l x * directionDerivative (b k) (directionDerivative (b l) f) x)
    (hg k)]
  apply Finset.sum_congr rfl
  intro l _
  rw [temperateDistribution_mul (hc k l)
    (temperate_directionDerivative (b k) (temperate_directionDerivative (b l) hf)),
    temperateDistribution_derivative (b k) (temperate_directionDerivative (b l) hf),
    temperateDistribution_derivative (b l) hf]
  rfl

 

theorem extended_smooth_solution
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (a : SmoothCoefficients (BasisIndex n) (EC n))
    (hsmall : perturbationBound (stdOrthonormalBasis ℝ (EC n)) (coefficientBCF a) *
      ellipticBound H hH < 1) (f : 𝓢(EC n, ℂ)) :
    ∃ u : EC n →ᵇ ℂ, (u : EC n → ℂ).HasTemperateGrowth ∧
      (fun x => u x - classicalDifferential (extendedCoefficient H (coefficientBCF a)) u x) = f := by
  let v := stdOrthonormalBasis ℝ (EC n)
  let R := localResolvent H hH v (coefficientBCF a) hsmall
  obtain ⟨u, hu, hue⟩ := all_even_smooth_representative
    (localResolvent_schwartz_memSobolev H hH v a hsmall f)
  have ha k l : (coefficientBCF a k l : EC n → ℂ).HasTemperateGrowth :=
    (a k l).hasTemperateGrowth
  have hc := extendedCoefficient_temperate H (coefficientBCF a) ha
  refine ⟨u, hu, ?_⟩
  apply temperateDistribution_injective (hu.sub (classicalDifferential_temperate _ hc hu))
    f.hasTemperateGrowth
  rw [temperateDistribution_sub hu (classicalDifferential_temperate _ hc hu),
    classicalDifferential_distribution _ hc hu,
    temperateDistribution_bounded u hu, hue, temperateDistribution_schwartz]
  rw [chartDifferential_extension H (coefficientBCF a) ha]
  rw [← sub_sub]
  have he := localResolvent_equation H hH v (coefficientBCF a) hsmall (schwartzCoord 0 f)
  have hz : realize 0 (schwartzCoord 0 f) = (schwartzCoord 0 f : 𝓢'(EC n, ℂ)) := by
    simp [realize]
  rw [← hz, realize_schwartzCoord] at he
  exact he

 

theorem germ_smooth_solution {U : Set (EC n)} (hU : IsOpen U)
    (H : EC n → Matrix (Fin n) (Fin n) ℂ) (hH : ContDiffOn ℝ ∞ H U)
    (hh : ∀ y ∈ U, (H y).PosDef) {x : EC n} (hx : x ∈ U) :
    ∃ V : Set (EC n), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ f : 𝓢(EC n, ℂ), ∃ u : EC n →ᵇ ℂ,
        (u : EC n → ℂ).HasTemperateGrowth ∧ ∀ y ∈ V,
          u y - (∑ k, ∑ l, (traceBilin (H y)
            (rankTwo (stdOrthonormalBasis ℝ (EC n) k)
              (stdOrthonormalBasis ℝ (EC n) l)) : ℂ) *
            directionDerivative (stdOrthonormalBasis ℝ (EC n) k)
              (directionDerivative (stdOrthonormalBasis ℝ (EC n) l) u) y) = f y := by
  let b := stdOrthonormalBasis ℝ (EC n)
  obtain ⟨a, hat, hac, has, hag⟩ := local_coefficient_extension hU H hH hh hx b
  let a' : SmoothCoefficients (BasisIndex n) (EC n) :=
    fun k l => (hac k l).toSchwartzMap (hat k l).1
  have hae : coefficientBCF a' = a := by
    funext k l
    ext y
    rfl
  have has' : perturbationBound b (coefficientBCF a') * ellipticBound (H x) (hh x hx) < 1 := by
    rw [hae]
    exact has
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hag)
  refine ⟨V, hVo, hxV, fun y hy => (hVsub hy).1, fun f => ?_⟩
  obtain ⟨u, hu, he⟩ := extended_smooth_solution (H x) (hh x hx) a' has' f
  refine ⟨u, hu, fun y hy => ?_⟩
  have hc k l : extendedCoefficient (H x) (coefficientBCF a') k l y =
      (traceBilin (H y) (rankTwo (b k) (b l)) : ℂ) := by
    rw [hae]
    change (traceBilin (H x) (rankTwo (b k) (b l)) : ℂ) + a k l y = _
    rw [(hVsub hy).2 k l]
    ring
  have hey := congrFun he y
  simpa only [classicalDifferential, hc] using hey

end MetricLocalization

end
end

end OAI
