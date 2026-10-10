import Mathlib
import OAI.Geometry.PrescribedPotential.MetricLocalization

namespace OAI

/-! Chart Parametrix. -/

section

 

noncomputable section
open Filter Set Topology MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ComplexOrder MatrixOrder Matrix.Norms.Elementwise ContDiff

namespace MetricLocalization
open EllipticKernel FrozenPoisson SobolevChart
variable {n : ℕ}

abbrev BasisIndex (n : ℕ) := Fin (Module.finrank ℝ (EC n))

def chartDifferential (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ) :
    𝓢'(EC n, ℂ) →L[ℂ] 𝓢'(EC n, ℂ) :=
  ∑ k, ∑ l, smulLeftCLM ℂ (c k l) ∘L
    lineDerivOpCLM ℂ 𝓢'(EC n, ℂ) (stdOrthonormalBasis ℝ (EC n) k) ∘L
    lineDerivOpCLM ℂ 𝓢'(EC n, ℂ) (stdOrthonormalBasis ℝ (EC n) l)

def extendedCoefficient (H : Matrix (Fin n) (Fin n) ℂ)
    (a : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (k l : BasisIndex n) : EC n →ᵇ ℂ :=
  BoundedContinuousFunction.const _
    (traceBilin H (rankTwo (stdOrthonormalBasis ℝ (EC n) k)
      (stdOrthonormalBasis ℝ (EC n) l)) : ℂ) + a k l

lemma extendedCoefficient_temperate (H : Matrix (Fin n) (Fin n) ℂ)
    (a : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (ha : ∀ k l, (a k l : EC n → ℂ).HasTemperateGrowth) (k l : BasisIndex n) :
    (extendedCoefficient H a k l : EC n → ℂ).HasTemperateGrowth := by
  change ((fun _ : EC n => (traceBilin H (rankTwo
    (stdOrthonormalBasis ℝ (EC n) k) (stdOrthonormalBasis ℝ (EC n) l)) : ℂ)) +
    (a k l : EC n → ℂ)).HasTemperateGrowth
  apply Function.HasTemperateGrowth.add
  · fun_prop
  · exact ha k l

lemma chartDifferential_extension (H : Matrix (Fin n) (Fin n) ℂ)
    (a : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (ha : ∀ k l, (a k l : EC n → ℂ).HasTemperateGrowth) (u : L2 (EC n)) :
    chartDifferential (extendedCoefficient H a) (realize 2 u) =
      frozenDifferential H (realize 2 u) +
        (perturbation (stdOrthonormalBasis ℝ (EC n)) a u : 𝓢'(EC n, ℂ)) := by
  rw [perturbation_distribution _ a ha]
  simp only [chartDifferential, frozenDifferential, differentialWithBasis,
    _root_.sum_apply, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change smulLeftCLM ℂ ((fun _ : EC n => (traceBilin H (rankTwo
    (stdOrthonormalBasis ℝ (EC n) k) (stdOrthonormalBasis ℝ (EC n) l)) : ℂ)) +
    (a k l : EC n → ℂ)) _ = _
  rw [smulLeftCLM_add (by fun_prop) (ha k l)]
  simp

 

theorem chart_parametrix {U : Set (EC n)} (hU : IsOpen U)
    (H : EC n → Matrix (Fin n) (Fin n) ℂ) (hH : ContDiffOn ℝ ∞ H U)
    (hh : ∀ y ∈ U, (H y).PosDef) {x : EC n} (hx : x ∈ U) :
    ∃ (V : Set (EC n)) (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
      (R : L2 (EC n) →L[ℂ] L2 (EC n)) (C : ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ 0 < C ∧
      (∀ k l, (c k l : EC n → ℂ).HasTemperateGrowth) ∧
      (∀ y ∈ V, ∀ k l,
        c k l y = (traceBilin (H y) (rankTwo
          (stdOrthonormalBasis ℝ (EC n) k) (stdOrthonormalBasis ℝ (EC n) l)) : ℂ)) ∧
      (∀ f, realize 2 (R f) - chartDifferential c (realize 2 (R f)) = (f : 𝓢'(EC n, ℂ))) ∧
      (∀ f, ‖R f‖ ≤ C * ‖f‖) ∧
      (∀ (u f : L2 (EC n)), realize 2 u - chartDifferential c (realize 2 u) = (f : 𝓢'(EC n, ℂ)) →
        u = R f) := by
  let b := stdOrthonormalBasis ℝ (EC n)
  obtain ⟨a, hat, _, has, hag⟩ := local_coefficient_extension hU H hH hh hx b
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hag)
  let R := localResolvent (H x) (hh x hx) b a has
  let C := ellipticBound (H x) (hh x hx) /
    (1 - perturbationBound b a * ellipticBound (H x) (hh x hx))
  have hC : 0 < C := div_pos (ellipticBound_pos _ _) (sub_pos.mpr has)
  refine ⟨V, extendedCoefficient (H x) a, R, C, hVo, hxV,
    fun y hy => (hV hy).1, hC, extendedCoefficient_temperate _ _ hat, ?_, ?_, ?_, ?_⟩
  · intro y hy k l
    change (_ : ℂ) + a k l y = _
    rw [(hV hy).2 k l]
    simp [b]
  · intro f
    rw [chartDifferential_extension _ _ hat, ← sub_sub]
    exact localResolvent_equation _ _ _ _ has f
  · intro f
    exact localResolvent_bound _ _ _ _ has f
  · intro u f hu
    rw [chartDifferential_extension _ _ hat, ← sub_sub] at hu
    exact perturbed_unique _ _ _ _ has u _ f hu (localResolvent_equation _ _ _ _ has f)

end MetricLocalization

namespace Anticanonical.SourceSmooth
open EllipticKernel MetricLocalization SobolevChart FrozenPoisson
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

 

theorem KaehlerMetric.chart_parametrix (g : KaehlerMetric A)
    (i : Fin A.count) {x : EC d} (hx : coordinateEquiv d x ∈ (A.chart i).target) :
    ∃ (V : Set (EC d)) (c : BasisIndex d → BasisIndex d → EC d →ᵇ ℂ)
      (R : L2 (EC d) →L[ℂ] L2 (EC d)) (C : ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ (coordinateEquiv d) ⁻¹' (A.chart i).target ∧ 0 < C ∧
      (∀ k l, (c k l : EC d → ℂ).HasTemperateGrowth) ∧
      (∀ y ∈ V, ∀ k l,
        c k l y = (traceBilin (g.matrix i (coordinateEquiv d y)) (rankTwo
          (stdOrthonormalBasis ℝ (EC d) k) (stdOrthonormalBasis ℝ (EC d) l)) : ℂ)) ∧
      (∀ f, realize 2 (R f) - chartDifferential c (realize 2 (R f)) = (f : 𝓢'(EC d, ℂ))) ∧
      (∀ f, ‖R f‖ ≤ C * ‖f‖) ∧
      (∀ (u f : L2 (EC d)), realize 2 u - chartDifferential c (realize 2 u) = (f : 𝓢'(EC d, ℂ)) →
        u = R f) := by
  exact MetricLocalization.chart_parametrix
    ((A.chart i).open_target.preimage (coordinateEquiv d).continuous)
    _ ((g.smooth i).comp (coordinateEquiv d).contDiff.contDiffOn (fun _ h => h))
    (fun y hy => g.positive i _ hy) hx

end Anticanonical.SourceSmooth

end
end

end OAI
