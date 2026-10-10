import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.DualEnergyInverse
import OAI.Geometry.TamingCompatibility.Charts.CriticalChartPairing

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ComplexMatrix
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
local instance : Fact ((1 : ENNReal) ≤ ENNReal.ofReal (4/3:ℝ)) := ⟨by norm_num⟩

include hD in

theorem geometric_critical_inverse :
    ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
      (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
        ⟪f-(harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
      (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
      ∀ (p : A.centers) (τ : 𝓢(Space,ℝ)) (U : Set Space)
        (hUD : U ⊆ (D p).domain)
        (_hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space,ℝ))
          (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U) (j : Fin 2),
          ‖G (smoothL2 A J α hs ht true
            (testAnti A J α hs ht D p (componentTest j φ)
              (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))).val)‖ ≤
          C * ‖(densityTest A J α hs ht D p φ hc (hφU.trans hUD)).toLp
            (ENNReal.ofReal (4/3:ℝ)) (volume : Measure Space)‖ := by
  obtain ⟨G,C,hC,hw,ho,hb⟩ := geometric_dual_energy_inverse A J α hs ht D hD
  refine ⟨G,hw,ho,fun p τ U hUD hτ => ?_⟩
  obtain ⟨K,hK,hpair⟩ := critical_chart_pairing A J α hs ht D hD p τ hUD hτ
  refine ⟨C*K,mul_nonneg hC.le hK,fun φ hc hφU j => ?_⟩
  have h := hb (smoothL2 A J α hs ht true
    (testAnti A J α hs ht D p (componentTest j φ)
      (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD))).val)
    (K * ‖(densityTest A J α hs ht D p φ hc (hφU.trans hUD)).toLp
      (ENNReal.ofReal (4/3:ℝ)) volume‖) (mul_nonneg hK (norm_nonneg _))
    (hpair φ hc hφU j)
  simpa only [mul_assoc] using h
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.CriticalSobolev
open MeasureTheory
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
local instance : Fact ((1 : ENNReal) ≤ ENNReal.ofReal (4/3:ℝ)) := ⟨by norm_num⟩

lemma schwartz_LfourThirds_support_scale (hdim : Module.finrank ℝ E = 4)
    (φ : 𝓢(E,ℝ)) (p : E) {r M : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hs : tsupport φ ⊆ Metric.ball p r) (hb : ∀ x, |φ x| ≤ M) :
    ‖φ.toLp (ENNReal.ofReal (4/3:ℝ)) (volume : Measure E)‖ ≤
      M * ((Real.pi^2/2) ^ (3/4:ℝ)) * r^3 := by
  have he : eLpNorm φ (ENNReal.ofReal (4/3:ℝ)) volume ≤
      ENNReal.ofReal M * volume (Metric.ball p r) ^ (3/4:ℝ) := by
    have h := eLpNorm_sub_le_of_dist_bdd (volume : Measure E)
      (p := ENNReal.ofReal (4/3:ℝ)) (by norm_num) measurableSet_ball.nullMeasurableSet hM
      (f := (φ : E → ℝ)) (g := 0)
      (φ.continuous.aestronglyMeasurable.sub aestronglyMeasurable_zero)
      (fun x => by simpa [Real.dist_eq] using hb x)
      ((subset_tsupport _).trans hs) (by simp)
    norm_num at h ⊢
    exact h
  have hvol : volume (Metric.ball p r) = ENNReal.ofReal r ^ 4 *
      ENNReal.ofReal (Real.pi^2/2) := by
    have h := InnerProductSpace.volume_ball_of_dim_even (E := E) (k := 2)
      (by omega : Module.finrank ℝ E = 2*2) p r
    simpa [hdim,Nat.factorial] using h
  have hfin : ENNReal.ofReal M * volume (Metric.ball p r) ^ (3/4:ℝ) ≠ ⊤ := by
    rw [hvol]
    finiteness
  have h := ENNReal.toReal_mono hfin he
  rw [SchwartzMap.norm_toLp]
  apply h.trans_eq
  rw [hvol,ENNReal.toReal_mul,← ENNReal.toReal_rpow,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hr,ENNReal.toReal_ofReal hM,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi^2/2),
    Real.mul_rpow (by positivity) (by positivity)]
  have hp : (r^4) ^ (3/4:ℝ) = r^3 := by
    rw [← Real.rpow_natCast r 4,← Real.rpow_mul hr]
    norm_num
  rw [hp]
  ring
end TamingCompatibility.CriticalSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume ComplexMatrix
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
local instance : Fact ((1 : ENNReal) ≤ ENNReal.ofReal (4/3:ℝ)) := ⟨by norm_num⟩

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma densityTest_scale_bound (p : A.centers) {V : Set Space}
    (hV : IsCompact V) (hVD : V ⊆ (D p).domain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
      (hφV : tsupport φ ⊆ V) (q : Space) (r M : ℝ), 0 ≤ r → 0 ≤ M →
      tsupport φ ⊆ Metric.ball q r → (∀ x, |φ x| ≤ M) →
      ‖(densityTest A J α hs ht D p φ hc (hφV.trans hVD)).toLp
        (ENNReal.ofReal (4/3:ℝ)) (volume : Measure Space)‖ ≤ C*M*r^3 := by
  obtain ⟨K,hK⟩ := hV.exists_bound_of_continuousOn
    (((chartDensity_smooth J α hs ht p.val).continuousOn.mono
      (hVD.trans (D p).domain_subset)).const_mul 2)
  let K' := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  refine ⟨K'*(Real.pi^2/2)^(3/4:ℝ),by positivity,fun φ hc hφV q r M hr hM hball hb => ?_⟩
  have hψ : ∀ x, |densityTest A J α hs ht D p φ hc (hφV.trans hVD) x| ≤ M*K' := by
    intro x
    rw [densityTest_apply,abs_mul]
    by_cases hx : x ∈ tsupport φ
    · apply mul_le_mul (hb x) _ (abs_nonneg _) hM
      exact (show |2*chartDensity J α p.val x| ≤ K from hK x (hφV hx)).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx,abs_zero,zero_mul]
      exact mul_nonneg hM hK'
  have h := CriticalSobolev.schwartz_LfourThirds_support_scale
    (E := Space) (by simp [Space]) (densityTest A J α hs ht D p φ hc (hφV.trans hVD)) q
    hr (mul_nonneg hM hK')
    ((densityTest_support A J α hs ht D p φ hc (hφV.trans hVD)).trans hball) hψ
  convert h using 1; ring

variable (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include hD in

theorem geometric_scaled_inverse :
    ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
      (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
        ⟪f-(harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
      (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
      ∀ (p : A.centers) (τ : 𝓢(Space,ℝ)) (V : Set Space)
        (_hV : IsCompact V) (hVD : V ⊆ (D p).domain)
        (_hτ : ∀ z ∈ V, τ z * coordinateWeight A p z = 1),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space,ℝ))
          (hc : HasCompactSupport (φ : Space → ℝ)) (hφV : tsupport φ ⊆ V)
          (j : Fin 2) (q : Space) (r M : ℝ), 0 ≤ r → 0 ≤ M →
          tsupport φ ⊆ Metric.ball q r → (∀ x, |φ x| ≤ M) →
          ‖G (smoothL2 A J α hs ht true
            (testAnti A J α hs ht D p (componentTest j φ)
              (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφV.trans hVD))).val)‖ ≤
          C*M*r^3 := by
  obtain ⟨G,hw,ho,hb⟩ := geometric_critical_inverse A J α hs ht D hD
  refine ⟨G,hw,ho,fun p τ V hV hVD hτ => ?_⟩
  obtain ⟨B,hB,hbound⟩ := hb p τ V hVD hτ
  obtain ⟨K,hK,hscale⟩ := densityTest_scale_bound A J α hs ht D p hV hVD
  refine ⟨B*K,mul_nonneg hB hK,fun φ hc hφV j q r M hr hM hball hφ => ?_⟩
  apply (hbound φ hc hφV j).trans
  have h := mul_le_mul_of_nonneg_left (hscale φ hc hφV q r M hr hM hball hφ) hB
  simpa only [mul_assoc] using h
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
