import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.HilbertImageTotal
import OAI.Geometry.EinsteinFour.HodgeTheory08
import OAI.Geometry.EinsteinFour.ScalarContinuousLift
import OAI.Geometry.EinsteinFour.ScalarLocalHilbertSum
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelSobolev
import OAI.Geometry.EinsteinFour.ScalarRegularity07
import OAI.Geometry.EinsteinFour.WeylEstimates03
import OAI.Geometry.EinsteinFour.WeylEstimates07
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI


section

/-! The connection correction of a locally Sobolev two-form has one lower order
divergence. The witnesses are actual Euclidean L2 functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) (hVK : V ⊆ K)
  (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (b : TwoFormFour)

include hreg in
theorem twoFormFluxCorrection_memSobolev_successor (j : Fin 4) :
    MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2 (twoFormFluxCorrection c S hS hK hKt
      η hη hcη (hηV.trans hVK) b u j) : 𝓢'(FourSpace, ℂ)) := by
  apply scalarReal_memSobolev_finset (n + 1)
  intro i _
  apply twoFormCoefficientPair_memSobolev_integer
    (twoFormFluxCoefficient (g := g) c η b i j)
    (twoFormFluxCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b i j)
    hcη.mul_right.smul_right (n + 1)
  intro r
  rw [twoFormGramCorrectionVector_component]
  exact twoFormGramDerivativeCorrection_memSobolev_integer (n + 1) c S hS hK hKt hVK u hreg
    η hη hcη hηV (twoFormComponentIndex r) i

include hreg in
theorem twoFormFluxCorrection_integer_derivatives :
    ∃ D : Fin 4 → Lp ℝ 2 (volume : Measure FourSpace),
      (∀ j, scalarCoordinateDerivative j (scalarComplexL2
        (twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j) :
          𝓢'(FourSpace, ℂ)) = (scalarComplexL2 (D j) : 𝓢'(FourSpace, ℂ))) ∧
      ∀ j, MemSobolev (n : ℝ) 2 (scalarComplexL2 (D j) : 𝓢'(FourSpace, ℂ)) := by
  have he (j : Fin 4) : ∃ D : Lp ℝ 2 (volume : Measure FourSpace),
      scalarCoordinateDerivative j (scalarComplexL2
        (twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j) :
          𝓢'(FourSpace, ℂ)) = (scalarComplexL2 D : 𝓢'(FourSpace, ℂ)) ∧
      MemSobolev (n : ℝ) 2 (scalarComplexL2 D : 𝓢'(FourSpace, ℂ)) := by
    exact scalar_real_derivative_sobolev n _
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        twoFormFluxCorrection_memSobolev_successor n c S hS hK hKt hVK u hreg η hη hcη hηV b j) j
  choose D hD hregD using he
  exact ⟨D, hD, hregD⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local H3 regularity follows for actual weak harmonic two-forms.
Both the H2 bootstrap and the H1 source are constructed here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp hχ hc hs in
theorem twoFormHarmonic_inner_H3 (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (z₀ : ChartTarget c) (hnear : {z | z ∈ K ∧ χ z = 1} ∈ 𝓝 z₀.val) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K),
      {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val ∧
      ∀ r : Fin 6, ∃ (t : ℝ) (ht : 0 < t),
        (∀ y ∈ closedBall (0 : FourSpace) 1,
          scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
        ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
          tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
          MemSobolev 3 2 (smulLeftCLM ℂ φ (scalarComplexL2
            (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
              (twoFormWeightedComponentL2 c S hK hKt η hη hcη hηK r u)) :
                𝓢'(FourSpace, ℂ))) := by
  obtain ⟨V, hV, hzV, hVK, hχV, hreg⟩ := twoFormRough_inner_H2 c S hS hK hKt χ hχ hc hs
    U hU hUt hKU hp u (twoFormWeitzenbockPotential (twoFormH1ToL2 u)) hu z₀ hnear
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by
    rw [η.tsupport_eq]
    exact hdV
  let hηK : tsupport (η : FourSpace → ℝ) ⊆ K := hηV.trans hVK
  have hηnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val := by
    filter_upwards [η.eventuallyEq_one] with z hz
    exact ⟨hηK (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [show η z = 1 from hz]; norm_num)), hz⟩
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, hηnear, ?_⟩
  intro r
  obtain ⟨F, hFH, hF⟩ := twoFormHarmonic_weightedWeakH1 c S hS hK hKt hVK
    χ hχ hc hs hχV U hU hUt hKU hp u hu hreg η η.contDiff η.hasCompactSupport hηV r
  apply scalarEuclidean_local_H3 g c z₀ {z | z ∈ K ∧ η z = 1} hηnear
    (twoFormWeightedComponentL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK r u) F
    (twoFormWeightedComponent_H1 c S hK hKt η η.contDiff η.hasCompactSupport hηK r u) hFH
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

theorem twoFormHarmonic_actual_local_H3 (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (c : M) (z₀ : ChartTarget c) :
    ∃ (S : Mat4) (_hS : Sᵀ * S = 1) (K : Set FourSpace)
      (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
      (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K),
      ∀ r : Fin 6, ∃ (t : ℝ) (ht : 0 < t),
        (∀ y ∈ closedBall (0 : FourSpace) 1,
          scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
        ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
          tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
          MemSobolev 3 2 (smulLeftCLM ℂ φ (scalarComplexL2
            (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
              (twoFormWeightedComponentL2 c S hK hKt η hη hcη hηK r u)) :
                𝓢'(FourSpace, ℂ))) := by
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hc, hs, hnear⟩ :=
    twoForm_regularity_cutoff o c z₀
  let hct : tsupport χ ⊆ (chartAt FourSpace c).target := hs.trans hUt
  obtain ⟨η, hη, hcη, hηK, _, hreg⟩ := twoFormHarmonic_inner_H3 c S hS hc hct χ hχ hc
    (Subset.refl _) U hU hUt hs hp u hu z₀ hnear
  exact ⟨S, hS, tsupport χ, hc, hct, η, hη, hcη, hηK, hreg⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak harmonic coefficients have continuous local
representatives, obtained from the proved H3 estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp hχ hc hs in
theorem twoFormHarmonic_continuous_coefficients (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (z₀ : ChartTarget c) (hnear : {z | z ∈ K ∧ χ z = 1} ∈ 𝓝 z₀.val) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K),
      ∀ r : Fin 6, ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧ W ⊆ K ∧
        (∀ z ∈ W, η z = 1) ∧ ∃ f : FourSpace → ℝ, ContinuousOn f W ∧
          (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u :
            FourSpace → ℝ) =ᵐ[volume.restrict W] f := by
  obtain ⟨η, hη, hcη, hηK, hηnear, hreg⟩ := twoFormHarmonic_inner_H3 c S hS hK hKt
    χ hχ hc hs U hU hUt hKU hp u hu z₀ hnear
  obtain ⟨Z, hZs, hZo, hzZ⟩ := _root_.mem_nhds_iff.mp hηnear
  refine ⟨η, hη, hcη, hηK, ?_⟩
  intro r
  obtain ⟨t, ht, hpoint, hregt⟩ := hreg r
  let w := scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
    (twoFormWeightedComponentL2 c S hK hKt η hη hcη hηK r u)
  obtain ⟨G, hG, hwG⟩ := scalar_local_H3_continuous_real_representative w hregt
  have he : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ t y) *
      twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u
        (scalarRescaledPoint g c z₀ t y)) =ᵐ[volume.restrict (ball (0 : FourSpace) (1 / 4))] G := by
    have he' : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ t y) *
        twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u
          (scalarRescaledPoint g c z₀ t y)) =ᵐ[volume.restrict (ball (0 : FourSpace) (1 / 4))] w :=
      ae_restrict_of_ae_restrict_of_subset
        (ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1))
        (twoFormWeightedComponent_rescaled_coe c S hK hKt η hη hcη hηK r u z₀ t ht.ne' hpoint)
    exact he'.trans hwG
  obtain ⟨W, hW, hzW, _, f, hf, heq⟩ := scalar_euclidean_continuous_unweight g c z₀ t ht
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u)
    (fun y hy => hKt (hpoint y hy).1) G hG he
  refine ⟨W ∩ Z, hW.inter hZo, ⟨hzW, hzZ⟩,
    fun z hz => (hZs hz.2).1, fun z hz => (hZs hz.2).2,
    f, hf.mono inter_subset_left, ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset inter_subset_left heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The lower-order harmonic source has one fewer derivative than the
locally controlled two-form, at every finite order used by the bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (b : TwoFormFour)

include hreg in
theorem twoFormInnerNabla_component_integer (i : Fin 4) (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
        𝓢'(FourSpace, ℂ)) := by
  dsimp only [twoFormGramNablaL2]
  rw [twoFormVectorComponentL2_assemble]
  exact twoFormGramCovariant_memSobolev_integer n c S hS hK hKt hVK u η hη hcη hηV
    (twoFormComponentIndex r) i hreg

include hV hreg in
theorem twoFormHarmonicDivergenceSource_integer :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
        (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
          (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
        (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
      𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  apply MemSobolev.sub
  · apply twoFormCoefficientPair_memSobolev_integer
      (twoFormMassCoefficient (g := g) c η b)
      (twoFormMassCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b)
      hcη.mul_right.smul_right n
    intro r
    rw [map_sub]
    change MemSobolev (n : ℝ) 2 (C (_ - _))
    rw [map_sub]
    have hp := (twoFormPotential_local_integer (n + 1) c S hS hK hKt hV hVK u hreg
      η hη hcη hηV r).mono hle
    have hv : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)) : 𝓢'(FourSpace, ℂ)) := by
      rw [twoFormGramVectorComponent]
      exact (hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle
    exact hp.sub hv
  · apply scalarReal_memSobolev_finset n
    intro i _
    exact twoFormCoefficientPair_memSobolev_integer
      (fun z => η z • twoFormWeightedConnection (g := g) c S b i z)
      (twoFormCutoffWeightedConnection_smooth c S hS b i η hη ((hηV.trans hVK).trans hKt))
      hcη.smul_right n _
      (twoFormInnerNabla_component_integer n c S hS hK hKt hVK u hreg η hη hcη hηV i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The linear eigenvalue source in the actual Hodge equation has the finite
Sobolev regularity required by the local elliptic bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o) (κ : ℝ)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hreg in
theorem twoFormEigen_forcing_integer (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
          κ • twoFormH1ToL2 u))) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (twoFormVectorComponentL2 r
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))))
  simp only [map_add]
  exact ((twoFormPotential_local_integer (n + 1) c S hS hK hKt hV hVK u hreg
    η hη hcη hηV r).mono hle).add
      (by
        rw [map_smul, map_smul, twoFormL2GramValue_H1 c S hS, twoFormGramVectorComponent]
        exact scalar_real_sobolev_smul (n : ℝ) κ _
          ((hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle))

include hV hreg in
theorem twoFormEigenDivergenceSource_integer (b : TwoFormFour) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
        (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
          (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
            κ • twoFormH1ToL2 u))
        (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
      𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  apply MemSobolev.sub
  · apply twoFormCoefficientPair_memSobolev_integer
      (twoFormMassCoefficient (g := g) c η b)
      (twoFormMassCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b)
      hcη.mul_right.smul_right n
    intro r
    rw [map_sub]
    change MemSobolev (n : ℝ) 2 (C (_ - _))
    rw [map_sub]
    have hv : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)) : 𝓢'(FourSpace, ℂ)) := by
      rw [twoFormGramVectorComponent]
      exact (hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle
    exact (twoFormEigen_forcing_integer n c S hS hK hKt hV hVK u κ hreg η hη hcη hηV r).sub hv
  · apply scalarReal_memSobolev_finset n
    intro i _
    exact twoFormCoefficientPair_memSobolev_integer
      (fun z => η z • twoFormWeightedConnection (g := g) c S b i z)
      (twoFormCutoffWeightedConnection_smooth c S hS b i η hη ((hηV.trans hVK).trans hKt))
      hcη.smul_right n _
      (twoFormInnerNabla_component_integer n c S hS hK hKt hVK u hreg η hη hcη hηV i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The harmonic equation has actual integer-order forcing in its scalar
principal part. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormHarmonic_principalWeakInteger (b : TwoFormFour) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 R : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD, hDH⟩ := twoFormFluxCorrection_integer_derivatives n c S hS hK hKt hVK u hreg
    η hη hcη hηV b
  let F := fun j => twoFormDivergenceFlux (g := g) c η hη hcη ((hηV.trans hVK).trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
    (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (_ - _))
    rw [map_sub]
    have hsum : MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ j : Fin 4, D j) :
        𝓢'(FourSpace, ℂ)) := by
      apply scalarReal_memSobolev_finset n
      intro j _
      exact hDH j
    exact (twoFormHarmonicDivergenceSource_integer n c S hS hK hKt hV hVK u hreg
      η hη hcη hηV b).sub hsum
  · intro ψ hψ hcψ hψK hon
    have hF := twoFormRough_scalarWeakEquation c S hS η ψ hη hcη hψ hcψ hon b
      hK hKt (hηV.trans hVK) hψK U hU hUt hKU hp u
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u)) hu
    have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
    have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
        ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
          (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
            (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
        (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
        (twoFormPrincipalFlux_eq c S hS hK hKt η hη hcη (hηV.trans hVK) b u j)
    rw [heq] at he
    exact he

include hV hU hKU hp hu hreg in
theorem twoFormHarmonic_weightedWeakInteger (r : Fin 6) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 F : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hRH, hR⟩ := twoFormHarmonic_principalWeakInteger n c S hS hK hKt hV hVK U hU hUt hKU hp u hu hreg η hη hcη hηV
      (EuclideanSpace.basisFun (Fin 6) ℝ r)
  refine ⟨-R, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (-R))
    rw [map_neg]
    exact hRH.neg
  · intro ψ hψ hcψ hψK hon
    have he := hR ψ hψ hcψ hψK hon
    rw [twoFormPrincipalFlux_integrationByParts c η ψ hη hψ hcψ S hK hKt hcη (hηV.trans hVK) u r,
      twoFormWeightedComponent_operator_pairing c S hK hKt η hη hcη (hηV.trans hVK) r u
        ψ hψ hcψ (hψK.trans hKt) hon] at he
    have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
      rw [inner_neg_left]
      linarith only [he]
    rw [hv, L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial]
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth forcing in the actual Hodge-Poisson equation has the finite
Sobolev regularity required by the local elliptic bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o) (w : smoothTwoForms o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hreg in
theorem twoFormPoisson_forcing_integer (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
          smoothTwoFormToL2 (w : SmoothL2TwoForm o)))) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (twoFormVectorComponentL2 r
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (w : SmoothL2TwoForm o)))))
  simp only [map_add]
  exact ((twoFormPotential_local_integer (n + 1) c S hS hK hKt hV hVK u hreg
    η hη hcη hηV r).mono hle).add
      (twoForm_smooth_source_integer n c S hS hK hKt η hη hcη (hηV.trans hVK) w r)

include hV hreg in
theorem twoFormPoissonDivergenceSource_integer (b : TwoFormFour) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
        (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
          (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
            smoothTwoFormToL2 (w : SmoothL2TwoForm o)))
        (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
      𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  apply MemSobolev.sub
  · apply twoFormCoefficientPair_memSobolev_integer
      (twoFormMassCoefficient (g := g) c η b)
      (twoFormMassCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b)
      hcη.mul_right.smul_right n
    intro r
    rw [map_sub]
    change MemSobolev (n : ℝ) 2 (C (_ - _))
    rw [map_sub]
    have hv : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)) : 𝓢'(FourSpace, ℂ)) := by
      rw [twoFormGramVectorComponent]
      exact (hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle
    exact (twoFormPoisson_forcing_integer n c S hS hK hKt hV hVK u w hreg η hη hcη hηV r).sub hv
  · apply scalarReal_memSobolev_finset n
    intro i _
    exact twoFormCoefficientPair_memSobolev_integer
      (fun z => η z • twoFormWeightedConnection (g := g) c S b i z)
      (twoFormCutoffWeightedConnection_smooth c S hS b i η hη ((hηV.trans hVK).trans hKt))
      hcη.smul_right n _
      (twoFormInnerNabla_component_integer n c S hS hK hKt hVK u hreg η hη hcη hηV i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite-regularity source in the actual Hodge equation has the finite
Sobolev regularity required by the local elliptic bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o) (f : TwoFormL2 o)

  (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
        (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hsource hreg in
theorem twoFormRegularSource_forcing_integer (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
          f))) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (twoFormVectorComponentL2 r
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))))
  simp only [map_add]
  exact ((twoFormPotential_local_integer (n + 1) c S hS hK hKt hV hVK u hreg
    η hη hcη hηV r).mono hle).add
      (hsource η hη hcη hηV r)

include hV hsource hreg in
theorem twoFormRegularSourceDivergenceSource_integer (b : TwoFormFour) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
        (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
          (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
            f))
        (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
      𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  apply MemSobolev.sub
  · apply twoFormCoefficientPair_memSobolev_integer
      (twoFormMassCoefficient (g := g) c η b)
      (twoFormMassCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b)
      hcη.mul_right.smul_right n
    intro r
    rw [map_sub]
    change MemSobolev (n : ℝ) 2 (C (_ - _))
    rw [map_sub]
    have hv : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)) : 𝓢'(FourSpace, ℂ)) := by
      rw [twoFormGramVectorComponent]
      exact (hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle
    exact (twoFormRegularSource_forcing_integer n c S hS hK hKt hV hVK u f hsource hreg η hη hcη hηV r).sub hv
  · apply scalarReal_memSobolev_finset n
    intro i _
    exact twoFormCoefficientPair_memSobolev_integer
      (fun z => η z • twoFormWeightedConnection (g := g) c S b i z)
      (twoFormCutoffWeightedConnection_smooth c S hS b i η hη ((hηV.trans hVK).trans hKt))
      hcη.smul_right n _
      (twoFormInnerNabla_component_integer n c S hS hK hKt hVK u hreg η hη hcη hηV i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The linear-eigenvalue Hodge equation has actual integer-order forcing in its scalar
principal part. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (κ : ℝ)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormEigen_principalWeakInteger (b : TwoFormFour) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 R : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD, hDH⟩ := twoFormFluxCorrection_integer_derivatives n c S hS hK hKt hVK u hreg
    η hη hcη hηV b
  let F := fun j => twoFormDivergenceFlux (g := g) c η hη hcη ((hηV.trans hVK).trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
    (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (_ - _))
    rw [map_sub]
    have hsum : MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ j : Fin 4, D j) :
        𝓢'(FourSpace, ℂ)) := by
      apply scalarReal_memSobolev_finset n
      intro j _
      exact hDH j
    exact (twoFormEigenDivergenceSource_integer n c S hS hK hKt hV hVK u κ hreg
      η hη hcη hηV b).sub hsum
  · intro ψ hψ hcψ hψK hon
    have hF := twoFormRough_scalarWeakEquation c S hS η ψ hη hcη hψ hcψ hon b
      hK hKt (hηV.trans hVK) hψK U hU hUt hKU hp u
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u) hu
    have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
    have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
        ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
          (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
            (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
        (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
        (twoFormPrincipalFlux_eq c S hS hK hKt η hη hcη (hηV.trans hVK) b u j)
    rw [heq] at he
    exact he

include hV hU hKU hp hu hreg in
theorem twoFormEigen_weightedWeakInteger (r : Fin 6) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 F : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hRH, hR⟩ := twoFormEigen_principalWeakInteger n c S hS hK hKt hV hVK U hU hUt hKU hp u κ hu hreg η hη hcη hηV
      (EuclideanSpace.basisFun (Fin 6) ℝ r)
  refine ⟨-R, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (-R))
    rw [map_neg]
    exact hRH.neg
  · intro ψ hψ hcψ hψK hon
    have he := hR ψ hψ hcψ hψK hon
    rw [twoFormPrincipalFlux_integrationByParts c η ψ hη hψ hcψ S hK hKt hcη (hηV.trans hVK) u r,
      twoFormWeightedComponent_operator_pairing c S hK hKt η hη hcη (hηV.trans hVK) r u
        ψ hψ hcψ (hψK.trans hKt) hon] at he
    have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
      rw [inner_neg_left]
      linarith only [he]
    rw [hv, L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial]
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual local elliptic step for harmonic two-forms at any finite
Sobolev order, with the metric coefficients and forcing from the Hodge equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormHarmonic_weighted_integer (r : Fin 6) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
      ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
        tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev ((n + 2 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
            (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u)) :
              𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, hFH, hF⟩ := twoFormHarmonic_weightedWeakInteger n c S hS hK hKt hV hVK
    U hU hUt hKU hp u hu hreg η hη hcη hηV r
  apply scalarEuclidean_local_integer n g c z₀ {z | z ∈ K ∧ η z = 1} hnear
    (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u) F
    (twoFormWeightedComponent_H1 c S hK hKt η hη hcη (hηV.trans hVK) r u) hFH
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The smooth-source Hodge-Poisson equation has actual integer-order forcing in its scalar
principal part. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (f : smoothTwoForms o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormPoisson_principalWeakInteger (b : TwoFormFour) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 R : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD, hDH⟩ := twoFormFluxCorrection_integer_derivatives n c S hS hK hKt hVK u hreg
    η hη hcη hηV b
  let F := fun j => twoFormDivergenceFlux (g := g) c η hη hcη ((hηV.trans hVK).trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
    (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (_ - _))
    rw [map_sub]
    have hsum : MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ j : Fin 4, D j) :
        𝓢'(FourSpace, ℂ)) := by
      apply scalarReal_memSobolev_finset n
      intro j _
      exact hDH j
    exact (twoFormPoissonDivergenceSource_integer n c S hS hK hKt hV hVK u f hreg
      η hη hcη hηV b).sub hsum
  · intro ψ hψ hcψ hψK hon
    have hF := twoFormRough_scalarWeakEquation c S hS η ψ hη hcη hψ hcψ hon b
      hK hKt (hηV.trans hVK) hψK U hU hUt hKU hp u
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)) hu
    have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
    have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
        ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
          (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
            (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
        (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
        (twoFormPrincipalFlux_eq c S hS hK hKt η hη hcη (hηV.trans hVK) b u j)
    rw [heq] at he
    exact he

include hV hU hKU hp hu hreg in
theorem twoFormPoisson_weightedWeakInteger (r : Fin 6) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 F : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hRH, hR⟩ := twoFormPoisson_principalWeakInteger n c S hS hK hKt hV hVK U hU hUt hKU hp u f hu hreg η hη hcη hηV
      (EuclideanSpace.basisFun (Fin 6) ℝ r)
  refine ⟨-R, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (-R))
    rw [map_neg]
    exact hRH.neg
  · intro ψ hψ hcψ hψK hon
    have he := hR ψ hψ hcψ hψK hon
    rw [twoFormPrincipalFlux_integrationByParts c η ψ hη hψ hcψ S hK hKt hcη (hηV.trans hVK) u r,
      twoFormWeightedComponent_operator_pairing c S hK hKt η hη hcη (hηV.trans hVK) r u
        ψ hψ hcψ (hψK.trans hKt) hon] at he
    have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
      rw [inner_neg_left]
      linarith only [he]
    rw [hv, L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial]
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite-regularity-source Hodge equation has actual integer-order forcing in its scalar
principal part. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (f : TwoFormL2 o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))

  (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
        (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hsource hreg in
theorem twoFormRegularSource_principalWeakInteger (b : TwoFormFour) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 R : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD, hDH⟩ := twoFormFluxCorrection_integer_derivatives n c S hS hK hKt hVK u hreg
    η hη hcη hηV b
  let F := fun j => twoFormDivergenceFlux (g := g) c η hη hcη ((hηV.trans hVK).trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
    (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (_ - _))
    rw [map_sub]
    have hsum : MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ j : Fin 4, D j) :
        𝓢'(FourSpace, ℂ)) := by
      apply scalarReal_memSobolev_finset n
      intro j _
      exact hDH j
    exact (twoFormRegularSourceDivergenceSource_integer n c S hS hK hKt hV hVK u f hsource hreg
      η hη hcη hηV b).sub hsum
  · intro ψ hψ hcψ hψK hon
    have hF := twoFormRough_scalarWeakEquation c S hS η ψ hη hcη hψ hcψ hon b
      hK hKt (hηV.trans hVK) hψK U hU hUt hKU hp u
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f) hu
    have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
    have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
        ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
          (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
            (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
        (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
        (twoFormPrincipalFlux_eq c S hS hK hKt η hη hcη (hηV.trans hVK) b u j)
    rw [heq] at he
    exact he

include hV hU hKU hp hu hsource hreg in
theorem twoFormRegularSource_weightedWeakInteger (r : Fin 6) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 F : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hRH, hR⟩ := twoFormRegularSource_principalWeakInteger n c S hS hK hKt hV hVK U hU hUt hKU hp u f hu hsource hreg η hη hcη hηV
      (EuclideanSpace.basisFun (Fin 6) ℝ r)
  refine ⟨-R, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (-R))
    rw [map_neg]
    exact hRH.neg
  · intro ψ hψ hcψ hψK hon
    have he := hR ψ hψ hcψ hψK hon
    rw [twoFormPrincipalFlux_integrationByParts c η ψ hη hψ hcψ S hK hKt hcη (hηV.trans hVK) u r,
      twoFormWeightedComponent_operator_pairing c S hK hKt η hη hcη (hηV.trans hVK) r u
        ψ hψ hcψ (hψK.trans hKt) hon] at he
    have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
      rw [inner_neg_left]
      linarith only [he]
    rw [hv, L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial]
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual local elliptic step for linear-eigenvalue Hodge two-forms at any finite
Sobolev order, with the metric coefficients and forcing from the Hodge equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (κ : ℝ)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormEigen_weighted_integer (r : Fin 6) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
      ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
        tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev ((n + 2 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
            (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u)) :
              𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, hFH, hF⟩ := twoFormEigen_weightedWeakInteger n c S hS hK hKt hV hVK
    U hU hUt hKU hp u κ hu hreg η hη hcη hηV r
  apply scalarEuclidean_local_integer n g c z₀ {z | z ∈ K ∧ η z = 1} hnear
    (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u) F
    (twoFormWeightedComponent_H1 c S hK hKt η hη hcη (hηV.trans hVK) r u) hFH
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A harmonic two-form with local H^(n+1) control has actual H^(n+2)
representatives near each point, in the original chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_improved_representative (n : ℕ) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) {K V : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
    (r : Fin 6) (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
          (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ) := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val := by
    filter_upwards [η.eventuallyEq_one] with z hz
    exact ⟨hηK (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [show η z = 1 from hz]; norm_num)), hz⟩
  obtain ⟨t, ht, hpoint, hgain⟩ := twoFormHarmonic_weighted_integer n c S hS hK hKt hV hVK
    U hU hUt hKU hp u hu hreg η η.contDiff η.hasCompactSupport hηV r z₀ hnear
  let A := scalarRescalingLinearEquiv g c z₀ t ht.ne'
  let β : ContDiffBump (0 : FourSpace) :=
    { rIn := 1 / 8
      rOut := 1 / 4
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hsβ : tsupport (β : FourSpace → ℝ) ⊆ ball (0 : FourSpace) (1 / 2) := by
    rw [β.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨w, hw, he⟩ := twoFormInteger_unweight_unscale c S hK hKt η η.contDiff η.hasCompactSupport
    hηK r u z₀ t ht.ne' hpoint (n + 2) hgain β β.contDiff β.hasCompactSupport hsβ
  let W : Set FourSpace := (fun z => A.symm (z - z₀)) ⁻¹' ball 0 (1 / 8)
  have hW : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have hzW : z₀.val ∈ W := by
    dsimp only [W]
    simp only [Set.mem_preimage, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ t (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ t ht.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hone (z : FourSpace) (hz : z ∈ W) : η z = 1 := by
    have hpz := hpoint (A.symm (z - z₀))
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
    rw [hinv] at hpz
    exact hpz.2
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, W, hW, hzW, ?_, hone, w, hw, ?_⟩
  · intro z hz
    exact hηV (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [hone z hz]; norm_num))
  · filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [hz, β.one_of_mem_closedBall (ball_subset_closedBall hzW), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual local elliptic step for smooth-source Hodge-Poisson two-forms at any finite
Sobolev order, with the metric coefficients and forcing from the Hodge equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (f : smoothTwoForms o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormPoisson_weighted_integer (r : Fin 6) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
      ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
        tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev ((n + 2 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
            (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u)) :
              𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, hFH, hF⟩ := twoFormPoisson_weightedWeakInteger n c S hS hK hKt hV hVK
    U hU hUt hKU hp u f hu hreg η hη hcη hηV r
  apply scalarEuclidean_local_integer n g c z₀ {z | z ∈ K ∧ η z = 1} hnear
    (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u) F
    (twoFormWeightedComponent_H1 c S hK hKt η hη hcη (hηV.trans hVK) r u) hFH
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual local elliptic step for finite-regularity-source Hodge two-forms at any finite
Sobolev order, with the metric coefficients and forcing from the Hodge equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (f : TwoFormL2 o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))

  (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
        (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hsource hreg in
theorem twoFormRegularSource_weighted_integer (r : Fin 6) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
      ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
        tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev ((n + 2 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
            (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u)) :
              𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, hFH, hF⟩ := twoFormRegularSource_weightedWeakInteger n c S hS hK hKt hV hVK
    U hU hUt hKU hp u f hu hsource hreg η hη hcη hηV r
  apply scalarEuclidean_local_integer n g c z₀ {z | z ∈ K ∧ η z = 1} hnear
    (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u) F
    (twoFormWeightedComponent_H1 c S hK hKt η hη hcη (hηV.trans hVK) r u) hFH
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A linear-eigenvalue Hodge two-form with local H^(n+1) control has actual H^(n+2)
representatives near each point, in the original chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_improved_representative (n : ℕ) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) {K V : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
    (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
    (r : Fin 6) (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
          (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ) := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val := by
    filter_upwards [η.eventuallyEq_one] with z hz
    exact ⟨hηK (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [show η z = 1 from hz]; norm_num)), hz⟩
  obtain ⟨t, ht, hpoint, hgain⟩ := twoFormEigen_weighted_integer n c S hS hK hKt hV hVK
    U hU hUt hKU hp u κ hu hreg η η.contDiff η.hasCompactSupport hηV r z₀ hnear
  let A := scalarRescalingLinearEquiv g c z₀ t ht.ne'
  let β : ContDiffBump (0 : FourSpace) :=
    { rIn := 1 / 8
      rOut := 1 / 4
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hsβ : tsupport (β : FourSpace → ℝ) ⊆ ball (0 : FourSpace) (1 / 2) := by
    rw [β.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨w, hw, he⟩ := twoFormInteger_unweight_unscale c S hK hKt η η.contDiff η.hasCompactSupport
    hηK r u z₀ t ht.ne' hpoint (n + 2) hgain β β.contDiff β.hasCompactSupport hsβ
  let W : Set FourSpace := (fun z => A.symm (z - z₀)) ⁻¹' ball 0 (1 / 8)
  have hW : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have hzW : z₀.val ∈ W := by
    dsimp only [W]
    simp only [Set.mem_preimage, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ t (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ t ht.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hone (z : FourSpace) (hz : z ∈ W) : η z = 1 := by
    have hpz := hpoint (A.symm (z - z₀))
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
    rw [hinv] at hpz
    exact hpz.2
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, W, hW, hzW, ?_, hone, w, hw, ?_⟩
  · intro z hz
    exact hηV (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [hone z hz]; norm_num))
  · filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [hz, β.one_of_mem_closedBall (ball_subset_closedBall hzW), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every compact chart cutoff of an actual weak harmonic two-form has
all integer Sobolev orders. The bootstrap stays on a fixed open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_local_all_orders (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u))) :
    ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
  have hreg : ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
    intro n
    induction n with
    | zero =>
        intro a ha hc hs v
        simpa only [Nat.zero_add, Nat.cast_one] using
          twoFormGram_memSobolev_one c S hK hKt a ha hc (hs.trans hVK) v u
    | succ n ih =>
        intro a ha hc hs v
        change MemSobolev ((n + 2 : ℕ) : ℝ) 2 _
        apply twoForm_local_sobolev_assembly (n + 2) c S hS hK hKt hVK u _ a ha hc hs v
        intro r x hx
        let z₀ : ChartTarget c := ⟨x, hKt (hVK hx)⟩
        obtain ⟨η, hη, hcη, hηK, W, hW, hxW, _, hone, w, hw, he⟩ :=
          twoFormHarmonic_improved_representative n c S hS hK hKt hV hVK U hU hUt hKU hp
            u hu ih r z₀ hx
        exact ⟨η, hη, hcη, hηK, W, hW, hxW, hone, w, hw, he⟩
  intro n a ha hc hs v
  exact (hreg n a ha hc hs v).mono (by exact_mod_cast Nat.le_succ n)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth-source Hodge-Poisson two-form with local H^(n+1) control has actual H^(n+2)
representatives near each point, in the original chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_improved_representative (n : ℕ) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) {K V : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
    (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
    (r : Fin 6) (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
          (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ) := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val := by
    filter_upwards [η.eventuallyEq_one] with z hz
    exact ⟨hηK (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [show η z = 1 from hz]; norm_num)), hz⟩
  obtain ⟨t, ht, hpoint, hgain⟩ := twoFormPoisson_weighted_integer n c S hS hK hKt hV hVK
    U hU hUt hKU hp u f hu hreg η η.contDiff η.hasCompactSupport hηV r z₀ hnear
  let A := scalarRescalingLinearEquiv g c z₀ t ht.ne'
  let β : ContDiffBump (0 : FourSpace) :=
    { rIn := 1 / 8
      rOut := 1 / 4
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hsβ : tsupport (β : FourSpace → ℝ) ⊆ ball (0 : FourSpace) (1 / 2) := by
    rw [β.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨w, hw, he⟩ := twoFormInteger_unweight_unscale c S hK hKt η η.contDiff η.hasCompactSupport
    hηK r u z₀ t ht.ne' hpoint (n + 2) hgain β β.contDiff β.hasCompactSupport hsβ
  let W : Set FourSpace := (fun z => A.symm (z - z₀)) ⁻¹' ball 0 (1 / 8)
  have hW : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have hzW : z₀.val ∈ W := by
    dsimp only [W]
    simp only [Set.mem_preimage, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ t (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ t ht.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hone (z : FourSpace) (hz : z ∈ W) : η z = 1 := by
    have hpz := hpoint (A.symm (z - z₀))
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
    rw [hinv] at hpz
    exact hpz.2
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, W, hW, hzW, ?_, hone, w, hw, ?_⟩
  · intro z hz
    exact hηV (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [hone z hz]; norm_num))
  · filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [hz, β.one_of_mem_closedBall (ball_subset_closedBall hzW), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite-regularity-source Hodge two-form with local H^(n+1) control has actual H^(n+2)
representatives near each point, in the original chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormRegularSource_improved_representative (n : ℕ) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) {K V : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))

  (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
        (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
    (r : Fin 6) (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
          (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ) := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val := by
    filter_upwards [η.eventuallyEq_one] with z hz
    exact ⟨hηK (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [show η z = 1 from hz]; norm_num)), hz⟩
  obtain ⟨t, ht, hpoint, hgain⟩ := twoFormRegularSource_weighted_integer n c S hS hK hKt hV hVK
    U hU hUt hKU hp u f hu hsource hreg η η.contDiff η.hasCompactSupport hηV r z₀ hnear
  let A := scalarRescalingLinearEquiv g c z₀ t ht.ne'
  let β : ContDiffBump (0 : FourSpace) :=
    { rIn := 1 / 8
      rOut := 1 / 4
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hsβ : tsupport (β : FourSpace → ℝ) ⊆ ball (0 : FourSpace) (1 / 2) := by
    rw [β.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨w, hw, he⟩ := twoFormInteger_unweight_unscale c S hK hKt η η.contDiff η.hasCompactSupport
    hηK r u z₀ t ht.ne' hpoint (n + 2) hgain β β.contDiff β.hasCompactSupport hsβ
  let W : Set FourSpace := (fun z => A.symm (z - z₀)) ⁻¹' ball 0 (1 / 8)
  have hW : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have hzW : z₀.val ∈ W := by
    dsimp only [W]
    simp only [Set.mem_preimage, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ t (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ t ht.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hone (z : FourSpace) (hz : z ∈ W) : η z = 1 := by
    have hpz := hpoint (A.symm (z - z₀))
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
    rw [hinv] at hpz
    exact hpz.2
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, W, hW, hzW, ?_, hone, w, hw, ?_⟩
  · intro z hz
    exact hηV (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [hone z hz]; norm_num))
  · filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [hz, β.one_of_mem_closedBall (ball_subset_closedBall hzW), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every compact chart cutoff of an actual weak linear-eigenvalue Hodge two-form has
all integer Sobolev orders. The bootstrap stays on a fixed open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_local_all_orders (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u)) :
    ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
  have hreg : ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
    intro n
    induction n with
    | zero =>
        intro a ha hc hs v
        simpa only [Nat.zero_add, Nat.cast_one] using
          twoFormGram_memSobolev_one c S hK hKt a ha hc (hs.trans hVK) v u
    | succ n ih =>
        intro a ha hc hs v
        change MemSobolev ((n + 2 : ℕ) : ℝ) 2 _
        apply twoForm_local_sobolev_assembly (n + 2) c S hS hK hKt hVK u _ a ha hc hs v
        intro r x hx
        let z₀ : ChartTarget c := ⟨x, hKt (hVK hx)⟩
        obtain ⟨η, hη, hcη, hηK, W, hW, hxW, _, hone, w, hw, he⟩ :=
          twoFormEigen_improved_representative n c S hS hK hKt hV hVK U hU hUt hKU hp
            u κ hu ih r z₀ hx
        exact ⟨η, hη, hcη, hηK, W, hW, hxW, hone, w, hw, he⟩
  intro n a ha hc hs v
  exact (hreg n a ha hc hs v).mono (by exact_mod_cast Nat.le_succ n)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth representatives of the six actual harmonic chart coefficients,
on one common neighborhood. All Sobolev estimates come from the weak
harmonic equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_smooth_coefficients (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ F : Fin 6 → FourSpace → ℝ,
          (∀ r, ContDiff ℝ ∞ (F r)) ∧ ∀ r,
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u :
              FourSpace → ℝ) =ᵐ[volume] F r := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hreg (r : Fin 6) (n : ℕ) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)) :=
    twoFormHarmonic_local_all_orders c S hS hK hKt hV hVK U hU hUt hKU hp u hu n
      η η.contDiff η.hasCompactSupport hηV (twoFormComponentIndex r)
  have hrep (r : Fin 6) : ∃ f : FourSpace → ℝ, ContDiff ℝ ∞ f ∧
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u : FourSpace → ℝ) =ᵐ[volume] f := by
    obtain ⟨f, hf, he⟩ := scalar_L2_sobolev_smooth_real_representative
      (scalarComplexL2 (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u)) (hreg r)
    refine ⟨f, hf, ?_⟩
    filter_upwards [he, scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η η.contDiff
      η.hasCompactSupport hηK (twoFormComponentIndex r) u)] with z hz hc
    simpa only [hc, Complex.ofReal_re] using hz
  choose F hF he using hrep
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, ball z₀.val (d / 2), isOpen_ball,
    mem_ball_self (half_pos hd), ?_, ?_, F, hF, he⟩
  · exact (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (half_le_self hd.le))).trans hdV
  · intro z hz
    exact η.one_of_mem_closedBall (ball_subset_closedBall hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every compact chart cutoff of an actual weak smooth-source Hodge-Poisson two-form has
all integer Sobolev orders. The bootstrap stays on a fixed open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_local_all_orders (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o))) :
    ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
  have hreg : ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
    intro n
    induction n with
    | zero =>
        intro a ha hc hs v
        simpa only [Nat.zero_add, Nat.cast_one] using
          twoFormGram_memSobolev_one c S hK hKt a ha hc (hs.trans hVK) v u
    | succ n ih =>
        intro a ha hc hs v
        change MemSobolev ((n + 2 : ℕ) : ℝ) 2 _
        apply twoForm_local_sobolev_assembly (n + 2) c S hS hK hKt hVK u _ a ha hc hs v
        intro r x hx
        let z₀ : ChartTarget c := ⟨x, hKt (hVK hx)⟩
        obtain ⟨η, hη, hcη, hηK, W, hW, hxW, _, hone, w, hw, he⟩ :=
          twoFormPoisson_improved_representative n c S hS hK hKt hV hVK U hU hUt hKU hp
            u f hu ih r z₀ hx
        exact ⟨η, hη, hcη, hηK, W, hW, hxW, hone, w, hw, he⟩
  intro n a ha hc hs v
  exact (hreg n a ha hc hs v).mono (by exact_mod_cast Nat.le_succ n)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite-order local regularity of the actual shifted Hodge resolvent.
The forcing is an H1 section with the indicated local Sobolev order. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def TwoFormChartSobolev (n : ℕ) (c : M) (S : Mat4) {K V : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hVK : V ⊆ K) (u : TwoFormH1 o) : Prop :=
  ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ))

theorem TwoFormChartSobolev.mono {n m : ℕ} {c : M} {S : Mat4} {K V : Set FourSpace}
    {hK : IsCompact K} {hKt : K ⊆ (chartAt FourSpace c).target} {hVK : V ⊆ K}
    {u : TwoFormH1 o} (h : TwoFormChartSobolev m c S hK hKt hVK u) (hnm : n ≤ m) :
    TwoFormChartSobolev n c S hK hKt hVK u := by
  intro a ha hc hs v
  exact (h a ha hc hs v).mono (by exact_mod_cast hnm)

theorem twoFormChartSobolev_one (c : M) (S : Mat4) {K V : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hVK : V ⊆ K) (u : TwoFormH1 o) : TwoFormChartSobolev 1 c S hK hKt hVK u := by
  intro a ha hc hs v
  simpa only [Nat.cast_one] using
    twoFormGram_memSobolev_one c S hK hKt a ha hc (hs.trans hVK) v u

theorem twoFormRegularSource_chart_gain (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))
    (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
        (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
          (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
    (hreg : TwoFormChartSobolev (n + 1) c S hK hKt hVK u) :
    TwoFormChartSobolev (n + 2) c S hK hKt hVK u := by
  intro a ha hc hs v
  apply twoForm_local_sobolev_assembly (n + 2) c S hS hK hKt hVK u _ a ha hc hs v
  intro r x hx
  let z₀ : ChartTarget c := ⟨x, hKt (hVK hx)⟩
  obtain ⟨η, hη, hcη, hηK, W, hW, hxW, _, hone, w, hw, he⟩ :=
    twoFormRegularSource_improved_representative n c S hS hK hKt hV hVK U hU hUt hKU hp
      u f hu hsource hreg r z₀ hx
  exact ⟨η, hη, hcη, hηK, W, hW, hxW, hone, w, hw, he⟩

theorem twoFormShiftedSolution_rough (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedSolution hRic f = twoFormRoughSolution
      (twoFormWeitzenbockPotential (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) +
        (f - twoFormH1ToL2 (twoFormShiftedSolution hRic f))) := by
  apply twoFormRoughSolution_unique
  intro v
  have he := twoFormShiftedSolution_weak hRic f v
  unfold twoFormHodgeForm at he
  rw [inner_add_left, inner_sub_left]
  linarith only [he]

theorem twoFormShiftedSolution_chart_gain (n : ℕ) (hRic : RicciThree g)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (v : TwoFormH1 o) (hv : TwoFormChartSobolev n c S hK hKt hVK v) :
    TwoFormChartSobolev (n + 2) c S hK hKt hVK
      (twoFormShiftedSolution hRic (twoFormH1ToL2 v)) := by
  let u := twoFormShiftedSolution hRic (twoFormH1ToL2 v)
  have hgain (k : ℕ) (hk : k ≤ n) (hu : TwoFormChartSobolev (k + 1) c S hK hKt hVK u) :
      TwoFormChartSobolev (k + 2) c S hK hKt hVK u := by
    apply twoFormRegularSource_chart_gain k c S hS hK hKt hV hVK U hU hUt hKU hp u
      (twoFormH1ToL2 v - twoFormH1ToL2 u) (twoFormShiftedSolution_rough hRic _) _ hu
    intro a ha hc hs r
    let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (k : ℝ) 2 (C (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt a ha hc (hs.trans hVK) hS
        (twoFormH1ToL2 v - twoFormH1ToL2 u))))
    rw [map_sub, map_sub, map_sub, twoFormL2GramValue_H1, twoFormL2GramValue_H1,
      twoFormGramVectorComponent, twoFormGramVectorComponent]
    exact ((hv.mono hk) a ha hc hs (twoFormComponentIndex r)).sub
      ((hu.mono (Nat.le_succ k)) a ha hc hs (twoFormComponentIndex r))
  have hrec (k : ℕ) : k ≤ n → TwoFormChartSobolev (k + 2) c S hK hKt hVK u := by
    induction k with
    | zero =>
        intro hk
        exact hgain 0 hk (twoFormChartSobolev_one c S hK hKt hVK u)
    | succ k ih =>
        intro hk
        exact hgain (k + 1) hk (ih (Nat.le_trans (Nat.le_succ k) hk))
  exact hrec n le_rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth representatives of the six actual linear-eigenvalue Hodge chart coefficients,
on one common neighborhood. All Sobolev estimates come from the weak
harmonic equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_smooth_coefficients (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
    (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ F : Fin 6 → FourSpace → ℝ,
          (∀ r, ContDiff ℝ ∞ (F r)) ∧ ∀ r,
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u :
              FourSpace → ℝ) =ᵐ[volume] F r := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hreg (r : Fin 6) (n : ℕ) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)) :=
    twoFormEigen_local_all_orders c S hS hK hKt hV hVK U hU hUt hKU hp u κ hu n
      η η.contDiff η.hasCompactSupport hηV (twoFormComponentIndex r)
  have hrep (r : Fin 6) : ∃ f : FourSpace → ℝ, ContDiff ℝ ∞ f ∧
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u : FourSpace → ℝ) =ᵐ[volume] f := by
    obtain ⟨f, hf, he⟩ := scalar_L2_sobolev_smooth_real_representative
      (scalarComplexL2 (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u)) (hreg r)
    refine ⟨f, hf, ?_⟩
    filter_upwards [he, scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η η.contDiff
      η.hasCompactSupport hηK (twoFormComponentIndex r) u)] with z hz hc
    simpa only [hc, Complex.ofReal_re] using hz
  choose F hF he using hrep
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, ball z₀.val (d / 2), isOpen_ball,
    mem_ball_self (half_pos hd), ?_, ?_, F, hF, he⟩
  · exact (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (half_le_self hd.le))).trans hdV
  · intro z hz
    exact η.one_of_mem_closedBall (ball_subset_closedBall hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite-order smoothing of the positive-time Hodge heat operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
  {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hV hU hKU hp in
theorem twoFormResolvent_iterate_chart_order (k : ℕ) (f : TwoFormL2 o) :
    TwoFormChartSobolev (2 * k + 1) c S hK hKt hVK
      (twoFormShiftedSolution hRic ((twoFormShiftedResolvent hRic ^ k) f)) := by
  induction k with
  | zero =>
      change TwoFormChartSobolev 1 c S hK hKt hVK (twoFormShiftedSolution hRic f)
      exact twoFormChartSobolev_one c S hK hKt hVK (twoFormShiftedSolution hRic f)
  | succ k ih =>
      have he : twoFormH1ToL2 (twoFormShiftedSolution hRic
          ((twoFormShiftedResolvent hRic ^ k) f)) =
          (twoFormShiftedResolvent hRic ^ (k + 1)) f := by
        rw [pow_succ']
        rfl
      have hg := twoFormShiftedSolution_chart_gain (2 * k + 1) hRic c S hS hK hKt hV hVK
        U hU hUt hKU hp (twoFormShiftedSolution hRic ((twoFormShiftedResolvent hRic ^ k) f)) ih
      rw [he] at hg
      convert hg using 1

include hV hU hKU hp in
theorem twoFormHeatLift_chart_order (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o) (n : ℕ) :
    TwoFormChartSobolev n c S hK hKt hVK (twoFormHeatLift hRic t ht f) := by
  let F := twoFormHeatPowerSource hRic t ht (n + 1) f
  let u := twoFormShiftedSolution hRic ((twoFormShiftedResolvent hRic ^ n) F)
  have he : twoFormH1ToL2 u = twoFormHeat hRic t f := by
    change twoFormShiftedResolvent hRic ((twoFormShiftedResolvent hRic ^ n) F) = _
    have hpw := twoFormHeatPowerSource_resolvent hRic t ht (n + 1) f
    rw [pow_succ'] at hpw
    exact hpw
  have hu : u = twoFormHeatLift hRic t ht f :=
    twoFormH1ToL2_injective hRic (he.trans (twoFormHeatLift_value hRic t ht f).symm)
  have hg := twoFormResolvent_iterate_chart_order hRic c S hS hK hKt hV hVK U hU hUt hKU hp n F
  change TwoFormChartSobolev (2 * n + 1) c S hK hKt hVK u at hg
  rw [hu] at hg
  exact hg.mono (by omega)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth representatives of the six actual smooth-source Hodge-Poisson chart coefficients,
on one common neighborhood. All Sobolev estimates come from the weak
harmonic equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_smooth_coefficients (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
    (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ F : Fin 6 → FourSpace → ℝ,
          (∀ r, ContDiff ℝ ∞ (F r)) ∧ ∀ r,
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u :
              FourSpace → ℝ) =ᵐ[volume] F r := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hreg (r : Fin 6) (n : ℕ) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)) :=
    twoFormPoisson_local_all_orders c S hS hK hKt hV hVK U hU hUt hKU hp u f hu n
      η η.contDiff η.hasCompactSupport hηV (twoFormComponentIndex r)
  have hrep (r : Fin 6) : ∃ f : FourSpace → ℝ, ContDiff ℝ ∞ f ∧
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u : FourSpace → ℝ) =ᵐ[volume] f := by
    obtain ⟨f, hf, he⟩ := scalar_L2_sobolev_smooth_real_representative
      (scalarComplexL2 (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u)) (hreg r)
    refine ⟨f, hf, ?_⟩
    filter_upwards [he, scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η η.contDiff
      η.hasCompactSupport hηK (twoFormComponentIndex r) u)] with z hz hc
    simpa only [hc, Complex.ofReal_re] using hz
  choose F hF he using hrep
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, ball z₀.val (d / 2), isOpen_ball,
    mem_ball_self (half_pos hd), ?_, ?_, F, hF, he⟩
  · exact (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (half_le_self hd.le))).trans hdV
  · intro z hz
    exact η.one_of_mem_closedBall (ball_subset_closedBall hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth local representatives of completed two-forms, characterized
by their actual L2 pairings with compactly supported chart tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_smooth_local_representative (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K W : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηK : tsupport η ⊆ K) (hW : IsOpen W) (hWK : W ⊆ K)
    (hone : ∀ z ∈ W, η z = 1) (u : TwoFormH1 o)
    (F : FourSpace → TwoFormFour) (hF : ContDiff ℝ ∞ F)
    (hrep : twoFormGramVectorL2 c S hK hKt η hη hcη hηK u =ᵐ[volume] F)
    (z₀ : FourSpace) (hzW : z₀ ∈ W) :
    ∃ (Z : Set FourSpace) (v : smoothTwoForms o), IsOpen Z ∧ z₀ ∈ Z ∧ ∃ hZW : Z ⊆ W,
      ∀ (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
        (has : tsupport a ⊆ Z),
        inner ℝ (twoFormH1ToL2 u)
          (smoothTwoFormToL2 (twoFormGramTest o c S a ha hK hKt (has.trans (hZW.trans hWK)))) =
        inner ℝ (smoothTwoFormToL2 v)
          (smoothTwoFormToL2 (twoFormGramTest o c S a ha hK hKt (has.trans (hZW.trans hWK)))) := by
  obtain ⟨d, hd, hdW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hzW)
  let ψ : ContDiffBump z₀ :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  let B : FourSpace → TwoFormFour := fun z => ψ z • F z
  have hB : ContDiff ℝ ∞ B := ψ.contDiff.smul hF
  have hBK : tsupport B ⊆ K := by
    apply (tsupport_smul_subset_left (ψ : FourSpace → ℝ) F).trans
    rw [ψ.tsupport_eq]
    exact hdW.trans hWK
  let v := twoFormGramTest o c S B hB.contDiffOn hK hKt hBK
  let Z := ball z₀ (d / 2)
  have hZW : Z ⊆ W :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hd.le))).trans hdW
  refine ⟨Z, v, isOpen_ball, mem_ball_self (half_pos hd), hZW, ?_⟩
  intro a ha has
  let hasK := has.trans (hZW.trans hWK)
  have hon : ∀ z ∈ tsupport a, η z = 1 := fun z hz => hone z (hZW (has hz))
  have hl := twoFormL2_localTest c S hS hK hKt η hη hcη hηK a ha hasK hon
    (twoFormH1ToL2 u)
  have hr := twoFormL2_localTest c S hS hK hKt η hη hcη hηK a ha hasK hon
    (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
  rw [twoFormL2GramValue_H1] at hl
  have hv : twoFormL2GramValue c S hK hKt η hη hcη hηK hS
      (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) =ᵐ[volume]
      fun z => η z • twoFormChartValue o v.val c S hS z := by
    have he := twoFormL2GramValue_smooth c S hK hKt η hη hcη hηK hS
      (v : SmoothL2TwoForm o)
    have hae : (twoFormL2GramValue c S hK hKt η hη hcη hηK hS
        (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) : FourSpace → TwoFormFour) =ᵐ[volume]
        smoothTwoFormGramL2Linear c S hK hKt η hη hcη hηK (v : SmoothL2TwoForm o) :=
      Filter.Eventually.of_forall (fun z => congrArg
        (fun w : Lp TwoFormFour 2 (volume : Measure FourSpace) => w z) he)
    exact hae.trans (twoFormGramVectorL2_coe c S hS hK hKt η hη hcη hηK (smoothL2AsH1 v))
  have he : inner ℝ (twoFormGramVectorL2 c S hK hKt η hη hcη hηK u)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) hasK)
        (hasK.trans hKt)) =
      inner ℝ (twoFormL2GramValue c S hK hKt η hη hcη hηK hS
        (smoothTwoFormToL2 (v : SmoothL2TwoForm o)))
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) hasK)
        (hasK.trans hKt)) := by
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep, hv, twoFormMassTestL2_coe (g := g) c a ha
      (hK.of_isClosed_subset (isClosed_tsupport a) hasK) (hasK.trans hKt)] with z hu hv hm
    rw [hu, hv, hm]
    by_cases hz : z ∈ tsupport a
    · have hzZ := has hz
      have hzK := hasK hz
      have hψ : ψ z = 1 := ψ.one_of_mem_closedBall (ball_subset_closedBall hzZ)
      have hvz : twoFormChartValue o v.val c S hS z = B z :=
        twoFormGramTest_value c S hS B hB.contDiffOn hK hKt hBK z (hKt hzK)
      rw [hvz, hon z hz, one_smul]
      change inner ℝ (F z) _ = inner ℝ (ψ z • F z) _
      rw [hψ, one_smul]
    · have haz := image_eq_zero_of_notMem_tsupport hz
      simp only [twoFormMassTest, haz, smul_zero, inner_zero_right]
  exact hl.trans ((congrArg (fun r : ℝ => (normalizedChartFactor g).toReal * r) he).trans hr.symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual weak linear-eigenvalue Hodge two-form agrees locally, in all smooth
test pairings, with a constructed smooth global section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_local_smooth (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u)) (x : M) :
    ∃ (O : Set M) (v : smoothTwoForms o), IsOpen O ∧ x ∈ O ∧
      ∀ w : smoothTwoForms o, tsupport w.val ⊆ O →
        inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
          inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
            (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨η, hη, hcη, hηK, W, hW, hzW, hWV, hone, F, hF, heF⟩ :=
    twoFormEigen_smooth_coefficients x S hS hcχ hKt hV hVK U hU hUt hχU hp u κ hu z₀ hzV
  let B : FourSpace → TwoFormFour := fun z => WithLp.toLp 2 (fun r => F r z)
  have hB : ContDiff ℝ ∞ B := (contDiff_piLp (p := 2)).mpr hF
  have hrep : twoFormGramVectorL2 x S hcχ hKt η hη hcη hηK u =ᵐ[volume] B :=
    twoFormAssembleL2_coe _ u B heF
  obtain ⟨Z, v, hZ, hzZ, hZW, he⟩ := twoForm_smooth_local_representative x S hS hcχ hKt
    η hη hcη hηK hW (hWV.trans hVK) hone u B hB hrep z₀ hzW
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' Z
  refine ⟨O, v, (chartAt FourSpace x).isOpen_inter_preimage hZ,
    ⟨mem_chart_source FourSpace x, hzZ⟩, ?_⟩
  intro w hw
  have hws : tsupport w.val ⊆ (chartAt FourSpace x).symm '' Z := by
    intro y hy
    exact ⟨chartAt FourSpace x y, (hw hy).2, (chartAt FourSpace x).left_inv (hw hy).1⟩
  obtain ⟨a, ha, has, haw⟩ := twoForm_supported_gramTest x S hS hcχ hKt
    (hZW.trans (hWV.trans hVK)) w hws
  have he' := he a ha has
  have hl : smoothTwoFormToL2 (twoFormGramTest o x S a ha hcχ hKt
      (has.trans (hZW.trans (hWV.trans hVK)))) = smoothTwoFormToL2 (w : SmoothL2TwoForm o) :=
    congrArg (fun t : smoothTwoForms o => smoothTwoFormToL2 (t : SmoothL2TwoForm o)) haw
  exact (congrArg (fun t : TwoFormL2 o => inner ℝ (twoFormH1ToL2 u) t) hl).symm.trans
    (he'.trans (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) t) hl))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual weak harmonic two-form agrees locally, in all smooth
test pairings, with a constructed smooth global section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_local_smooth (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u))) (x : M) :
    ∃ (O : Set M) (v : smoothTwoForms o), IsOpen O ∧ x ∈ O ∧
      ∀ w : smoothTwoForms o, tsupport w.val ⊆ O →
        inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
          inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
            (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨η, hη, hcη, hηK, W, hW, hzW, hWV, hone, F, hF, heF⟩ :=
    twoFormHarmonic_smooth_coefficients x S hS hcχ hKt hV hVK U hU hUt hχU hp u hu z₀ hzV
  let B : FourSpace → TwoFormFour := fun z => WithLp.toLp 2 (fun r => F r z)
  have hB : ContDiff ℝ ∞ B := (contDiff_piLp (p := 2)).mpr hF
  have hrep : twoFormGramVectorL2 x S hcχ hKt η hη hcη hηK u =ᵐ[volume] B :=
    twoFormAssembleL2_coe _ u B heF
  obtain ⟨Z, v, hZ, hzZ, hZW, he⟩ := twoForm_smooth_local_representative x S hS hcχ hKt
    η hη hcη hηK hW (hWV.trans hVK) hone u B hB hrep z₀ hzW
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' Z
  refine ⟨O, v, (chartAt FourSpace x).isOpen_inter_preimage hZ,
    ⟨mem_chart_source FourSpace x, hzZ⟩, ?_⟩
  intro w hw
  have hws : tsupport w.val ⊆ (chartAt FourSpace x).symm '' Z := by
    intro y hy
    exact ⟨chartAt FourSpace x y, (hw hy).2, (chartAt FourSpace x).left_inv (hw hy).1⟩
  obtain ⟨a, ha, has, haw⟩ := twoForm_supported_gramTest x S hS hcχ hKt
    (hZW.trans (hWV.trans hVK)) w hws
  have he' := he a ha has
  have hl : smoothTwoFormToL2 (twoFormGramTest o x S a ha hcχ hKt
      (has.trans (hZW.trans (hWV.trans hVK)))) = smoothTwoFormToL2 (w : SmoothL2TwoForm o) :=
    congrArg (fun t : smoothTwoForms o => smoothTwoFormToL2 (t : SmoothL2TwoForm o)) haw
  exact (congrArg (fun t : TwoFormL2 o => inner ℝ (twoFormH1ToL2 u) t) hl).symm.trans
    (he'.trans (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) t) hl))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local heat coefficients are bounded continuous functions, with a bound
by the L2 norm of the initial section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap NNReal BoundedContinuousFunction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
  (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
  {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
  (hs : tsupport a ⊆ V) (r : Fin 6)

def twoFormHeatChartL2 : TwoFormL2 o →L[ℝ] Lp ℂ 2 (volume : Measure FourSpace) :=
  (Complex.ofRealCLM.compLpL 2 volume).comp
    ((twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) (twoFormComponentIndex r)).comp
      (twoFormHeatLift hRic t ht))

include hV hU hKU hp in
theorem twoFormHeatChartL2_regular (f : TwoFormL2 o) :
    MemSobolev 3 2 (twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r f :
      𝓢'(FourSpace, ℂ)) := by
  exact twoFormHeatLift_chart_order hRic c S hS hK hKt hV hVK U hU hUt hKU hp t ht f 3
    a ha hc hs (twoFormComponentIndex r)

def twoFormHeatChartContinuous : TwoFormL2 o →L[ℝ] (FourSpace →ᵇ ℂ) :=
  scalarH3ContinuousLift (twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r)
    (twoFormHeatChartL2_regular hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r)

theorem twoFormHeatChartContinuous_ae (f : TwoFormL2 o) :
    (twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r f : FourSpace → ℂ) =ᵐ[volume]
      twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r f :=
  scalarH3ContinuousLift_ae _ _ f

theorem twoFormHeatChartContinuous_bound (f : TwoFormL2 o) (z : FourSpace) :
    ‖twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r f z‖ ≤
      ‖twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r‖ * ‖f‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm _ z).trans (ContinuousLinearMap.le_opNorm _ f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth representatives of the six actual positive-time Hodge heat chart coefficients,
on one common neighborhood. All Sobolev estimates come from the weak
heat resolvent identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_smooth_coefficients (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (input : TwoFormL2 o)
    (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ F : Fin 6 → FourSpace → ℝ,
          (∀ r, ContDiff ℝ ∞ (F r)) ∧ ∀ r,
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input) :
              FourSpace → ℝ) =ᵐ[volume] F r := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hreg (r : Fin 6) (n : ℕ) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input)) : 𝓢'(FourSpace, ℂ)) :=
    twoFormHeatLift_chart_order hRic c S hS hK hKt hV hVK U hU hUt hKU hp t ht input n
      η η.contDiff η.hasCompactSupport hηV (twoFormComponentIndex r)
  have hrep (r : Fin 6) : ∃ f : FourSpace → ℝ, ContDiff ℝ ∞ f ∧
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input) : FourSpace → ℝ) =ᵐ[volume] f := by
    obtain ⟨f, hf, he⟩ := scalar_L2_sobolev_smooth_real_representative
      (scalarComplexL2 (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input))) (hreg r)
    refine ⟨f, hf, ?_⟩
    filter_upwards [he, scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η η.contDiff
      η.hasCompactSupport hηK (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input))] with z hz hc
    simpa only [hc, Complex.ofReal_re] using hz
  choose F hF he using hrep
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, ball z₀.val (d / 2), isOpen_ball,
    mem_ball_self (half_pos hd), ?_, ?_, F, hF, he⟩
  · exact (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (half_le_self hd.le))).trans hdV
  · intro z hz
    exact η.one_of_mem_closedBall (ball_subset_closedBall hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual weak smooth-source Hodge-Poisson two-form agrees locally, in all smooth
test pairings, with a constructed smooth global section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_local_smooth (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o))) (x : M) :
    ∃ (O : Set M) (v : smoothTwoForms o), IsOpen O ∧ x ∈ O ∧
      ∀ w : smoothTwoForms o, tsupport w.val ⊆ O →
        inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
          inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
            (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨η, hη, hcη, hηK, W, hW, hzW, hWV, hone, F, hF, heF⟩ :=
    twoFormPoisson_smooth_coefficients x S hS hcχ hKt hV hVK U hU hUt hχU hp u f hu z₀ hzV
  let B : FourSpace → TwoFormFour := fun z => WithLp.toLp 2 (fun r => F r z)
  have hB : ContDiff ℝ ∞ B := (contDiff_piLp (p := 2)).mpr hF
  have hrep : twoFormGramVectorL2 x S hcχ hKt η hη hcη hηK u =ᵐ[volume] B :=
    twoFormAssembleL2_coe _ u B heF
  obtain ⟨Z, v, hZ, hzZ, hZW, he⟩ := twoForm_smooth_local_representative x S hS hcχ hKt
    η hη hcη hηK hW (hWV.trans hVK) hone u B hB hrep z₀ hzW
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' Z
  refine ⟨O, v, (chartAt FourSpace x).isOpen_inter_preimage hZ,
    ⟨mem_chart_source FourSpace x, hzZ⟩, ?_⟩
  intro w hw
  have hws : tsupport w.val ⊆ (chartAt FourSpace x).symm '' Z := by
    intro y hy
    exact ⟨chartAt FourSpace x y, (hw hy).2, (chartAt FourSpace x).left_inv (hw hy).1⟩
  obtain ⟨a, ha, has, haw⟩ := twoForm_supported_gramTest x S hS hcχ hKt
    (hZW.trans (hWV.trans hVK)) w hws
  have he' := he a ha has
  have hl : smoothTwoFormToL2 (twoFormGramTest o x S a ha hcχ hKt
      (has.trans (hZW.trans (hWV.trans hVK)))) = smoothTwoFormToL2 (w : SmoothL2TwoForm o) :=
    congrArg (fun t : smoothTwoForms o => smoothTwoFormToL2 (t : SmoothL2TwoForm o)) haw
  exact (congrArg (fun t : TwoFormL2 o => inner ℝ (twoFormH1ToL2 u) t) hl).symm.trans
    (he'.trans (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) t) hl))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual weak linear-eigenvalue Hodge two-forms have smooth global representatives.
A finite partition of unity assembles the local test-pairing identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_smooth_representative (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u)) :
    ∃ v : smoothTwoForms o, twoFormH1ToL2 u = smoothTwoFormToL2 (v : SmoothL2TwoForm o) := by
  choose O v hO hx he using twoFormEigen_local_smooth u κ hu
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let ι := {x : M // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : (univ : Set M) ⊆ ⋃ i : ι, O i.val := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ (fun i : ι => O i.val)
      (fun i => hO i.val) hfinite
  let R : ι → SmoothScalar (M := M) := fun i => ⟨ρ i, (ρ i).contMDiff⟩
  have hR (x : M) : ∑ i : ι, (R i).val x = 1 := by
    simpa only [R, finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  let V : smoothTwoForms o := ∑ i : ι, smoothTwoFormProduct (R i) (v i.val)
  refine ⟨V, twoFormL2_eq_of_smooth_pairings _ _ ?_⟩
  intro w
  have hpart := smoothTwoForm_partition_weights R hR (w : smoothTwoForms o)
  have hsum : smoothTwoFormToL2 w = ∑ i : ι,
      smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o) := by
    have heq := congrArg (fun a : smoothTwoForms o => smoothTwoFormToL2 (a : SmoothL2TwoForm o)) hpart
    exact heq.symm.trans (map_sum smoothTwoFormToL2 _ _)
  calc
    inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 w) =
        ∑ i : ι, inner ℝ (twoFormH1ToL2 u)
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      rw [hsum, inner_sum]
    _ = ∑ i : ι, inner ℝ (smoothTwoFormToL2 (v i.val : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply he i.val
      exact (tsupport_smul_subset_left (R i).val (w : smoothTwoForms o).val).trans (hρ i)
    _ = ∑ i : ι, inner ℝ
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (v i.val) : SmoothL2TwoForm o))
          (smoothTwoFormToL2 w) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (smoothTwoForm_product_inner (R i) (v i.val) (w : smoothTwoForms o)).symm
    _ = inner ℝ (smoothTwoFormToL2 (V : SmoothL2TwoForm o)) (smoothTwoFormToL2 w) := by
      rw [← sum_inner]
      congr 1
      exact (map_sum smoothTwoFormToL2 _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual weak harmonic two-forms have smooth global representatives.
A finite partition of unity assembles the local test-pairing identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_smooth_representative (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u))) :
    ∃ v : smoothTwoForms o, twoFormH1ToL2 u = smoothTwoFormToL2 (v : SmoothL2TwoForm o) := by
  choose O v hO hx he using twoFormHarmonic_local_smooth u hu
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let ι := {x : M // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : (univ : Set M) ⊆ ⋃ i : ι, O i.val := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ (fun i : ι => O i.val)
      (fun i => hO i.val) hfinite
  let R : ι → SmoothScalar (M := M) := fun i => ⟨ρ i, (ρ i).contMDiff⟩
  have hR (x : M) : ∑ i : ι, (R i).val x = 1 := by
    simpa only [R, finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  let V : smoothTwoForms o := ∑ i : ι, smoothTwoFormProduct (R i) (v i.val)
  refine ⟨V, twoFormL2_eq_of_smooth_pairings _ _ ?_⟩
  intro w
  have hpart := smoothTwoForm_partition_weights R hR (w : smoothTwoForms o)
  have hsum : smoothTwoFormToL2 w = ∑ i : ι,
      smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o) := by
    have heq := congrArg (fun a : smoothTwoForms o => smoothTwoFormToL2 (a : SmoothL2TwoForm o)) hpart
    exact heq.symm.trans (map_sum smoothTwoFormToL2 _ _)
  calc
    inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 w) =
        ∑ i : ι, inner ℝ (twoFormH1ToL2 u)
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      rw [hsum, inner_sum]
    _ = ∑ i : ι, inner ℝ (smoothTwoFormToL2 (v i.val : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply he i.val
      exact (tsupport_smul_subset_left (R i).val (w : smoothTwoForms o).val).trans (hρ i)
    _ = ∑ i : ι, inner ℝ
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (v i.val) : SmoothL2TwoForm o))
          (smoothTwoFormToL2 w) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (smoothTwoForm_product_inner (R i) (v i.val) (w : smoothTwoForms o)).symm
    _ = inner ℝ (smoothTwoFormToL2 (V : SmoothL2TwoForm o)) (smoothTwoFormToL2 w) := by
      rw [← sum_inner]
      congr 1
      exact (map_sum smoothTwoFormToL2 _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every positive-time Hodge heat output agrees locally, in all smooth
test pairings, with a constructed smooth global section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_local_smooth (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (input : TwoFormL2 o) (x : M) :
    ∃ (O : Set M) (v : smoothTwoForms o), IsOpen O ∧ x ∈ O ∧
      ∀ w : smoothTwoForms o, tsupport w.val ⊆ O →
        inner ℝ (twoFormH1ToL2 (twoFormHeatLift hRic t ht input)) (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
          inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
            (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨η, hη, hcη, hηK, W, hW, hzW, hWV, hone, F, hF, heF⟩ :=
    twoFormHeat_smooth_coefficients x S hS hcχ hKt hV hVK U hU hUt hχU hp hRic t ht input z₀ hzV
  let B : FourSpace → TwoFormFour := fun z => WithLp.toLp 2 (fun r => F r z)
  have hB : ContDiff ℝ ∞ B := (contDiff_piLp (p := 2)).mpr hF
  have hrep : twoFormGramVectorL2 x S hcχ hKt η hη hcη hηK (twoFormHeatLift hRic t ht input) =ᵐ[volume] B :=
    twoFormAssembleL2_coe _ (twoFormHeatLift hRic t ht input) B heF
  obtain ⟨Z, v, hZ, hzZ, hZW, he⟩ := twoForm_smooth_local_representative x S hS hcχ hKt
    η hη hcη hηK hW (hWV.trans hVK) hone (twoFormHeatLift hRic t ht input) B hB hrep z₀ hzW
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' Z
  refine ⟨O, v, (chartAt FourSpace x).isOpen_inter_preimage hZ,
    ⟨mem_chart_source FourSpace x, hzZ⟩, ?_⟩
  intro w hw
  have hws : tsupport w.val ⊆ (chartAt FourSpace x).symm '' Z := by
    intro y hy
    exact ⟨chartAt FourSpace x y, (hw hy).2, (chartAt FourSpace x).left_inv (hw hy).1⟩
  obtain ⟨a, ha, has, haw⟩ := twoForm_supported_gramTest x S hS hcχ hKt
    (hZW.trans (hWV.trans hVK)) w hws
  have he' := he a ha has
  have hl : smoothTwoFormToL2 (twoFormGramTest o x S a ha hcχ hKt
      (has.trans (hZW.trans (hWV.trans hVK)))) = smoothTwoFormToL2 (w : SmoothL2TwoForm o) :=
    congrArg (fun t : smoothTwoForms o => smoothTwoFormToL2 (t : SmoothL2TwoForm o)) haw
  exact (congrArg (fun z : TwoFormL2 o => inner ℝ (twoFormH1ToL2 (twoFormHeatLift hRic t ht input)) z) hl).symm.trans
    (he'.trans (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) t) hl))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual weak smooth-source Hodge-Poisson two-forms have smooth global representatives.
A finite partition of unity assembles the local test-pairing identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_smooth_representative (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o))) :
    ∃ v : smoothTwoForms o, twoFormH1ToL2 u = smoothTwoFormToL2 (v : SmoothL2TwoForm o) := by
  choose O v hO hx he using twoFormPoisson_local_smooth u f hu
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let ι := {x : M // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : (univ : Set M) ⊆ ⋃ i : ι, O i.val := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ (fun i : ι => O i.val)
      (fun i => hO i.val) hfinite
  let R : ι → SmoothScalar (M := M) := fun i => ⟨ρ i, (ρ i).contMDiff⟩
  have hR (x : M) : ∑ i : ι, (R i).val x = 1 := by
    simpa only [R, finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  let V : smoothTwoForms o := ∑ i : ι, smoothTwoFormProduct (R i) (v i.val)
  refine ⟨V, twoFormL2_eq_of_smooth_pairings _ _ ?_⟩
  intro w
  have hpart := smoothTwoForm_partition_weights R hR (w : smoothTwoForms o)
  have hsum : smoothTwoFormToL2 w = ∑ i : ι,
      smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o) := by
    have heq := congrArg (fun a : smoothTwoForms o => smoothTwoFormToL2 (a : SmoothL2TwoForm o)) hpart
    exact heq.symm.trans (map_sum smoothTwoFormToL2 _ _)
  calc
    inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 w) =
        ∑ i : ι, inner ℝ (twoFormH1ToL2 u)
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      rw [hsum, inner_sum]
    _ = ∑ i : ι, inner ℝ (smoothTwoFormToL2 (v i.val : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply he i.val
      exact (tsupport_smul_subset_left (R i).val (w : smoothTwoForms o).val).trans (hρ i)
    _ = ∑ i : ι, inner ℝ
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (v i.val) : SmoothL2TwoForm o))
          (smoothTwoFormToL2 w) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (smoothTwoForm_product_inner (R i) (v i.val) (w : smoothTwoForms o)).symm
    _ = inner ℝ (smoothTwoFormToL2 (V : SmoothL2TwoForm o)) (smoothTwoFormToL2 w) := by
      rw [← sum_inner]
      congr 1
      exact (map_sum smoothTwoFormToL2 _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak harmonic kernel and the smooth closed and coclosed
two-forms coincide. The equivalence uses proved elliptic regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_smooth_H1 (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    ∃ v : smoothTwoForms o, v ∈ smoothHarmonicTwoForms ∧
      u = smoothTwoFormToH1 (v : SmoothH1TwoForm o) := by
  obtain ⟨v, hv⟩ := twoFormHarmonic_smooth_representative u (twoFormWeakHarmonic_rough u hu)
  have he : u = smoothTwoFormToH1 (v : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hv.trans (twoFormH1ToL2_smooth (v : SmoothH1TwoForm o)).symm)
  have hk : smoothTwoFormToH1 (v : SmoothH1TwoForm o) ∈ twoFormWeitzenbockKernel (o := o) :=
    he ▸ hu
  have hE := (mem_twoFormWeitzenbockKernel_iff_energy_zero hRic _).mp hk
  have henergy : smoothTwoFormDeRhamEnergy v = 0 :=
    (twoFormHodgeForm_smooth hRic (v : SmoothH1TwoForm o)).symm.trans hE
  exact ⟨v, (smoothTwoFormDeRhamEnergy_eq_zero_iff v).mp henergy, he⟩

theorem smoothHarmonicToWeak_surjective (hRic : RicciThree g) :
    Function.Surjective (smoothHarmonicToWeak (o := o) hRic) := by
  intro u
  obtain ⟨v, hv, he⟩ := twoFormHarmonic_smooth_H1 hRic u.val u.property
  refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
  exact he.symm

def smoothHarmonicWeakEquiv (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) ≃ₗ[ℝ] twoFormWeitzenbockKernel (o := o) :=
  LinearEquiv.ofBijective (smoothHarmonicToWeak hRic)
    ⟨smoothHarmonicToWeak_injective hRic, smoothHarmonicToWeak_surjective hRic⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time Hodge heat outputs have smooth global representatives.
A finite partition of unity assembles the local test-pairing identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_smooth_representative (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (input : TwoFormL2 o) :
    ∃ v : smoothTwoForms o, twoFormH1ToL2 (twoFormHeatLift hRic t ht input) = smoothTwoFormToL2 (v : SmoothL2TwoForm o) := by
  choose O v hO hx he using twoFormHeat_local_smooth hRic t ht input
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let ι := {x : M // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : (univ : Set M) ⊆ ⋃ i : ι, O i.val := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ (fun i : ι => O i.val)
      (fun i => hO i.val) hfinite
  let R : ι → SmoothScalar (M := M) := fun i => ⟨ρ i, (ρ i).contMDiff⟩
  have hR (x : M) : ∑ i : ι, (R i).val x = 1 := by
    simpa only [R, finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  let V : smoothTwoForms o := ∑ i : ι, smoothTwoFormProduct (R i) (v i.val)
  refine ⟨V, twoFormL2_eq_of_smooth_pairings _ _ ?_⟩
  intro w
  have hpart := smoothTwoForm_partition_weights R hR (w : smoothTwoForms o)
  have hsum : smoothTwoFormToL2 w = ∑ i : ι,
      smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o) := by
    have heq := congrArg (fun a : smoothTwoForms o => smoothTwoFormToL2 (a : SmoothL2TwoForm o)) hpart
    exact heq.symm.trans (map_sum smoothTwoFormToL2 _ _)
  calc
    inner ℝ (twoFormH1ToL2 (twoFormHeatLift hRic t ht input)) (smoothTwoFormToL2 w) =
        ∑ i : ι, inner ℝ (twoFormH1ToL2 (twoFormHeatLift hRic t ht input))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      rw [hsum, inner_sum]
    _ = ∑ i : ι, inner ℝ (smoothTwoFormToL2 (v i.val : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply he i.val
      exact (tsupport_smul_subset_left (R i).val (w : smoothTwoForms o).val).trans (hρ i)
    _ = ∑ i : ι, inner ℝ
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (v i.val) : SmoothL2TwoForm o))
          (smoothTwoFormToL2 w) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (smoothTwoForm_product_inner (R i) (v i.val) (w : smoothTwoForms o)).symm
    _ = inner ℝ (smoothTwoFormToL2 (V : SmoothL2TwoForm o)) (smoothTwoFormToL2 w) := by
      rw [← sum_inner]
      congr 1
      exact (map_sum smoothTwoFormToL2 _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth Hodge-Poisson solvability for an actual smooth source
orthogonal to the smooth harmonic space. Both weak solvability and
regularity are proved, with no extra analytic premise. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothHodgePoisson (hRic : RicciThree g) (f : smoothTwoForms o)
    (hf : ∀ h ∈ smoothHarmonicTwoForms (o := o), smoothTwoFormL2Inner f h = 0) :
    ∃ u : smoothTwoForms o, ∀ v : TwoFormH1 o,
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) v =
        inner ℝ (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) (twoFormH1ToL2 v) := by
  have hfweak : ∀ v ∈ twoFormWeitzenbockKernel (o := o),
      inner ℝ (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) (twoFormH1ToL2 v) = 0 := by
    intro v hv
    obtain ⟨h, hh, he⟩ := twoFormHarmonic_smooth_H1 hRic v hv
    have hJ : twoFormH1ToL2 v = smoothTwoFormToL2 (h : SmoothL2TwoForm o) :=
      (congrArg twoFormH1ToL2 he).trans (twoFormH1ToL2_smooth (h : SmoothH1TwoForm o))
    exact (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) t) hJ).trans
        ((smoothTwoFormToL2.inner_map_map _ _).trans (hf h hh))
  obtain ⟨u, _, hu⟩ := exists_weakHodgePoisson hRic
    (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) hfweak
  have hrough : u = twoFormRoughSolution
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)) := by
    have h := (twoFormHodgeEquation_rough_iff u (smoothTwoFormToL2 (f : SmoothL2TwoForm o))).mp hu
    simpa only [add_comm] using h
  obtain ⟨v, hv⟩ := twoFormPoisson_smooth_representative u f hrough
  have he : u = smoothTwoFormToH1 (v : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hv.trans (twoFormH1ToL2_smooth (v : SmoothH1TwoForm o)).symm)
  refine ⟨v, ?_⟩
  intro w
  exact (congrArg (fun a : TwoFormH1 o => twoFormHodgeForm a w) he).symm.trans (hu w)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The eigenvalue one of the actual shifted resolvent is exactly the
smooth harmonic space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedSolution_unique (hRic : RicciThree g) (f : TwoFormL2 o)
    (u : TwoFormH1 o)
    (hu : ∀ v, twoFormHodgeForm u v + inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 v) =
      inner ℝ f (twoFormH1ToL2 v)) : u = twoFormShiftedSolution hRic f := by
  apply twoFormShiftedHodge_injective hRic
  apply ext_inner_right ℝ
  intro v
  rw [twoFormShiftedHodge_inner, twoFormShiftedHodge_inner]
  exact (hu v).trans (twoFormShiftedSolution_weak hRic f v).symm

theorem twoFormShiftedSolution_harmonic (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    twoFormShiftedSolution hRic (twoFormH1ToL2 u) = u := by
  symm
  apply twoFormShiftedSolution_unique hRic
  intro v
  rw [twoFormHodgeForm_zero_left hRic u
    ((mem_twoFormWeitzenbockKernel_iff_energy_zero hRic u).mp hu) v, zero_add]

theorem twoFormShiftedResolvent_harmonic (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    twoFormShiftedResolvent hRic (twoFormH1ToL2 u) = twoFormH1ToL2 u := by
  change twoFormH1ToL2 (twoFormShiftedSolution hRic (twoFormH1ToL2 u)) = _
  rw [twoFormShiftedSolution_harmonic hRic u hu]

theorem twoFormShiftedSolution_mem_harmonic (hRic : RicciThree g) (f : TwoFormL2 o)
    (hf : twoFormShiftedResolvent hRic f = f) :
    twoFormShiftedSolution hRic f ∈ twoFormWeitzenbockKernel (o := o) := by
  apply (mem_twoFormWeitzenbockKernel_iff_energy_zero hRic _).mpr
  have he := twoFormShiftedSolution_weak hRic f (twoFormShiftedSolution hRic f)
  change twoFormHodgeForm (twoFormShiftedSolution hRic f) (twoFormShiftedSolution hRic f) +
    inner ℝ (twoFormShiftedResolvent hRic f) (twoFormShiftedResolvent hRic f) =
      inner ℝ f (twoFormShiftedResolvent hRic f) at he
  rw [hf] at he
  linarith only [he]

def twoFormWeakHarmonicToResolvent (hRic : RicciThree g) :
    twoFormWeitzenbockKernel (o := o) →ₗ[ℝ]
      Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1 :=
  (twoFormH1ToL2.toLinearMap.comp (twoFormWeitzenbockKernel (o := o)).subtype).codRestrict _
    (fun u => Module.End.mem_eigenspace_iff.mpr (by
      change twoFormShiftedResolvent hRic (twoFormH1ToL2 u.val) =
        (1 : ℝ) • twoFormH1ToL2 u.val
      rw [one_smul]
      exact twoFormShiftedResolvent_harmonic hRic u.val u.property))

def twoFormWeakHarmonicResolventEquiv (hRic : RicciThree g) :
    twoFormWeitzenbockKernel (o := o) ≃ₗ[ℝ]
      Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1 :=
  LinearEquiv.ofBijective (twoFormWeakHarmonicToResolvent hRic) ⟨by
    intro u v huv
    exact Subtype.ext (twoFormH1ToL2_injective hRic (congrArg Subtype.val huv)), by
    intro f
    have hf := Module.End.mem_eigenspace_iff.mp f.property
    change twoFormShiftedResolvent hRic f.val = (1 : ℝ) • f.val at hf
    rw [one_smul] at hf
    refine ⟨⟨twoFormShiftedSolution hRic f.val,
      twoFormShiftedSolution_mem_harmonic hRic f.val hf⟩, Subtype.ext ?_⟩
    exact hf⟩

def smoothHarmonicResolventEquiv (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) ≃ₗ[ℝ]
      Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1 :=
  (smoothHarmonicWeakEquiv hRic).trans (twoFormWeakHarmonicResolventEquiv hRic)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pointwise Hodge-Poisson solvability and the kernel of the actual
smooth Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_eq_of_pairings (u v : smoothTwoForms o)
    (h : ∀ w : smoothTwoForms o, smoothTwoFormL2Inner u w = smoothTwoFormL2Inner v w) :
    u = v := by
  have he : (u : SmoothL2TwoForm o) = (v : SmoothL2TwoForm o) :=
    @ext_inner_right ℝ (SmoothL2TwoForm o) _ _ _ (u : SmoothL2TwoForm o)
      (v : SmoothL2TwoForm o) (fun w => h (w : smoothTwoForms o))
  exact he

theorem smoothHodgeLaplacian_eq_zero_iff (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic u = 0 ↔ u ∈ smoothHarmonicTwoForms := by
  constructor
  · intro h
    apply (smoothTwoFormDeRhamEnergy_eq_zero_iff u).mp
    have he := (smoothHodgeLaplacian_pairing hRic u u).trans
      (twoFormHodgeForm_smooth hRic (u : SmoothH1TwoForm o))
    rw [h] at he
    exact he.symm.trans (show smoothTwoFormL2Inner (0 : smoothTwoForms o) u = 0 from
      @inner_zero_left ℝ (SmoothL2TwoForm o) _ _ _ (u : SmoothL2TwoForm o))
  · intro hu
    have hE : twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o))
        (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) = 0 :=
      (twoFormHodgeForm_smooth hRic (u : SmoothH1TwoForm o)).trans
        ((smoothTwoFormDeRhamEnergy_eq_zero_iff u).mpr hu)
    apply smoothTwoForm_eq_of_pairings
    intro v
    exact ((smoothHodgeLaplacian_pairing hRic u v).trans
      (twoFormHodgeForm_zero_left hRic _ hE _)).trans
        (@inner_zero_left ℝ (SmoothL2TwoForm o) _ _ _ (v : SmoothL2TwoForm o)).symm

theorem exists_smoothHodgePoisson_pointwise (hRic : RicciThree g)
    (f : smoothTwoForms o)
    (hf : ∀ h ∈ smoothHarmonicTwoForms (o := o), smoothTwoFormL2Inner f h = 0) :
    ∃ u : smoothTwoForms o, smoothHodgeLaplacian hRic u = f := by
  obtain ⟨u, hu⟩ := exists_smoothHodgePoisson hRic f hf
  refine ⟨u, smoothTwoForm_eq_of_pairings _ _ (fun v => ?_)⟩
  have hj : twoFormH1ToL2 (smoothTwoFormToH1 (v : SmoothH1TwoForm o)) =
      smoothTwoFormToL2 (v : SmoothL2TwoForm o) :=
    twoFormH1ToL2_smooth (v : SmoothH1TwoForm o)
  exact (smoothHodgeLaplacian_pairing hRic u v).trans ((hu _).trans
    ((congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) t) hj).trans
        (smoothTwoFormToL2.inner_map_map _ _)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The shifted Hodge resolvent commutes with the actual Hodge
involution. Consequently each finite spectral space is graded. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodgeForm_hodge_left (hRic : RicciThree g) (u v : TwoFormH1 o) :
    twoFormHodgeForm (twoFormH1Hodge u) v = twoFormHodgeForm u (twoFormH1Hodge v) := by
  unfold twoFormHodgeForm
  rw [twoFormH1Hodge_selfAdjoint, twoFormH1ToL2_hodge,
    twoFormWeitzenbockPotential_hodge hRic, twoFormL2Hodge_selfAdjoint, twoFormH1ToL2_hodge]

theorem twoFormShiftedSolution_hodge (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedSolution hRic (twoFormL2Hodge f) =
      twoFormH1Hodge (twoFormShiftedSolution hRic f) := by
  symm
  apply twoFormShiftedSolution_unique hRic
  intro v
  calc
    _ = twoFormHodgeForm (twoFormShiftedSolution hRic f) (twoFormH1Hodge v) +
        inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f))
          (twoFormH1ToL2 (twoFormH1Hodge v)) := by
      rw [twoFormHodgeForm_hodge_left hRic, twoFormH1ToL2_hodge,
        twoFormL2Hodge_selfAdjoint, twoFormH1ToL2_hodge]
    _ = inner ℝ f (twoFormH1ToL2 (twoFormH1Hodge v)) :=
      twoFormShiftedSolution_weak hRic f (twoFormH1Hodge v)
    _ = _ := by rw [twoFormH1ToL2_hodge, twoFormL2Hodge_selfAdjoint]

theorem twoFormShiftedResolvent_hodge (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedResolvent hRic (twoFormL2Hodge f) =
      twoFormL2Hodge (twoFormShiftedResolvent hRic f) := by
  change twoFormH1ToL2 (twoFormShiftedSolution hRic (twoFormL2Hodge f)) = _
  rw [twoFormShiftedSolution_hodge, twoFormH1ToL2_hodge]
  rfl

theorem twoFormResolvent_eigenspace_hodge (hRic : RicciThree g) (μ : ℝ) (f : TwoFormL2 o)
    (hf : f ∈ Module.End.eigenspace (twoFormShiftedResolvent hRic).toLinearMap μ) :
    twoFormL2Hodge f ∈ Module.End.eigenspace (twoFormShiftedResolvent hRic).toLinearMap μ := by
  apply Module.End.mem_eigenspace_iff.mpr
  have he := Module.End.mem_eigenspace_iff.mp hf
  change twoFormShiftedResolvent hRic f = μ • f at he
  change twoFormShiftedResolvent hRic (twoFormL2Hodge f) = μ • twoFormL2Hodge f
  rw [twoFormShiftedResolvent_hodge, he, map_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The large-time heat limit is the actual finite-dimensional harmonic
projection, with a smooth closed and coclosed representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped Manifold ContDiff _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHarmonicWeight (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : ℝ :=
  if μ.val = 1 then 1 else 0

theorem twoFormHarmonicWeight_bound (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : |twoFormHarmonicWeight hRic μ| ≤ 1 := by
  simp only [twoFormHarmonicWeight]
  split_ifs <;> norm_num

def twoFormL2HarmonicProjection (hRic : RicciThree g) : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormSpectralMultiplier hRic (twoFormHarmonicWeight hRic) 1 zero_le_one
    (twoFormHarmonicWeight_bound hRic)

theorem twoFormL2HarmonicProjection_coordinate (hRic : RicciThree g) (f : TwoFormL2 o)
    (μ : TwoFormSpectralValue hRic) :
    (twoFormSpectralEquiv hRic (twoFormL2HarmonicProjection hRic f)) μ =
      twoFormHarmonicWeight hRic μ • (twoFormSpectralEquiv hRic f) μ :=
  twoFormSpectralMultiplier_coordinate hRic _ _ _ _ f μ

theorem twoFormL2HarmonicProjection_fixed (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedResolvent hRic (twoFormL2HarmonicProjection hRic f) =
      twoFormL2HarmonicProjection hRic f := by
  apply (twoFormSpectralEquiv hRic).injective
  apply lp.ext
  funext μ
  rw [twoFormShiftedResolvent_coordinate, twoFormL2HarmonicProjection_coordinate]
  by_cases hμ : μ.val = 1
  · simp [twoFormHarmonicWeight, hμ]
  · simp only [twoFormHarmonicWeight, ite_eq_right hμ, zero_smul, smul_zero]

theorem twoFormL2HarmonicProjection_smooth (hRic : RicciThree g) (f : TwoFormL2 o) :
    ∃ v : smoothTwoForms o, v ∈ smoothHarmonicTwoForms ∧
      twoFormL2HarmonicProjection hRic f = smoothTwoFormToL2 v := by
  let u := twoFormShiftedSolution hRic (twoFormL2HarmonicProjection hRic f)
  have hu := twoFormShiftedSolution_mem_harmonic hRic (twoFormL2HarmonicProjection hRic f)
    (twoFormL2HarmonicProjection_fixed hRic f)
  obtain ⟨v, hv, he⟩ := twoFormHarmonic_smooth_H1 hRic u hu
  refine ⟨v, hv, ?_⟩
  calc
    _ = twoFormH1ToL2 u := (twoFormL2HarmonicProjection_fixed hRic f).symm
    _ = _ := (congrArg twoFormH1ToL2 he).trans
      (twoFormH1ToL2_smooth (v : SmoothH1TwoForm o))

theorem twoFormHeatWeight_tendsto (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    Tendsto (fun t : ℝ≥0 => twoFormHeatWeight hRic t μ) atTop
      (𝓝 (twoFormHarmonicWeight hRic μ)) := by
  by_cases hμ : μ.val = 1
  · have hr := (twoFormHeatRate_eq_zero hRic μ).mpr hμ
    simpa only [twoFormHeatWeight, hr, mul_zero, Real.exp_zero,
      twoFormHarmonicWeight, ite_eq_left hμ] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (1 : ℝ)) atTop (𝓝 1))
  · have hp : 0 < twoFormHeatRate hRic μ := lt_of_le_of_ne
      (twoFormHeatRate_nonneg hRic μ)
      (Ne.symm (mt (twoFormHeatRate_eq_zero hRic μ).mp hμ))
    have ht : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
      NNReal.tendsto_coe_atTop.mpr tendsto_id
    have hn := ht.atTop_mul_const_of_neg (neg_neg_of_pos hp)
    have he := Real.tendsto_exp_atBot.comp hn
    simpa only [Function.comp_def, twoFormHeatWeight, mul_neg, neg_mul,
      twoFormHarmonicWeight, ite_eq_right hμ] using he

theorem twoFormHeat_tendsto_harmonic (hRic : RicciThree g) (f : TwoFormL2 o) :
    Tendsto (fun t : ℝ≥0 => twoFormHeat hRic t f) atTop
      (𝓝 (twoFormL2HarmonicProjection hRic f)) :=
  twoFormSpectralMultiplier_tendsto hRic (twoFormHeatWeight hRic) (twoFormHarmonicWeight hRic)
    (twoFormHeatWeight_bound hRic) (twoFormHarmonicWeight_bound hRic)
    (twoFormHeatWeight_tendsto hRic) f

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Hodge operator as a densely defined operator on L2.
Its domain is the range of the shifted resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHodgeDomain (hRic : RicciThree g) : Submodule ℝ (TwoFormL2 o) :=
  (twoFormShiftedResolvent hRic).range

def twoFormHodgeDomainEquiv (hRic : RicciThree g) :
    TwoFormL2 o ≃ₗ[ℝ] twoFormHodgeDomain (o := o) hRic :=
  LinearEquiv.ofInjective (twoFormShiftedResolvent hRic).toLinearMap
    (twoFormShiftedResolvent_injective hRic)

def twoFormHodgeGenerator (hRic : RicciThree g) :
    twoFormHodgeDomain (o := o) hRic →ₗ[ℝ] TwoFormL2 o :=
  (twoFormHodgeDomainEquiv hRic).symm.toLinearMap - (twoFormHodgeDomain hRic).subtype

theorem twoFormHodgeDomain_dense (hRic : RicciThree g) :
    (twoFormHodgeDomain (o := o) hRic).topologicalClosure = ⊤ := by
  have hle : (⨆ μ : TwoFormSpectralValue (o := o) hRic, TwoFormSpectralSpace hRic μ) ≤
      twoFormHodgeDomain hRic := by
    apply iSup_le
    intro μ f hf
    refine ⟨μ.val⁻¹ • f, ?_⟩
    change twoFormShiftedResolvent hRic (μ.val⁻¹ • f) = f
    rw [map_smul]
    have he := Module.End.mem_eigenspace_iff.mp hf
    change twoFormShiftedResolvent hRic f = μ.val • f at he
    rw [he, smul_smul, inv_mul_cancel₀ (ne_of_gt (twoFormSpectralValue_bounds hRic μ).1), one_smul]
  apply top_unique
  rw [← twoFormSpectral_total hRic]
  exact Submodule.topologicalClosure_mono hle

theorem twoFormHodgeDomain_weak (hRic : RicciThree g)
    (f : twoFormHodgeDomain (o := o) hRic) :
    ∃ u : TwoFormH1 o, twoFormH1ToL2 u = f.val ∧
      ∀ v, twoFormHodgeForm u v = inner ℝ (twoFormHodgeGenerator hRic f) (twoFormH1ToL2 v) := by
  let h := (twoFormHodgeDomainEquiv hRic).symm f
  have hf : twoFormShiftedResolvent hRic h = f.val :=
    congrArg Subtype.val ((twoFormHodgeDomainEquiv hRic).apply_symm_apply f)
  refine ⟨twoFormShiftedSolution hRic h, hf, fun v => ?_⟩
  have he := twoFormShiftedSolution_weak hRic h v
  change twoFormHodgeForm (twoFormShiftedSolution hRic h) v +
    inner ℝ (twoFormShiftedResolvent hRic h) (twoFormH1ToL2 v) = _ at he
  rw [hf] at he
  change _ = inner ℝ (h - f.val) (twoFormH1ToL2 v)
  rw [inner_sub_left]
  linarith only [he]

theorem twoFormHodgeDomain_of_weak (hRic : RicciThree g) (u : TwoFormH1 o) (h : TwoFormL2 o)
    (hu : ∀ v, twoFormHodgeForm u v = inner ℝ h (twoFormH1ToL2 v)) :
    twoFormH1ToL2 u ∈ twoFormHodgeDomain hRic := by
  refine ⟨h + twoFormH1ToL2 u, ?_⟩
  have he : u = twoFormShiftedSolution hRic (h + twoFormH1ToL2 u) := by
    apply twoFormShiftedSolution_unique hRic
    intro v
    rw [hu v, inner_add_left]
  change twoFormH1ToL2 (twoFormShiftedSolution hRic (h + twoFormH1ToL2 u)) = _
  exact congrArg twoFormH1ToL2 he.symm

theorem twoFormHeat_mem_hodgeDomain (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) : twoFormHeat hRic t f ∈ twoFormHodgeDomain hRic :=
  ⟨twoFormHeatLiftSource hRic t ht f, twoFormHeatLiftSource_resolvent hRic t ht f⟩

theorem twoFormHodgeGenerator_nonneg (hRic : RicciThree g)
    (f : twoFormHodgeDomain (o := o) hRic) :
    0 ≤ inner ℝ (twoFormHodgeGenerator hRic f) f.val := by
  obtain ⟨u, hu, he⟩ := twoFormHodgeDomain_weak hRic f
  have h := twoFormHodgeForm_nonneg hRic u
  rwa [he u, hu] at h

theorem twoFormHodgeGenerator_symmetric (hRic : RicciThree g)
    (f h : twoFormHodgeDomain (o := o) hRic) :
    inner ℝ (twoFormHodgeGenerator hRic f) h.val =
      inner ℝ f.val (twoFormHodgeGenerator hRic h) := by
  obtain ⟨u, hu, he⟩ := twoFormHodgeDomain_weak hRic f
  obtain ⟨v, hv, hk⟩ := twoFormHodgeDomain_weak hRic h
  calc
    _ = twoFormHodgeForm u v := by rw [he v, hv]
    _ = twoFormHodgeForm v u := twoFormHodgeForm_comm u v
    _ = inner ℝ (twoFormHodgeGenerator hRic h) f.val := by rw [hk u, hu]
    _ = _ := real_inner_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the smooth geometric Hodge Laplacian, proved using its
nondegenerate integral pairing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeLaplacian_add (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothHodgeLaplacian hRic (u + v) =
      smoothHodgeLaplacian hRic u + smoothHodgeLaplacian hRic v := by
  apply smoothTwoForm_eq_of_pairings
  intro w
  have he : smoothTwoFormToH1 ((u + v : smoothTwoForms o) : SmoothH1TwoForm o) =
      smoothTwoFormToH1 (u : SmoothH1TwoForm o) +
        smoothTwoFormToH1 (v : SmoothH1TwoForm o) :=
    map_add smoothTwoFormToH1 (u : SmoothH1TwoForm o) (v : SmoothH1TwoForm o)
  rw [smoothTwoFormL2Inner_add, smoothHodgeLaplacian_pairing,
    smoothHodgeLaplacian_pairing, smoothHodgeLaplacian_pairing]
  exact (congrArg (fun t : TwoFormH1 o =>
    twoFormHodgeForm t (smoothTwoFormToH1 (w : SmoothH1TwoForm o))) he).trans
      (twoFormHodgeForm_add_left _ _ _)

theorem smoothHodgeLaplacian_smul (hRic : RicciThree g) (r : ℝ) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic (r • u) = r • smoothHodgeLaplacian hRic u := by
  apply smoothTwoForm_eq_of_pairings
  intro w
  have he : smoothTwoFormToH1 ((r • u : smoothTwoForms o) : SmoothH1TwoForm o) =
      r • smoothTwoFormToH1 (u : SmoothH1TwoForm o) :=
    map_smul smoothTwoFormToH1 r (u : SmoothH1TwoForm o)
  rw [smoothTwoFormL2Inner_smul, smoothHodgeLaplacian_pairing,
    smoothHodgeLaplacian_pairing]
  exact (congrArg (fun t : TwoFormH1 o =>
    twoFormHodgeForm t (smoothTwoFormToH1 (w : SmoothH1TwoForm o))) he).trans
      (twoFormHodgeForm_smul_left _ _ _)

def smoothHodgeLaplacianLinear (hRic : RicciThree g) :
    smoothTwoForms o →ₗ[ℝ] smoothTwoForms o where
  toFun := smoothHodgeLaplacian hRic
  map_add' := smoothHodgeLaplacian_add hRic
  map_smul' := smoothHodgeLaplacian_smul hRic

theorem smoothHodgeLaplacian_ker (hRic : RicciThree g) :
    (smoothHodgeLaplacianLinear (o := o) hRic).ker = smoothHarmonicTwoForms := by
  ext u
  exact smoothHodgeLaplacian_eq_zero_iff hRic u

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every eigenvector of the actual compact Hodge resolvent has a smooth
representative satisfying the geometric Hodge eigenvalue equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_weakEigen_rough (u : TwoFormH1 o) (κ : ℝ)
    (hu : ∀ v, twoFormHodgeForm u v = κ * inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 v)) :
    u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
      κ • twoFormH1ToL2 u) := by
  apply twoFormRoughSolution_unique
  intro v
  have he := hu v
  unfold twoFormHodgeForm at he
  rw [inner_add_left, real_inner_smul_left]
  linarith only [he]

theorem twoForm_weakEigen_smooth (hRic : RicciThree g) (u : TwoFormH1 o) (κ : ℝ)
    (hu : ∀ v, twoFormHodgeForm u v = κ * inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 v)) :
    ∃ w : smoothTwoForms o, u = smoothTwoFormToH1 (w : SmoothH1TwoForm o) ∧
      smoothHodgeLaplacian hRic w = κ • w := by
  obtain ⟨w, hw⟩ := twoFormEigen_smooth_representative u κ (twoForm_weakEigen_rough u κ hu)
  have he : u = smoothTwoFormToH1 (w : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hw.trans (twoFormH1ToL2_smooth _).symm)
  refine ⟨w, he, smoothTwoForm_eq_of_pairings _ _ ?_⟩
  intro v
  have hQ := hu (smoothTwoFormToH1 (v : SmoothH1TwoForm o))
  rw [he] at hQ
  have hpair : inner ℝ (twoFormH1ToL2 (smoothTwoFormToH1 (w : SmoothH1TwoForm o)))
      (twoFormH1ToL2 (smoothTwoFormToH1 (v : SmoothH1TwoForm o))) =
      smoothTwoFormL2Inner w v := by
    exact (congrArg₂ (fun a b : TwoFormL2 o => inner ℝ a b)
      (twoFormH1ToL2_smooth (w : SmoothH1TwoForm o))
      (twoFormH1ToL2_smooth (v : SmoothH1TwoForm o))).trans
        (smoothTwoFormToL2.inner_map_map _ _)
  calc
    _ = twoFormHodgeForm (smoothTwoFormToH1 (w : SmoothH1TwoForm o))
        (smoothTwoFormToH1 (v : SmoothH1TwoForm o)) := smoothHodgeLaplacian_pairing hRic w v
    _ = κ * smoothTwoFormL2Inner w v := hQ.trans (congrArg (κ * ·) hpair)
    _ = _ := (smoothTwoFormL2Inner_smul κ w v).symm

theorem twoFormResolvent_eigenvector_smooth (hRic : RicciThree g) {μ : ℝ} {f : TwoFormL2 o}
    (hf : Module.End.HasEigenvector (twoFormShiftedResolvent hRic).toLinearMap μ f) :
    ∃ w : smoothTwoForms o, f = smoothTwoFormToL2 (w : SmoothL2TwoForm o) ∧
      smoothHodgeLaplacian hRic w = (μ⁻¹ - 1) • w := by
  obtain ⟨u, hu, he⟩ := twoFormResolvent_eigenvector_weak hRic hf
  obtain ⟨w, hw, hL⟩ := twoForm_weakEigen_smooth hRic u (μ⁻¹ - 1) (fun v => by
    rw [he v, hu])
  exact ⟨w, hu.symm.trans ((congrArg twoFormH1ToL2 hw).trans (twoFormH1ToL2_smooth _)), hL⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The densely defined L2 generator agrees with the actual smooth
Hodge Laplacian, not merely with a formal spectral expression. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeLaplacian_weak (hRic : RicciThree g) (u : smoothTwoForms o)
    (v : TwoFormH1 o) :
    twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) v =
      inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 v) := by
  have hc : Continuous (fun w : TwoFormH1 o =>
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) w) :=
    (continuous_const.inner continuous_id).sub
      (continuous_const.inner twoFormH1ToL2.continuous)
  have hd : Continuous (fun w : TwoFormH1 o =>
      inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 w)) := continuous_const.inner twoFormH1ToL2.continuous
  have he : (fun w : TwoFormH1 o =>
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) w) =
      (fun w => inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 w)) := by
    apply (smoothTwoFormToH1_dense (o := o)).equalizer hc hd
    funext w
    change twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o))
      (smoothTwoFormToH1 w) =
      inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 (smoothTwoFormToH1 w))
    calc
      _ = smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) w :=
        (smoothHodgeLaplacian_pairing hRic u w).symm
      _ = inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) :=
        (smoothTwoFormToL2.inner_map_map
          (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o) (w : SmoothL2TwoForm o)).symm
      _ = _ := congrArg (fun z => inner ℝ
        (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o)) z)
          (twoFormH1ToL2_smooth w).symm
  exact congrFun he v

theorem smoothTwoForm_mem_hodgeDomain (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormToL2 (u : SmoothL2TwoForm o) ∈ twoFormHodgeDomain hRic := by
  have h := twoFormHodgeDomain_of_weak hRic _ _ (smoothHodgeLaplacian_weak hRic u)
  have hv : twoFormH1ToL2 (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) =
      smoothTwoFormToL2 (u : SmoothL2TwoForm o) := twoFormH1ToL2_smooth _
  exact hv ▸ h

theorem twoFormHodgeGenerator_smooth (hRic : RicciThree g) (u : smoothTwoForms o) :
    twoFormHodgeGenerator hRic
      ⟨smoothTwoFormToL2 (u : SmoothL2TwoForm o), smoothTwoForm_mem_hodgeDomain hRic u⟩ =
        smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o) := by
  let f : twoFormHodgeDomain (o := o) hRic :=
    ⟨smoothTwoFormToL2 (u : SmoothL2TwoForm o), smoothTwoForm_mem_hodgeDomain hRic u⟩
  obtain ⟨v, hv, he⟩ := twoFormHodgeDomain_weak hRic f
  have hv' : v = smoothTwoFormToH1 (u : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hv.trans (twoFormH1ToL2_smooth _).symm)
  have hpair (w : TwoFormH1 o) : inner ℝ (twoFormHodgeGenerator hRic f) (twoFormH1ToL2 w) =
      inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 w) := by
    rw [← he w, hv']
    exact smoothHodgeLaplacian_weak hRic u w
  have hall := twoFormH1ToL2_dense.equalizer
    (continuous_const.inner continuous_id) (continuous_const.inner continuous_id) (funext hpair)
  exact ext_inner_right ℝ (congrFun hall)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthogonal harmonic projection and smooth Poisson decomposition of
actual two-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothHarmonicL2 : Submodule ℝ (SmoothL2TwoForm o) where
  carrier := {u | (u : smoothTwoForms o) ∈ smoothHarmonicTwoForms}
  zero_mem' := (smoothHarmonicTwoForms (o := o)).zero_mem
  add_mem' hu hv := (smoothHarmonicTwoForms (o := o)).add_mem hu hv
  smul_mem' r _ hu := (smoothHarmonicTwoForms (o := o)).smul_mem r hu

def smoothHarmonicL2ToHarmonic :
    smoothHarmonicL2 (o := o) →ₗ[ℝ] smoothHarmonicTwoForms (o := o) where
  toFun u := ⟨u.val, u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothHarmonicL2ToHarmonic_injective :
    Function.Injective (smoothHarmonicL2ToHarmonic (o := o)) := by
  intro u v h
  exact Subtype.ext (congrArg Subtype.val h)

theorem smoothHarmonicL2_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (smoothHarmonicL2 (o := o)) := by
  let _ : AddCommGroup (smoothHarmonicTwoForms (o := o)) := Submodule.addCommGroup _
  let _ : FiniteDimensional ℝ (smoothHarmonicTwoForms (o := o)) :=
    smoothHarmonicTwoForms_finite (o := o) hRic
  exact FiniteDimensional.of_injective (smoothHarmonicL2ToHarmonic (o := o))
    (smoothHarmonicL2ToHarmonic_injective (o := o))

theorem exists_smoothHarmonic_projection (hRic : RicciThree g) (f : smoothTwoForms o) :
    ∃ h : smoothTwoForms o, h ∈ smoothHarmonicTwoForms ∧
      ∀ v ∈ smoothHarmonicTwoForms (o := o), smoothTwoFormL2Inner (f - h) v = 0 := by
  let _ := smoothHarmonicL2_finite (o := o) hRic
  let p := (smoothHarmonicL2 (o := o)).orthogonalProjectionOnto (f : SmoothL2TwoForm o)
  refine ⟨p.val, p.property, ?_⟩
  intro v hv
  exact (smoothHarmonicL2 (o := o)).starProjection_inner_eq_zero
    (f : SmoothL2TwoForm o) (v : SmoothL2TwoForm o) hv

theorem exists_smoothHodge_decomposition (hRic : RicciThree g) (f : smoothTwoForms o) :
    ∃ h : smoothTwoForms o, h ∈ smoothHarmonicTwoForms ∧
      ∃ u : smoothTwoForms o, f = h + smoothHodgeLaplacian hRic u := by
  obtain ⟨h, hh, hperp⟩ := exists_smoothHarmonic_projection hRic f
  obtain ⟨u, hu⟩ := exists_smoothHodgePoisson_pointwise hRic (f - h) hperp
  refine ⟨h, hh, u, ?_⟩
  rw [hu]
  abel

end
end PositiveEinsteinFour.Geometry
end


section

/-! A complete orthonormal basis of actual smooth Hodge eigenforms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev TwoFormEigenIndex (hRic : RicciThree g) :=
  Σ μ : TwoFormSpectralValue (o := o) hRic, Fin (Module.finrank ℝ (TwoFormSpectralSpace hRic μ))

def twoFormEigenvector (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) : TwoFormL2 o :=
  (stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic i.1) i.2).val

theorem twoFormEigenvector_orthonormal (hRic : RicciThree g) :
    Orthonormal ℝ (twoFormEigenvector (o := o) hRic) :=
  (twoFormShiftedResolvent_symmetric hRic).orthogonalFamily_eigenspaces'.orthonormal_sigma_orthonormal
    (fun μ => (stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic μ)).orthonormal)

theorem twoFormEigenvector_span (hRic : RicciThree g) :
    Submodule.span ℝ (Set.range (twoFormEigenvector (o := o) hRic)) =
      ⨆ μ : TwoFormSpectralValue (o := o) hRic, TwoFormSpectralSpace hRic μ := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (le_iSup (fun μ => TwoFormSpectralSpace hRic μ) i.1)
      (stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic i.1) i.2).property
  · apply iSup_le
    intro μ x hx
    let b := stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic μ)
    have he := congrArg (TwoFormSpectralSpace hRic μ).subtype
      (b.sum_repr (⟨x, hx⟩ : TwoFormSpectralSpace hRic μ))
    simp only [map_sum, map_smul] at he
    change (∑ j, (b.repr ⟨x, hx⟩) j • (b j : TwoFormL2 o)) = x at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨μ, j⟩, rfl⟩

def twoFormEigenbasis (hRic : RicciThree g) :
    HilbertBasis (TwoFormEigenIndex (o := o) hRic) ℝ (TwoFormL2 o) :=
  HilbertBasis.mk (twoFormEigenvector_orthonormal hRic) (by
    rw [twoFormEigenvector_span, twoFormSpectral_total hRic])

theorem twoFormEigenvector_hasEigenvector (hRic : RicciThree g)
    (i : TwoFormEigenIndex (o := o) hRic) :
    Module.End.HasEigenvector (twoFormShiftedResolvent hRic).toLinearMap i.1.val
      (twoFormEigenvector hRic i) := by
  refine ⟨(stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic i.1) i.2).property, ?_⟩
  have hn := (twoFormEigenvector_orthonormal hRic).1 i
  intro h
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem twoFormEigenvector_smooth (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    ∃ w : smoothTwoForms o, twoFormEigenvector hRic i = smoothTwoFormToL2 (w : SmoothL2TwoForm o) ∧
      smoothHodgeLaplacian hRic w = (i.1.val⁻¹ - 1) • w :=
  twoFormResolvent_eigenvector_smooth hRic (twoFormEigenvector_hasEigenvector hRic i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The geometric Hodge Laplacian splits as dδ + *dδ*. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormCodiffPairing_add_right (u v w : smoothTwoForms o) :
    twoFormCodiffPairing u (v + w) = twoFormCodiffPairing u v + twoFormCodiffPairing u w := by
  rw [twoFormCodiffPairing_comm, twoFormCodiffPairing_add_left,
    twoFormCodiffPairing_comm v u, twoFormCodiffPairing_comm w u]

theorem smoothTwoFormL2Inner_add_right (u v w : smoothTwoForms o) :
    smoothTwoFormL2Inner u (v + w) = smoothTwoFormL2Inner u v + smoothTwoFormL2Inner u w := by
  rw [smoothTwoFormL2Inner_comm, smoothTwoFormL2Inner_add,
    smoothTwoFormL2Inner_comm v u, smoothTwoFormL2Inner_comm w u]

theorem smoothTwoFormL2Inner_hodge_left (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothTwoFormHodge o u) v =
      smoothTwoFormL2Inner u (smoothTwoFormHodge o v) := by
  have h := (smoothL2Hodge (o := o)).inner_map_map
    (u : SmoothL2TwoForm o) (smoothL2Hodge (v : SmoothL2TwoForm o))
  change smoothTwoFormL2Inner (smoothTwoFormHodge o u)
    (smoothTwoFormHodge o (smoothTwoFormHodge o v)) =
      smoothTwoFormL2Inner u (smoothTwoFormHodge o v) at h
  rw [smoothTwoFormHodge_involutive o v] at h
  exact h

theorem smoothHodgeLaplacian_codiff_self (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) u =
      twoFormCodiffPairing u u +
        twoFormCodiffPairing (smoothTwoFormHodge o u) (smoothTwoFormHodge o u) :=
  (smoothHodgeLaplacian_pairing hRic u u).trans
    ((twoFormHodgeForm_smooth hRic (u : SmoothH1TwoForm o)).trans
      (smoothTwoFormDeRhamEnergy_codiff u))

theorem smoothHodgeLaplacian_codiff_pairing (hRic : RicciThree g)
    (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) v =
      twoFormCodiffPairing u v +
        twoFormCodiffPairing (smoothTwoFormHodge o u) (smoothTwoFormHodge o v) := by
  have h := smoothHodgeLaplacian_codiff_self hRic (u + v)
  have hu := smoothHodgeLaplacian_codiff_self hRic u
  have hv := smoothHodgeLaplacian_codiff_self hRic v
  simp only [smoothHodgeLaplacian_add, smoothTwoFormL2Inner_add,
    smoothTwoFormL2Inner_add_right, map_add, twoFormCodiffPairing_add_left,
    twoFormCodiffPairing_add_right] at h
  have hs : smoothTwoFormL2Inner (smoothHodgeLaplacian hRic v) u =
      smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) v :=
    (smoothHodgeLaplacian_selfAdjoint hRic v u).trans (smoothTwoFormL2Inner_comm _ _)
  rw [hs, twoFormCodiffPairing_comm v u,
    twoFormCodiffPairing_comm (smoothTwoFormHodge o v) (smoothTwoFormHodge o u)] at h
  linarith only [h, hu, hv]

theorem smoothHodgeLaplacian_dDelta_hodge (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic u = smoothTwoFormDDelta u +
      smoothTwoFormHodge o (smoothTwoFormDDelta (smoothTwoFormHodge o u)) := by
  apply smoothTwoForm_eq_of_pairings
  intro v
  rw [smoothTwoFormL2Inner_add, smoothTwoFormL2Inner_hodge_left,
    smoothTwoFormDDelta_pairing hRic, smoothTwoFormDDelta_pairing hRic,
    smoothHodgeLaplacian_codiff_pairing hRic]

theorem exists_smoothHodge_exact_coexact (hRic : RicciThree g) (f : smoothTwoForms o) :
    ∃ h : smoothTwoForms o, h ∈ smoothHarmonicTwoForms ∧
      ∃ a b : smoothCovariantFields (M := M) 1,
        f = h + smoothOneFormExterior a + smoothTwoFormHodge o (smoothOneFormExterior b) := by
  obtain ⟨h, hh, u, hu⟩ := exists_smoothHodge_decomposition hRic f
  refine ⟨h, hh, smoothTwoFormCodifferentialField u,
    smoothTwoFormCodifferentialField (smoothTwoFormHodge o u), ?_⟩
  rw [smoothHodgeLaplacian_dDelta_hodge hRic] at hu
  exact hu.trans (by abel)

end
end PositiveEinsteinFour.Geometry
end


section

/-! An L2 distributional Hodge equation against actual smooth sections
lies in the domain of the Hodge generator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodge_resolvent_of_distribution (hRic : RicciThree g)
    (f h : TwoFormL2 o)
    (hweak : ∀ v : smoothTwoForms o,
      inner ℝ f (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)) =
        inner ℝ h (smoothTwoFormToL2 (v : SmoothL2TwoForm o))) :
    twoFormShiftedResolvent hRic (f + h) = f := by
  apply (twoFormEigenbasis hRic).repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  simp only [twoFormEigenbasis, HilbertBasis.coe_mk]
  obtain ⟨v, hv, hLv⟩ := twoFormEigenvector_smooth hRic i
  have hL : smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o) =
      (i.1.val⁻¹ - 1) • twoFormEigenvector hRic i := by
    have he : (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o) =
        (i.1.val⁻¹ - 1) • (v : SmoothL2TwoForm o) := hLv
    calc
      _ = smoothTwoFormToL2 ((i.1.val⁻¹ - 1) • (v : SmoothL2TwoForm o)) :=
        congrArg smoothTwoFormToL2 he
      _ = (i.1.val⁻¹ - 1) • smoothTwoFormToL2 (v : SmoothL2TwoForm o) :=
        smoothTwoFormToL2.map_smul _ _
      _ = _ := congrArg ((i.1.val⁻¹ - 1) • ·) hv.symm
  have hpair := hweak v
  rw [hL, ← hv, real_inner_smul_right] at hpair
  have hEig := Module.End.mem_eigenspace_iff.mp (twoFormEigenvector_hasEigenvector hRic i).1
  change twoFormShiftedResolvent hRic (twoFormEigenvector hRic i) =
    i.1.val • twoFormEigenvector hRic i at hEig
  calc
    _ = inner ℝ (twoFormShiftedResolvent hRic (f + h)) (twoFormEigenvector hRic i) :=
      real_inner_comm _ _
    _ = inner ℝ (f + h) (twoFormShiftedResolvent hRic (twoFormEigenvector hRic i)) :=
      twoFormShiftedResolvent_symmetric hRic _ _
    _ = i.1.val * (inner ℝ f (twoFormEigenvector hRic i) +
        inner ℝ h (twoFormEigenvector hRic i)) := by
      rw [hEig, real_inner_smul_right, inner_add_left]
    _ = inner ℝ f (twoFormEigenvector hRic i) := by
      rw [← hpair]
      have hne := (twoFormSpectralValue_bounds hRic i.1).1.ne'
      field_simp
      ring
    _ = _ := real_inner_comm _ _

theorem twoFormHodgeDomain_of_distribution (hRic : RicciThree g)
    (f h : TwoFormL2 o)
    (hweak : ∀ v : smoothTwoForms o,
      inner ℝ f (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)) =
        inner ℝ h (smoothTwoFormToL2 (v : SmoothL2TwoForm o))) :
    ∃ hf : f ∈ twoFormHodgeDomain hRic, twoFormHodgeGenerator hRic ⟨f, hf⟩ = h := by
  have he := twoFormHodge_resolvent_of_distribution hRic f h hweak
  have hf : f ∈ twoFormHodgeDomain hRic := ⟨f + h, he⟩
  refine ⟨hf, ?_⟩
  have hi : (twoFormHodgeDomainEquiv hRic).symm ⟨f, hf⟩ = f + h := by
    apply (twoFormHodgeDomainEquiv hRic).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext he.symm
  change (twoFormHodgeDomainEquiv hRic).symm ⟨f, hf⟩ - f = h
  rw [hi]
  abel

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite spectral heat kernels and their actual diagonal trace integrals.
The normalization is the same probability-volume L2 pairing used throughout. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormEigenSection (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    smoothTwoForms o := (twoFormEigenvector_smooth hRic i).choose

theorem twoFormEigenSection_L2 (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    smoothTwoFormToL2 (twoFormEigenSection hRic i : SmoothL2TwoForm o) =
      twoFormEigenvector hRic i :=
  (twoFormEigenvector_smooth hRic i).choose_spec.1.symm

theorem twoFormEigenSection_equation (hRic : RicciThree g)
    (i : TwoFormEigenIndex (o := o) hRic) :
    smoothHodgeLaplacian hRic (twoFormEigenSection hRic i) =
      (i.1.val⁻¹ - 1) • twoFormEigenSection hRic i :=
  (twoFormEigenvector_smooth hRic i).choose_spec.2

theorem twoFormEigenSection_integral_norm (hRic : RicciThree g)
    (i : TwoFormEigenIndex (o := o) hRic) :
    (∫ x, ‖(twoFormEigenSection hRic i).val x‖ ^ 2 ∂normalizedVolume g) = 1 := by
  calc
    _ = ‖smoothTwoFormToL2 (twoFormEigenSection hRic i : SmoothL2TwoForm o)‖ ^ 2 :=
      (smoothTwoFormToL2_norm_sq (twoFormEigenSection hRic i : SmoothL2TwoForm o)).symm
    _ = 1 := by rw [twoFormEigenSection_L2,
      (twoFormEigenvector_orthonormal hRic).1 i, one_pow]

def twoFormFiniteHeatKernel (hRic : RicciThree g) (t : ℝ≥0)
    (s : Finset (TwoFormEigenIndex (o := o) hRic)) (x y : M) :
    TwoFormFour →ₗ[ℝ] TwoFormFour :=
  ∑ i ∈ s, twoFormHeatWeight hRic t i.1 •
    (InnerProductSpace.rankOne ℝ ((twoFormEigenSection hRic i).val x)
      ((twoFormEigenSection hRic i).val y)).toLinearMap

theorem twoFormFiniteHeatKernel_diagonal (hRic : RicciThree g) (t : ℝ≥0)
    (s : Finset (TwoFormEigenIndex (o := o) hRic)) (x : M) :
    LinearMap.trace ℝ TwoFormFour (twoFormFiniteHeatKernel hRic t s x x) =
      ∑ i ∈ s, twoFormHeatWeight hRic t i.1 * ‖(twoFormEigenSection hRic i).val x‖ ^ 2 := by
  classical
  rw [twoFormFiniteHeatKernel, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, InnerProductSpace.trace_rankOne, real_inner_self_eq_norm_sq]
  rfl

theorem twoFormFiniteHeatKernel_trace_integral (hRic : RicciThree g) (t : ℝ≥0)
    (s : Finset (TwoFormEigenIndex (o := o) hRic)) :
    (∫ x, LinearMap.trace ℝ TwoFormFour (twoFormFiniteHeatKernel hRic t s x x)
      ∂normalizedVolume g) = ∑ i ∈ s, twoFormHeatWeight hRic t i.1 := by
  classical
  have := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  simp only [twoFormFiniteHeatKernel_diagonal]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, twoFormEigenSection_integral_norm, mul_one]
  · intro i _
    have hc := (smoothTwoForm_norm_continuous (twoFormEigenSection hRic i)).pow 2
    exact (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth Hodge eigenforms are total in the two-form H1 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormEigenform (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    smoothTwoForms o := (twoFormEigenvector_smooth hRic i).choose

theorem twoFormEigenform_L2 (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormEigenvector hRic i = smoothTwoFormToL2 (twoFormEigenform hRic i : SmoothL2TwoForm o) :=
  (twoFormEigenvector_smooth hRic i).choose_spec.1

theorem twoFormEigenform_laplacian (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    smoothHodgeLaplacian hRic (twoFormEigenform hRic i) =
      (i.1.val⁻¹ - 1) • twoFormEigenform hRic i :=
  (twoFormEigenvector_smooth hRic i).choose_spec.2

theorem twoFormShiftedSolution_dense (hRic : RicciThree g) :
    DenseRange (twoFormShiftedSolution (o := o) hRic) := by
  have hr : DenseRange (twoFormRoughSolution (o := o)) :=
    adjoint_denseRange_of_injective _ (twoFormH1ToL2_injective hRic)
  exact (twoFormShiftedHodgeEquiv hRic).symm.surjective.denseRange.comp hr
    (twoFormShiftedHodgeEquiv hRic).symm.continuous

theorem twoFormShiftedSolution_eigen_smooth (hRic : RicciThree g)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormShiftedSolution hRic (twoFormEigenvector hRic i) =
      i.1.val • smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o) := by
  apply twoFormH1ToL2_injective hRic
  have hJ := twoFormH1ToL2_smooth (twoFormEigenform hRic i : SmoothH1TwoForm o)
  calc
    _ = i.1.val • twoFormEigenvector hRic i :=
      Module.End.mem_eigenspace_iff.mp (twoFormEigenvector_hasEigenvector hRic i).1
    _ = i.1.val • twoFormH1ToL2
        (smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o)) :=
      congrArg (i.1.val • ·) ((twoFormEigenform_L2 hRic i).trans hJ.symm)
    _ = _ := (twoFormH1ToL2.map_smul i.1.val
      (smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o))).symm

theorem twoFormH1_eigenforms_total (hRic : RicciThree g) :
    (Submodule.span ℝ (range (fun i : TwoFormEigenIndex (o := o) hRic =>
      smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o)))).topologicalClosure = ⊤ := by
  have he := dense_span_continuousLinearMap_image (twoFormEigenvector (o := o) hRic)
    (by rw [twoFormEigenvector_span, twoFormSpectral_total hRic])
    (twoFormShiftedSolution hRic) (twoFormShiftedSolution_dense hRic)
  have hs : Submodule.span ℝ (range (fun i =>
      twoFormShiftedSolution hRic (twoFormEigenvector hRic i))) ≤
      Submodule.span ℝ (range (fun i : TwoFormEigenIndex (o := o) hRic =>
        smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change twoFormShiftedSolution hRic (twoFormEigenvector hRic i) ∈ _
    rw [twoFormShiftedSolution_eigen_smooth]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  apply top_unique
  rw [← he]
  exact Submodule.topologicalClosure_mono hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local heat operators have compact support and square-summable
images of the orthonormal eigenbasis. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap NNReal BoundedContinuousFunction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
  (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
  {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
  (hs : tsupport a ⊆ V) (r : Fin 6)

theorem twoFormHeatChartContinuous_smooth (input : TwoFormL2 o) (w : smoothTwoForms o)
    (hw : twoFormH1ToL2 (twoFormHeatLift hRic t ht input) = smoothTwoFormToL2 (w : SmoothL2TwoForm o))
    (z : FourSpace) :
    twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input z =
      (a z * twoFormChartValue o w.val c S hS z r : ℂ) := by
  have hu : twoFormHeatLift hRic t ht input = smoothTwoFormToH1 (w : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hw.trans (twoFormH1ToL2_smooth _).symm)
  let q := twoFormGramCutoffC1 c S hKt a ha hc (hs.trans hVK) (twoFormComponentIndex r)
    (w : SmoothH1TwoForm o)
  have hA : (twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r input : FourSpace → ℂ) =ᵐ[volume]
      fun x => (q.val x : ℂ) := by
    have heq : twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r input =
        scalarComplexL2 (ScalarEuclideanSobolev.valueL2 q) :=
      congrArg scalarComplexL2 ((congrArg (twoFormGramValueL2 c S hK hKt a ha hc
        (hs.trans hVK) (twoFormComponentIndex r)) hu).trans
          (twoFormGramValueL2_smooth c S hK hKt a ha hc (hs.trans hVK)
            (twoFormComponentIndex r) (w : SmoothH1TwoForm o)))
    rw [heq]
    filter_upwards [scalarComplexL2_coe (ScalarEuclideanSobolev.valueL2 q),
      ScalarEuclideanSobolev.valueL2_coe q] with x hC hq
    exact hC.trans (congrArg Complex.ofReal hq)
  have he : (twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input :
      FourSpace → ℂ) = fun x => (q.val x : ℂ) := by
    apply MeasureTheory.Measure.eq_of_ae_eq
      ((twoFormHeatChartContinuous_ae hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input).symm.trans hA)
    · exact (twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input).continuous
    · exact Complex.continuous_ofReal.comp q.property.1.continuous
  rw [congrFun he z]
  rw [← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  exact (twoFormGramCutoffC1_value c S hS hKt a ha hc (hs.trans hVK)
    (twoFormComponentIndex r) (w : SmoothH1TwoForm o) z).trans
      (congrArg (a z * ·) (twoFormTensor_component _ r))

theorem twoFormHeatChartContinuous_support (input : TwoFormL2 o) (z : FourSpace)
    (hz : z ∉ K) :
    twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input z = 0 := by
  obtain ⟨w, hw⟩ := twoFormHeat_smooth_representative hRic t ht input
  rw [twoFormHeatChartContinuous_smooth hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input w hw z]
  have ha0 : a z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hVK (hs h)))
  rw [ha0, Complex.ofReal_zero, zero_mul]

include hV hU hKU hp in

theorem twoFormHeatChart_square_summable :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic =>
      ‖twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r (twoFormEigenvector hRic i)‖ ^ 2) := by
  apply scalarLocalOperator_summable (twoFormEigenvector_orthonormal hRic)
    (twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r)
    (twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r)
    (twoFormHeatChartContinuous_ae hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r) hK
  exact twoFormHeatChartContinuous_support hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual heat multiplier on each smooth Hodge eigensection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_eigenvalue (hRic : RicciThree g) (t : ℝ≥0)
    (μ : TwoFormSpectralValue (o := o) hRic) (f : TwoFormL2 o)
    (hf : f ∈ TwoFormSpectralSpace hRic μ) :
    twoFormHeat hRic t f = twoFormHeatWeight hRic t μ • f := by
  have hf' := Module.End.mem_eigenspace_iff.mp hf
  apply (twoFormSpectralEquiv hRic).injective
  apply lp.ext
  funext ν
  rw [twoFormHeat_coordinate, map_smul]
  change twoFormHeatWeight hRic t ν • (twoFormSpectralEquiv hRic f) ν =
    twoFormHeatWeight hRic t μ • (twoFormSpectralEquiv hRic f) ν
  by_cases hν : ν = μ
  · rw [hν]
  · have hne : ν.val - μ.val ≠ 0 := sub_ne_zero.mpr (fun h => hν (Subtype.ext h))
    have he := congrArg (fun u : TwoFormL2 o => (twoFormSpectralEquiv hRic u) ν) hf'
    change (twoFormSpectralEquiv hRic (twoFormShiftedResolvent hRic f)) ν =
      (twoFormSpectralEquiv hRic (μ.val • f)) ν at he
    rw [twoFormShiftedResolvent_coordinate, map_smul] at he
    have hz : (ν.val - μ.val) • (twoFormSpectralEquiv hRic f) ν = 0 := by
      rw [sub_smul, he]
      exact sub_self _
    have hv := (smul_eq_zero.mp hz).resolve_left hne
    rw [hv, smul_zero, smul_zero]

theorem twoFormHeat_eigenvector (hRic : RicciThree g) (t : ℝ≥0)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormHeat hRic t (twoFormEigenvector hRic i) =
      twoFormHeatWeight hRic t i.1 • twoFormEigenvector hRic i :=
  twoFormHeat_eigenvalue hRic t i.1 _ (twoFormEigenvector_hasEigenvector hRic i).1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Closed two-forms are orthogonal to coexact forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_closed_codiff_hodge (u : smoothTwoForms o)
    (hu : smoothTwoFormExterior u = 0) :
    smoothTwoFormCodifferential (smoothTwoFormHodge o u) = 0 := by
  have hd (e : FrameBundle g) (i j k : Fin 4) : smoothTwoFormExterior u e i j k = 0 :=
    congrFun (congrFun (congrFun (congrFun hu e) i) j) k
  funext e k
  have h := twoFormDeRhamDensity_hodge u e.base
  rw [twoFormDeRhamDensity_eq_frame, twoFormCodiffDensity_eq_frame u e,
    twoFormCodiffDensity_eq_frame (smoothTwoFormHodge o u) e,
    twoFormCodiffTensor_squareNorm, twoFormCodiffTensor_squareNorm] at h
  change (1 / 6 : ℝ) * (∑ i, ∑ j, ∑ k, smoothTwoFormExterior u e i j k ^ 2) +
      (∑ k, smoothTwoFormCodifferential u e k ^ 2) =
      (∑ k, smoothTwoFormCodifferential u e k ^ 2) +
      (∑ k, smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k ^ 2) at h
  simp only [hd, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero,
    mul_zero, zero_add] at h
  have hs : (∑ k, smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k ^ 2) = 0 := by
    linarith only [h]
  have hk : smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k ^ 2 ≤
      ∑ j, smoothTwoFormCodifferential (smoothTwoFormHodge o u) e j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  rw [hs] at hk
  exact (sq_eq_zero_iff.mp (le_antisymm hk (sq_nonneg _)))

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothOneForm_coexact_orthogonal_closed (hRic : RicciThree g)
    (a : smoothCovariantFields (M := M) 1) (v : smoothTwoForms o)
    (hv : smoothTwoFormExterior v = 0) :
    smoothTwoFormL2Inner (smoothTwoFormHodge o (smoothOneFormExterior a)) v = 0 := by
  rw [smoothTwoFormL2Inner_hodge_left, smoothOneFormExterior_adjoint hRic]
  have hz := smoothTwoForm_closed_codiff_hodge v hv
  simp only [hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, integral_zero]

theorem exists_smoothHodge_closed_decomposition (hRic : RicciThree g)
    (f : smoothTwoForms o) (hf : smoothTwoFormExterior f = 0) :
    ∃ h : smoothTwoForms o, h ∈ smoothHarmonicTwoForms ∧
      ∃ a : smoothCovariantFields (M := M) 1, f = h + smoothOneFormExterior a := by
  obtain ⟨h, hh, a, b, he⟩ := exists_smoothHodge_exact_coexact hRic f
  let w := smoothTwoFormHodge o (smoothOneFormExterior b)
  have hhclosed : smoothTwoFormExterior h = 0 := hh.1
  have ha := smoothOneFormExterior_closed (o := o) hRic a
  have hF := smoothOneForm_coexact_orthogonal_closed hRic b f hf
  have hH := smoothOneForm_coexact_orthogonal_closed hRic b h hhclosed
  have hA := smoothOneForm_coexact_orthogonal_closed hRic b (smoothOneFormExterior a) ha
  change smoothTwoFormL2Inner w f = 0 at hF
  change smoothTwoFormL2Inner w h = 0 at hH
  change smoothTwoFormL2Inner w (smoothOneFormExterior a) = 0 at hA
  have hw : smoothTwoFormL2Inner w w = 0 := by
    rw [he, smoothTwoFormL2Inner_add_right, smoothTwoFormL2Inner_add_right,
      hH, hA, zero_add] at hF
    simpa only [zero_add] using hF
  have hwzero : w = 0 := by
    exact (@inner_self_eq_zero ℝ (SmoothL2TwoForm o) _ _ _ (w : SmoothL2TwoForm o)).mp hw
  refine ⟨h, hh, a, ?_⟩
  change f = h + smoothOneFormExterior a + w at he
  rwa [hwzero, add_zero] at he

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Bochner heat convolution, its eigenmode pairing and its
quadratic norm bound for a linearly vanishing residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatConvolution (hRic : RicciThree g) (R : ℝ → TwoFormL2 o) (t : ℝ) : TwoFormL2 o :=
  ∫ s in (0 : ℝ)..t, twoFormHeat hRic (t - s).toNNReal (R s)

theorem twoFormHeatConvolution_integrable (hRic : RicciThree g)
    (R : ℝ → TwoFormL2 o) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t)) :
    IntervalIntegrable (fun s => twoFormHeat hRic (t - s).toNNReal (R s)) volume 0 t := by
  have htime : Continuous (fun s : ℝ => (t - s).toNNReal) :=
    continuous_real_toNNReal.comp (continuous_const.sub continuous_id)
  exact ((twoFormHeat_joint_continuous hRic).comp_continuousOn
    (htime.continuousOn.prodMk hR)).intervalIntegrable_of_Icc ht

theorem twoFormHeatConvolution_norm_le (hRic : RicciThree g)
    (R : ℝ → TwoFormL2 o) (t : ℝ) (ht : 0 ≤ t) (B : ℝ)
    (hR : ∀ s ∈ Icc 0 t, ‖R s‖ ≤ B * s) :
    ‖twoFormHeatConvolution hRic R t‖ ≤ B * t ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ => B * s) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, B * s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht _ hi
      exact Filter.Eventually.of_forall fun s hs =>
        (twoFormHeat_contraction hRic (t - s).toNNReal (R s)).trans
          (hR s ⟨hs.1.le, hs.2⟩)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; ring

theorem twoFormHeatConvolution_eigen (hRic : RicciThree g)
    (R : ℝ → TwoFormL2 o) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t))
    (i : TwoFormEigenIndex (o := o) hRic) :
    inner ℝ (twoFormHeatConvolution hRic R t) (twoFormEigenvector hRic i) =
      ∫ s in (0 : ℝ)..t, Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) *
        inner ℝ (R s) (twoFormEigenvector hRic i) := by
  have hi := twoFormHeatConvolution_integrable hRic R t ht hR
  have hp := (innerSL ℝ (twoFormEigenvector hRic i)).intervalIntegral_comp_comm hi
  change (∫ s in (0 : ℝ)..t,
    inner ℝ (twoFormEigenvector hRic i) (twoFormHeat hRic (t - s).toNNReal (R s))) =
      inner ℝ (twoFormEigenvector hRic i) (twoFormHeatConvolution hRic R t) at hp
  rw [real_inner_comm, ← hp]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht] using hs
  change inner ℝ (twoFormEigenvector hRic i) (twoFormHeat hRic (t - s).toNNReal (R s)) =
    Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) * inner ℝ (R s) (twoFormEigenvector hRic i)
  rw [real_inner_comm, twoFormHeat_selfAdjoint, twoFormHeat_eigenvector, real_inner_smul_right]
  unfold twoFormHeatWeight twoFormHeatRate
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs'.2)]
  ring_nf

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual smooth sections representing positive-time heat output. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatSection (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o) :
    smoothTwoForms o := (twoFormHeat_smooth_representative hRic t ht f).choose

theorem twoFormHeatSection_H1 (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o) :
    twoFormH1ToL2 (twoFormHeatLift hRic t ht f) =
      smoothTwoFormToL2 (twoFormHeatSection hRic t ht f : SmoothL2TwoForm o) :=
  (twoFormHeat_smooth_representative hRic t ht f).choose_spec

theorem twoFormHeatSection_L2 (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o) :
    smoothTwoFormToL2 (twoFormHeatSection hRic t ht f : SmoothL2TwoForm o) =
      twoFormHeat hRic t f :=
  (twoFormHeatSection_H1 hRic t ht f).symm.trans (twoFormHeatLift_value hRic t ht f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual coclosed one-forms are codifferentials of smooth two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeLaplacian_eq_dDelta_of_closed (hRic : RicciThree g)
    (u : smoothTwoForms o) (hu : smoothTwoFormExterior (smoothHodgeLaplacian hRic u) = 0) :
    smoothHodgeLaplacian hRic u = smoothTwoFormDDelta u := by
  let b := smoothTwoFormCodifferentialField (smoothTwoFormHodge o u)
  let w := smoothTwoFormHodge o (smoothOneFormExterior b)
  have he : smoothHodgeLaplacian hRic u = smoothTwoFormDDelta u + w :=
    smoothHodgeLaplacian_dDelta_hodge hRic u
  have hf := smoothOneForm_coexact_orthogonal_closed hRic b _ hu
  have ha := smoothOneForm_coexact_orthogonal_closed hRic b (smoothTwoFormDDelta u)
    (smoothTwoFormDDelta_closed hRic u)
  change smoothTwoFormL2Inner w (smoothHodgeLaplacian hRic u) = 0 at hf
  change smoothTwoFormL2Inner w (smoothTwoFormDDelta u) = 0 at ha
  rw [he, smoothTwoFormL2Inner_add_right, ha, zero_add] at hf
  have hw : w = 0 := smoothTwoFormL2Inner_definite w hf
  rwa [hw, add_zero] at he

theorem exists_smoothCoexact_of_divergence_eq_zero (hRic : RicciThree g)
    (v : smoothCovariantFields M 1) (hv : smoothOneFormDivergence g v = 0) :
    ∃ u : smoothTwoForms o, v = smoothTwoFormCodifferentialField u := by
  obtain ⟨u, hu⟩ := exists_smoothHodgePoisson_pointwise hRic
    (smoothOneFormExterior (o := o) v)
    (fun h hh => smoothHarmonic_orthogonal_exact hRic v h hh)
  have hclosed : smoothTwoFormExterior (smoothHodgeLaplacian hRic u) = 0 := by
    rw [hu]
    exact smoothOneFormExterior_closed hRic v
  have hd : smoothOneFormExterior (smoothTwoFormCodifferentialField u) =
      smoothOneFormExterior (o := o) v :=
    (smoothHodgeLaplacian_eq_dDelta_of_closed hRic u hclosed).symm.trans hu
  let w := v - smoothTwoFormCodifferentialField u
  have hwd : smoothOneFormExterior (o := o) w = 0 := by
    change smoothOneFormExteriorLinear (v - smoothTwoFormCodifferentialField u) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hd.symm
  have hwdiv : smoothOneFormDivergence g w = 0 := by
    change smoothOneFormDivergence g (v - smoothTwoFormCodifferentialField u) = 0
    rw [map_sub, hv, smoothTwoFormCodifferential_divergence hRic, sub_self]
  have hwt (e : FrameBundle g) :
      (∑ i, covariantFieldFramed g (covariantFieldDerivative g w.val) e ![i,i]) = 0 := by
    rw [← oneFormDivergence_eq_frame]
    exact congrArg (fun f : SmoothScalar (M := M) => f.val e.base) hwdiv
  have hw : w = 0 := oneForm_harmonic_eq_zero hRic w hwd hwt
  exact ⟨u, sub_eq_zero.mp hw⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Closedness is exactly vanishing of the Hodge-dual codifferential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormCodifferentialField_eq_zero_iff (u : smoothTwoForms o) :
    smoothTwoFormCodifferentialField u = 0 ↔ smoothTwoFormCodifferential u = 0 := by
  constructor
  · intro hu
    funext e k
    rw [← smoothTwoFormCodifferentialField_component, hu]
    simp [covariantFieldFramed_eq, frameTensor]
  · intro hu
    apply Subtype.ext
    apply covariantField_eq_of_framed (g := g)
    intro e
    funext a
    have ha : a = ![a 0] := by ext i; fin_cases i; rfl
    rw [ha, smoothTwoFormCodifferentialField_component, hu]
    simp [covariantFieldFramed_eq, frameTensor]

theorem smoothTwoForm_closed_iff_codifferential_hodge (u : smoothTwoForms o) :
    smoothTwoFormExterior u = 0 ↔
      smoothTwoFormCodifferentialField (smoothTwoFormHodge o u) = 0 := by
  rw [smoothTwoFormCodifferentialField_eq_zero_iff]
  constructor
  · exact smoothTwoForm_closed_codiff_hodge u
  · intro hu
    have hz (e : FrameBundle g) (k : Fin 4) :
        smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k = 0 :=
      congrFun (congrFun hu e) k
    funext e i j k
    have h := twoFormDeRhamDensity_hodge u e.base
    rw [twoFormDeRhamDensity_eq_frame, twoFormCodiffDensity_eq_frame u e,
      twoFormCodiffDensity_eq_frame (smoothTwoFormHodge o u) e,
      twoFormCodiffTensor_squareNorm, twoFormCodiffTensor_squareNorm] at h
    change (1 / 6 : ℝ) * (∑ i, ∑ j, ∑ k, smoothTwoFormExterior u e i j k ^ 2) +
        (∑ k, smoothTwoFormCodifferential u e k ^ 2) =
        (∑ k, smoothTwoFormCodifferential u e k ^ 2) +
        (∑ k, smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k ^ 2) at h
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero, add_zero] at h
    have hs : (∑ i, ∑ j, ∑ k, smoothTwoFormExterior u e i j k ^ 2) = 0 := by
      linarith only [h]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a (_ : a ∈ Finset.univ) => show 0 ≤ ∑ b, ∑ c,
        smoothTwoFormExterior u e a b c ^ 2 by positivity)).mp hs i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b (_ : b ∈ Finset.univ) => show 0 ≤ ∑ c,
        smoothTwoFormExterior u e i b c ^ 2 by positivity)).mp hi j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun c (_ : c ∈ Finset.univ) => sq_nonneg (smoothTwoFormExterior u e i j c))).mp
      hj k (Finset.mem_univ k))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Degree-two de Rham cohomology of the actual smooth exterior complex,
and its harmonic representative theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev smoothClosedTwoForms : Submodule ℝ (smoothTwoForms o) :=
  (smoothTwoFormExterior (o := o)).ker

local instance : AddCommGroup (smoothClosedTwoForms (o := o)) :=
  Submodule.addCommGroup _

local instance : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

def smoothExactTwoForms : Submodule ℝ (smoothClosedTwoForms (o := o)) :=
  (LinearMap.range (smoothOneFormExteriorLinear (o := o))).comap
    (smoothClosedTwoForms (o := o)).subtype

abbrev TwoFormDeRhamCohomology :=
  (smoothClosedTwoForms (o := o)) ⧸ (smoothExactTwoForms (o := o))

def smoothHarmonicToClosed :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] smoothClosedTwoForms (o := o) where
  toFun u := ⟨u.val, u.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def smoothHarmonicToDeRham :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] TwoFormDeRhamCohomology (o := o) :=
  (smoothExactTwoForms (o := o)).mkQ.comp smoothHarmonicToClosed

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothHarmonicToDeRham_injective (hRic : RicciThree g) :
    Function.Injective (smoothHarmonicToDeRham (o := o)) := by
  intro u v huv
  have hz : smoothHarmonicToDeRham (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hm : smoothHarmonicToClosed (u - v) ∈ smoothExactTwoForms :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  change (u - v).val ∈ LinearMap.range (smoothOneFormExteriorLinear (o := o)) at hm
  obtain ⟨a, ha⟩ := hm
  have hh : smoothOneFormExterior a ∈ smoothHarmonicTwoForms :=
    ha.symm ▸ (u - v).property
  have he : (u - v).val = 0 := ha.symm.trans (smoothHarmonic_exact_eq_zero hRic a hh)
  have he' : u - v = 0 := Subtype.ext he
  exact sub_eq_zero.mp he'

theorem smoothHarmonicToDeRham_surjective (hRic : RicciThree g) :
    Function.Surjective (smoothHarmonicToDeRham (o := o)) := by
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (p := smoothExactTwoForms (o := o)) q
  obtain ⟨h, hh, a, he⟩ := exists_smoothHodge_closed_decomposition hRic f.val f.property
  refine ⟨⟨h, hh⟩, ?_⟩
  apply (Submodule.Quotient.eq (smoothExactTwoForms (o := o))).mpr
  change h - f.val ∈ LinearMap.range (smoothOneFormExteriorLinear (o := o))
  refine ⟨-a, ?_⟩
  rw [map_neg]
  change -smoothOneFormExterior a = h - f.val
  rw [he]
  abel

def smoothHarmonicDeRhamEquiv (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) ≃ₗ[ℝ] TwoFormDeRhamCohomology (o := o) :=
  LinearEquiv.ofBijective smoothHarmonicToDeRham
    ⟨smoothHarmonicToDeRham_injective hRic, smoothHarmonicToDeRham_surjective hRic⟩

theorem twoFormDeRhamCohomology_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (TwoFormDeRhamCohomology (o := o)) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  exact FiniteDimensional.of_surjective (smoothHarmonicToDeRham (o := o))
    (smoothHarmonicToDeRham_surjective hRic)

theorem twoFormDeRhamCohomology_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (TwoFormDeRhamCohomology (o := o)) =
      Module.finrank ℝ (smoothHarmonicTwoForms (o := o)) :=
  (smoothHarmonicDeRhamEquiv (o := o) hRic).symm.finrank_eq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local heat operators have compact support and square-summable
images of the orthonormal eigenbasis. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap NNReal BoundedContinuousFunction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
  (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
  {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
  (hs : tsupport a ⊆ V)

theorem twoFormHeat_local_diagonal (s : Finset (TwoFormEigenIndex (o := o) hRic))
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (ha1 : a z = 1) :
    (∑ i ∈ s, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val
      ((chartAt FourSpace c).symm z)‖ ^ 2) ≤
      ∑ r : Fin 6, 2 * ‖twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r‖ ^ 2 := by
  let A := fun r : Fin 6 =>
    twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r
  have he (i : TwoFormEigenIndex (o := o) hRic) (r : Fin 6) :
      ‖A r (twoFormEigenvector hRic i) z‖ =
        ‖twoFormChartValue o (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val c S hS z r‖ := by
    rw [show A r (twoFormEigenvector hRic i) z = _ from
      twoFormHeatChartContinuous_smooth hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp
        a ha hc hs r _ _ (twoFormHeatSection_H1 hRic t ht _) z]
    rw [ha1, Complex.ofReal_one, one_mul, Complex.norm_real]
  calc
    _ = ∑ i ∈ s, ∑ r : Fin 6, ‖A r (twoFormEigenvector hRic i) z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← twoFormChartValue_norm o _ c S hS z hz, EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl (fun r _ => congrArg (fun x : ℝ => x ^ 2) (he i r).symm)
    _ = ∑ r : Fin 6, ∑ i ∈ s, ‖A r (twoFormEigenvector hRic i) z‖ ^ 2 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun r _ =>
      scalarBoundedOperator_bessel (twoFormEigenvector_orthonormal hRic) (A r) s z)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second de Rham dimension is the sum of the two actual Hodge
eigenspace dimensions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

theorem smoothHarmonicPositive_star (hRic : RicciThree g)
    (u : smoothHarmonicPositive (o := o) hRic) :
    smoothHarmonicHodge hRic u.val = u.val := by
  simpa only [one_smul] using (Module.End.mem_eigenspace_iff.mp u.property)

theorem smoothHarmonicNegative_star (hRic : RicciThree g)
    (u : smoothHarmonicNegative (o := o) hRic) :
    smoothHarmonicHodge hRic u.val = -u.val := by
  simpa only [neg_one_smul] using (Module.End.mem_eigenspace_iff.mp u.property)

def smoothHarmonicSumLinear (hRic : RicciThree g) :
    (smoothHarmonicPositive (o := o) hRic × smoothHarmonicNegative (o := o) hRic)
      →ₗ[ℝ] smoothHarmonicTwoForms (o := o) where
  toFun u := u.1.val + u.2.val
  map_add' _ _ := by dsimp; abel
  map_smul' r u := by dsimp; exact (smul_add r u.1.val u.2.val).symm

theorem smoothHarmonicSumLinear_injective (hRic : RicciThree g) :
    Function.Injective (smoothHarmonicSumLinear (o := o) hRic) := by
  intro u v huv
  change u.1.val + u.2.val = v.1.val + v.2.val at huv
  have hs := congrArg (smoothHarmonicHodge hRic) huv
  simp only [map_add, smoothHarmonicPositive_star, smoothHarmonicNegative_star] at hs
  have hp : u.1.val = v.1.val := by
    calc
      u.1.val = (2 : ℝ)⁻¹ • ((u.1.val + u.2.val) + (u.1.val + -u.2.val)) := by module
      _ = (2 : ℝ)⁻¹ • ((v.1.val + v.2.val) + (v.1.val + -v.2.val)) := by rw [huv, hs]
      _ = v.1.val := by module
  have hn : u.2.val = v.2.val := add_left_cancel (hp ▸ huv)
  exact Prod.ext (Subtype.ext hp) (Subtype.ext hn)

def smoothHarmonicSumEquiv (hRic : RicciThree g) :
    (smoothHarmonicPositive (o := o) hRic × smoothHarmonicNegative (o := o) hRic)
      ≃ₗ[ℝ] smoothHarmonicTwoForms (o := o) :=
  LinearEquiv.ofBijective (smoothHarmonicSumLinear hRic)
    ⟨smoothHarmonicSumLinear_injective hRic,
      fun u => ⟨(smoothHarmonicPlus hRic u, smoothHarmonicMinus hRic u),
        smoothHarmonic_decomposition hRic u⟩⟩

theorem twoFormDeRhamCohomology_hodge_dimension (hRic : RicciThree g) :
    Module.finrank ℝ (TwoFormDeRhamCohomology (o := o)) =
      Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) +
        Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) := by
  rw [twoFormDeRhamCohomology_finrank hRic,
    ← (smoothHarmonicSumEquiv (o := o) hRic).finrank_eq, Module.finrank_prod]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual coclosed/codifferential quotient. This is the upper-degree
Hodge-dual complex written in one-form coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev smoothCoClosedOneForms (g : SmoothMetric M) : Submodule ℝ (smoothCovariantFields M 1) :=
  (smoothOneFormDivergence g).ker

local instance hodgeDualClosedAddGroup : AddCommGroup (smoothCoClosedOneForms g) :=
  Submodule.addCommGroup _

def smoothCoexactOneForms : Submodule ℝ (smoothCoClosedOneForms g) :=
  (LinearMap.range (smoothTwoFormCodifferentialLinear (o := o))).comap
    (smoothCoClosedOneForms g).subtype

abbrev HodgeDualOneCohomology :=
  (smoothCoClosedOneForms g) ⧸ (smoothCoexactOneForms (o := o))

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothCoexactOneForms_eq_top (hRic : RicciThree g) :
    smoothCoexactOneForms (o := o) = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := exists_smoothCoexact_of_divergence_eq_zero (o := o) hRic v.val v.property
  change v.val ∈ LinearMap.range (smoothTwoFormCodifferentialLinear (o := o))
  exact ⟨u, hu.symm⟩

theorem hodgeDualOneCohomology_eq_zero (hRic : RicciThree g)
    (q : HodgeDualOneCohomology (o := o)) : q = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := smoothCoexactOneForms (o := o)) q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [smoothCoexactOneForms_eq_top hRic]
  trivial

theorem hodgeDualOneCohomology_subsingleton (hRic : RicciThree g) :
    Subsingleton (HodgeDualOneCohomology (o := o)) :=
  ⟨fun u v => (hodgeDualOneCohomology_eq_zero hRic u).trans
    (hodgeDualOneCohomology_eq_zero hRic v).symm⟩

theorem hodgeDualOneCohomology_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (HodgeDualOneCohomology (o := o)) = 0 := by
  let _ := hodgeDualOneCohomology_subsingleton (o := o) hRic
  exact Module.finrank_zero_of_subsingleton

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual degree-zero, one and two Hodge operators commute with
the exterior derivative and its metric adjoint. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneForm_eq_of_pairings (u v : smoothCovariantFields M 1)
    (h : ∀ w, smoothOneFormL2Pairing (o := o) u w = smoothOneFormL2Pairing (o := o) v w) :
    u = v := by
  apply sub_eq_zero.mp
  apply smoothOneFormL2Pairing_definite (o := o)
  rw [smoothOneFormL2Pairing_sub, h, sub_self]

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormDivergence_differential (f : SmoothScalar (M := M)) :
    smoothOneFormDivergence g (smoothScalarDifferential g f) = smoothScalarLaplacian g f := by
  apply Subtype.ext
  funext x
  exact oneFormDivergence_differential f (frameAt g x)

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormHodgeLaplacian_differential (f : SmoothScalar (M := M)) :
    smoothOneFormHodgeLaplacian (o := o) (smoothScalarDifferential g f) =
      -smoothScalarDifferential g (smoothScalarLaplacian g f) := by
  rw [smoothOneFormHodgeLaplacian_apply, smoothScalarDifferential_closed,
    show smoothTwoFormCodifferentialField (0 : smoothTwoForms o) = 0 from
      (smoothTwoFormCodifferentialLinear (o := o)).map_zero,
    zero_sub, smoothOneFormDivergence_differential]

theorem smoothHodgeLaplacian_of_closed (hRic : RicciThree g) (u : smoothTwoForms o)
    (hu : smoothTwoFormExterior u = 0) :
    smoothHodgeLaplacian hRic u = smoothTwoFormDDelta u := by
  have hz := (smoothTwoForm_closed_iff_codifferential_hodge u).mp hu
  rw [smoothHodgeLaplacian_dDelta_hodge hRic]
  have hw : smoothTwoFormDDelta (smoothTwoFormHodge o u) = 0 := by
    change smoothOneFormExterior (smoothTwoFormCodifferentialField (smoothTwoFormHodge o u)) = 0
    rw [hz]
    exact (smoothOneFormExteriorLinear (o := o)).map_zero
  rw [hw, map_zero, add_zero]

theorem smoothHodgeLaplacian_exterior (hRic : RicciThree g) (u : smoothCovariantFields M 1) :
    smoothHodgeLaplacian hRic (smoothOneFormExterior (o := o) u) =
      smoothOneFormExterior (o := o) (smoothOneFormHodgeLaplacian (o := o) u) := by
  rw [smoothHodgeLaplacian_of_closed hRic _ (smoothOneFormExterior_closed hRic u),
    smoothOneFormHodgeLaplacian_apply]
  change smoothOneFormExteriorLinear _ = smoothOneFormExteriorLinear (_ - _)
  rw [map_sub]
  change smoothOneFormExterior (smoothTwoFormCodifferentialField (smoothOneFormExterior u)) =
    smoothOneFormExterior (smoothTwoFormCodifferentialField (smoothOneFormExterior u)) -
      smoothOneFormExterior (smoothScalarDifferential g (smoothOneFormDivergence g u))
  rw [smoothScalarDifferential_closed, sub_zero]

theorem smoothOneFormHodgeLaplacian_codifferential (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothOneFormHodgeLaplacian (o := o) (smoothTwoFormCodifferentialField u) =
      smoothTwoFormCodifferentialField (smoothHodgeLaplacian hRic u) := by
  apply smoothOneForm_eq_of_pairings (o := o)
  intro v
  rw [smoothOneFormHodgeLaplacian_selfAdjoint hRic,
    smoothTwoFormCodifferential_pairing hRic, smoothTwoFormCodifferential_pairing hRic,
    ← smoothHodgeLaplacian_exterior hRic, smoothHodgeLaplacian_selfAdjoint hRic]

variable [SecondCountableTopology M]

theorem scalarEigen_differential_is_oneFormEigen
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (i : ScalarBaseEigenIndex g o d) :
    smoothOneFormHodgeLaplacian (o := o)
        (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)) =
      scalarBaseHeatRate g o d i • smoothScalarDifferential g (scalarBaseEigenfunction g o d i) := by
  rw [smoothOneFormHodgeLaplacian_differential, scalarBaseEigenfunction_laplacian,
    smoothScalarDifferential_smul]
  module

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every smooth one-form has its actual exact plus coexact decomposition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothOneForm_Hodge_decomposition (hRic : RicciThree g)
    (v : smoothCovariantFields M 1) :
    ∃ f : SmoothScalar (M := M), ∃ u : smoothTwoForms o,
      v = smoothScalarDifferential g f + smoothTwoFormCodifferentialField u := by
  obtain ⟨f, hf, hlap⟩ := actual_petersen_poisson g o hRic
    (oneFormDivergence g v) (oneFormDivergence_smooth v)
  let F : SmoothScalar (M := M) := ⟨f, hf⟩
  let w := v - smoothScalarDifferential g F
  have hw : smoothOneFormDivergence g w = 0 := by
    apply Subtype.ext
    funext x
    let e := frameAt g x
    have hb : e.base = x := rfl
    have he := hlap e
    rw [oneFormDivergence_mean_zero (o := o) hRic v, sub_zero] at he
    have hd := congrArg (fun a : SmoothScalar (M := M) => a.val x)
      (map_sub (smoothOneFormDivergence g) v (smoothScalarDifferential g F))
    change oneFormDivergence g w x =
      oneFormDivergence g v x - oneFormDivergence g (smoothScalarDifferential g F) x at hd
    change oneFormDivergence g w x = 0
    rw [hd, ← hb, oneFormDivergence_differential]
    exact sub_eq_zero.mpr he.symm
  obtain ⟨u, hu⟩ := exists_smoothCoexact_of_divergence_eq_zero (o := o) hRic w hw
  refine ⟨F, u, ?_⟩
  have h := sub_eq_iff_eq_add.mp hu
  exact h.trans (add_comm _ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact/coexact differential identities underlying cancellation of
the nonzero two-form spectrum in the signed trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormDDeltaLinear : smoothTwoForms o →ₗ[ℝ] smoothTwoForms o :=
  smoothOneFormExteriorLinear.comp smoothTwoFormCodifferentialLinear

theorem smoothTwoFormDDeltaLinear_apply (u : smoothTwoForms o) :
    smoothTwoFormDDeltaLinear u = smoothTwoFormDDelta u := rfl

theorem smoothTwoFormDDelta_add (u v : smoothTwoForms o) :
    smoothTwoFormDDelta (u + v) = smoothTwoFormDDelta u + smoothTwoFormDDelta v :=
  smoothTwoFormDDeltaLinear.map_add u v

theorem smoothTwoFormDDelta_smul (r : ℝ) (u : smoothTwoForms o) :
    smoothTwoFormDDelta (r • u) = r • smoothTwoFormDDelta u :=
  smoothTwoFormDDeltaLinear.map_smul r u

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothTwoFormDDelta_hodge_DDelta (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDDelta (smoothTwoFormHodge o (smoothTwoFormDDelta u)) = 0 := by
  have h := (smoothTwoForm_closed_iff_codifferential_hodge (smoothTwoFormDDelta u)).mp
    (smoothTwoFormDDelta_closed hRic u)
  change smoothOneFormExterior (smoothTwoFormCodifferentialField
    (smoothTwoFormHodge o (smoothTwoFormDDelta u))) = 0
  rw [h]
  exact smoothOneFormExteriorLinear.map_zero

theorem smoothHodgeLaplacian_hodge (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic (smoothTwoFormHodge o u) =
      smoothTwoFormHodge o (smoothHodgeLaplacian hRic u) := by
  rw [smoothHodgeLaplacian_dDelta_hodge hRic, smoothHodgeLaplacian_dDelta_hodge hRic,
    map_add, smoothTwoFormHodge_involutive, smoothTwoFormHodge_involutive]
  exact add_comm _ _

theorem smoothTwoFormDDelta_laplacian (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDDelta (smoothHodgeLaplacian hRic u) =
      smoothTwoFormDDelta (smoothTwoFormDDelta u) := by
  rw [smoothHodgeLaplacian_dDelta_hodge hRic, smoothTwoFormDDelta_add,
    smoothTwoFormDDelta_hodge_DDelta hRic, add_zero]

theorem smoothHodgeLaplacian_DDelta (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic (smoothTwoFormDDelta u) =
      smoothTwoFormDDelta (smoothTwoFormDDelta u) := by
  rw [smoothHodgeLaplacian_dDelta_hodge hRic, smoothTwoFormDDelta_hodge_DDelta hRic,
    map_zero, add_zero]

theorem smoothTwoFormDDelta_eigen_square (hRic : RicciThree g) (κ : ℝ)
    (u : smoothTwoForms o) (hu : smoothHodgeLaplacian hRic u = κ • u) :
    smoothTwoFormDDelta (smoothTwoFormDDelta u) = κ • smoothTwoFormDDelta u := by
  rw [← smoothTwoFormDDelta_laplacian hRic, hu, smoothTwoFormDDelta_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite chart cover gives a uniform diagonal bound for the actual
positive-time two-form heat operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric
open scoped BigOperators Manifold ContDiff NNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_local_diagonal_bound (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x : M) :
    ∃ (O : Set M) (C : ℝ), IsOpen O ∧ x ∈ O ∧ 0 ≤ C ∧
      ∀ (s : Finset (TwoFormEigenIndex (o := o) hRic)) (y : M), y ∈ O →
        (∑ i ∈ s, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val y‖ ^ 2) ≤ C := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let a : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have haV : tsupport (a : FourSpace → ℝ) ⊆ V := by rw [a.tsupport_eq]; exact hdV
  let A := fun r : Fin 6 => twoFormHeatChartContinuous hRic t ht x S hS hcχ hKt
    hV hVK U hU hUt hχU hp a a.contDiff a.hasCompactSupport haV r
  let C := ∑ r : Fin 6, 2 * ‖A r‖ ^ 2
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' ball z₀.val (d / 2)
  refine ⟨O, C, (chartAt FourSpace x).isOpen_inter_preimage isOpen_ball,
    ⟨mem_chart_source FourSpace x, mem_ball_self (half_pos hd)⟩,
    Finset.sum_nonneg (fun r _ => mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro s y hy
  have hz : chartAt FourSpace x y ∈ (chartAt FourSpace x).target :=
    (chartAt FourSpace x).mapsTo hy.1
  have hone : a (chartAt FourSpace x y) = 1 := a.one_of_mem_closedBall (ball_subset_closedBall hy.2)
  have h := twoFormHeat_local_diagonal hRic t ht x S hS hcχ hKt hV hVK U hU hUt hχU hp
    a a.contDiff a.hasCompactSupport haV s (chartAt FourSpace x y) hz hone
  rw [(chartAt FourSpace x).left_inv hy.1] at h
  exact h

theorem twoFormHeat_diagonal_bound (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset (TwoFormEigenIndex (o := o) hRic)) (y : M),
      (∑ i ∈ s, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val y‖ ^ 2) ≤ C := by
  classical
  choose O C hO hx hC hb using twoFormHeat_local_diagonal_bound (o := o) hRic t ht
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨q, hq⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  refine ⟨∑ x ∈ q, C x, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  intro s y
  obtain ⟨x, hxq, hy⟩ := mem_iUnion₂.mp (hq (mem_univ y))
  exact (hb x s y hy).trans (Finset.single_le_sum (fun z _ => hC z) hxq)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cokernel of actual smooth divergence is measured exactly by the
scalar integral. No upper-degree index identity is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M}

local instance divergenceMeanCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

def smoothScalarMean (g : SmoothMetric M) (o : FrameOrientation g) :
    SmoothScalar (M := M) →ₗ[ℝ] ℝ where
  toFun f := ∫ e, f.val e.base ∂canonicalFrameMeasure g o
  map_add' f h := integral_add
    ((f.property.continuous.comp (continuous_frameBase g)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((h.property.continuous.comp (continuous_frameBase g)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  map_smul' r f := by
    change (∫ e, r * f.val e.base ∂canonicalFrameMeasure g o) = _
    exact integral_const_mul r _

theorem smoothScalarMean_const (o : FrameOrientation g) (r : ℝ) :
    smoothScalarMean g o (smoothScalarConst r) = r := by
  simp [smoothScalarMean, smoothScalarConst]

abbrev DivergenceCokernel (g : SmoothMetric M) :=
  SmoothScalar (M := M) ⧸ (LinearMap.range (smoothOneFormDivergence g))

def divergenceCokernelMean (o : FrameOrientation g) (hRic : RicciThree g) :
    DivergenceCokernel g →ₗ[ℝ] ℝ :=
  (LinearMap.range (smoothOneFormDivergence g)).liftQ (smoothScalarMean g o) (by
    rintro f ⟨v, rfl⟩
    exact oneFormDivergence_mean_zero (o := o) hRic v)

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem mem_divergence_range_iff_mean_zero (o : FrameOrientation g) (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) :
    f ∈ LinearMap.range (smoothOneFormDivergence g) ↔ smoothScalarMean g o f = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact oneFormDivergence_mean_zero (o := o) hRic v
  · intro hmean
    obtain ⟨φ, hφ, hlap⟩ := actual_petersen_poisson g o hRic f.val f.property
    let F : SmoothScalar (M := M) := ⟨φ, hφ⟩
    refine ⟨smoothScalarDifferential g F, ?_⟩
    apply Subtype.ext
    funext x
    let e := frameAt g x
    have he := hlap e
    change (∫ e, f.val e.base ∂canonicalFrameMeasure g o) = 0 at hmean
    rw [hmean, sub_zero] at he
    exact (oneFormDivergence_differential F e).trans he

theorem divergenceCokernelMean_zero (o : FrameOrientation g) (hRic : RicciThree g)
    (q : DivergenceCokernel g) (hq : divergenceCokernelMean o hRic q = 0) : q = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := LinearMap.range (smoothOneFormDivergence g)) q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (mem_divergence_range_iff_mean_zero o hRic f).mpr
  exact hq

theorem divergenceCokernelMean_bijective (o : FrameOrientation g) (hRic : RicciThree g) :
    Function.Bijective (divergenceCokernelMean o hRic) := by
  constructor
  · intro u v huv
    apply sub_eq_zero.mp
    apply divergenceCokernelMean_zero o hRic
    rw [map_sub, huv, sub_self]
  · intro r
    refine ⟨(LinearMap.range (smoothOneFormDivergence g)).mkQ (smoothScalarConst r), ?_⟩
    exact smoothScalarMean_const o r

def divergenceCokernelEquiv (o : FrameOrientation g) (hRic : RicciThree g) :
    DivergenceCokernel g ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (divergenceCokernelMean o hRic)
    (divergenceCokernelMean_bijective o hRic)

theorem divergenceCokernel_finrank (o : FrameOrientation g) (hRic : RicciThree g) :
    Module.finrank ℝ (DivergenceCokernel g) = 1 := by
  rw [(divergenceCokernelEquiv o hRic).finrank_eq]
  exact Module.finrank_self ℝ

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hodge summand with zero Weyl curvature has no nonzero harmonic
forms. This follows from the actual integrated Weitzenbock identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance halfFlatHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
local instance halfFlatNegativeAddGroup (hRic : RicciThree g) :
    AddCommGroup (smoothHarmonicNegative (o := o) hRic) := Submodule.addCommGroup _

theorem halfFlat_negative_harmonic_zero (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (u : smoothHarmonicNegative (o := o) hRic) : u = 0 := by
  have hstar (x : M) : twoFormHodge (u.val.val.val x) = -u.val.val.val x := by
    have hh := congrArg (fun v : smoothHarmonicTwoForms (o := o) => v.val.val x)
      (smoothHarmonicNegative_star hRic u)
    exact hh
  have hcurv : smoothTwoFormCurvature u.val.val = u.val.val := by
    apply Subtype.ext
    funext x
    exact halfFlat_curvature_action_negative hRic hminus x _ (hstar x)
  have hE := smoothTwoForm_Weitzenbock hRic u.val.val
  rw [smoothHarmonicTwoForm_energy_zero u.val.val u.val.property, hcurv] at hE
  have hcov := smoothTwoFormCovariantEnergy_nonneg u.val.val
  have hnorm := smoothTwoFormL2Inner_nonneg u.val.val
  have hz : smoothTwoFormL2Inner u.val.val u.val.val = 0 := by linarith
  have hform := smoothTwoFormL2Inner_definite u.val.val hz
  apply Subtype.ext
  apply Subtype.ext
  exact hform

theorem halfFlat_negative_harmonic_dimension_zero (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0) :
    Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) = 0 := by
  let : Subsingleton (smoothHarmonicNegative (o := o) hRic) :=
    ⟨fun u v => (halfFlat_negative_harmonic_zero hRic hminus u).trans
      (halfFlat_negative_harmonic_zero hRic hminus v).symm⟩
  exact Module.finrank_zero_of_subsingleton

end
end PositiveEinsteinFour.Geometry
end


section

/-! Derivatives of the actual scalar and two-form eigenfamilies are total
in the one-form L2 completion. No spectral completeness is assumed in degree one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def oneFormDerivedFamily (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ScalarBaseEigenIndex g o d ⊕ TwoFormEigenIndex (o := o) hRic → OneFormL2 o
  | .inl i => smoothOneFormToL2 ⟨smoothScalarDifferential g (scalarBaseEigenfunction g o d i)⟩
  | .inr i => smoothOneFormToL2 ⟨smoothTwoFormCodifferentialField (twoFormEigenform hRic i)⟩

theorem oneFormDerivedFamily_total (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    (Submodule.span ℝ (range (oneFormDerivedFamily hRic d))).topologicalClosure = ⊤ := by
  let S := (Submodule.span ℝ (range (oneFormDerivedFamily hRic d))).topologicalClosure
  have hS : IsClosed (S : Set (OneFormL2 o)) := Submodule.isClosed_topologicalClosure _
  have hD (u : scalarH1 d) : scalarH1Differential d u ∈ S := by
    apply continuousLinearMap_mem_closed_of_total _ (scalarH1_eigenfunctions_total g o d)
      (scalarH1Differential d) S hS _ u
    intro i
    rw [scalarH1Differential_smooth]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
  have hδ (u : TwoFormH1 o) : twoFormH1Codifferential hRic u ∈ S := by
    apply continuousLinearMap_mem_closed_of_total _ (twoFormH1_eigenforms_total hRic)
      (twoFormH1Codifferential hRic) S hS _ u
    intro i
    exact (congrArg (fun z : OneFormL2 o => z ∈ S)
      (twoFormH1Codifferential_smooth hRic
        (twoFormEigenform hRic i : SmoothH1TwoForm o))).mpr
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  have hsmooth (u : SmoothL2OneForm o) : smoothOneFormToL2 u ∈ S := by
    obtain ⟨a, b, hab⟩ := exists_smoothOneForm_Hodge_decomposition (o := o) hRic u.toSmooth
    have he : u = (⟨smoothScalarDifferential g a⟩ : SmoothL2OneForm o) +
        ⟨smoothTwoFormCodifferentialField b⟩ := by
      apply (smoothL2OneFormEquiv o).injective
      exact hab
    rw [he, map_add]
    have ha := hD (smoothScalarToH1 d a)
    have hb := hδ (smoothTwoFormToH1 (b : SmoothH1TwoForm o))
    rw [scalarH1Differential_smooth] at ha
    have hb' := (congrArg (fun z : OneFormL2 o => z ∈ S)
      (twoFormH1Codifferential_smooth hRic (b : SmoothH1TwoForm o))).mp hb
    exact S.add_mem ha hb'
  apply top_unique
  intro u _
  apply hS.closure_subset_iff.mpr (show range (smoothOneFormToL2 (o := o)) ⊆ S from ?_)
    (smoothOneFormToL2_dense u)
  rintro _ ⟨v, rfl⟩
  exact hsmooth v

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual smooth solvability in degree one follows from the proved
scalar and two-form Poisson equations and the exact/coexact decomposition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothOneFormHodgePoisson (hRic : RicciThree g)
    (f : smoothCovariantFields M 1) :
    ∃ u : smoothCovariantFields M 1, smoothOneFormHodgeLaplacian (o := o) u = f := by
  obtain ⟨a, b, hf⟩ := exists_smoothOneForm_Hodge_decomposition (o := o) hRic f
  obtain ⟨φ, hφ, hφeq⟩ := actual_petersen_poisson g o hRic a.val a.property
  let Φ : SmoothScalar (M := M) := ⟨φ, hφ⟩
  have hΦ : smoothScalarLaplacian g Φ = a -
      smoothScalarConst (∫ e, a.val e.base ∂canonicalFrameMeasure g o) := by
    apply Subtype.ext
    funext x
    exact hφeq (frameAt g x)
  have hdΦ : smoothScalarDifferential g (smoothScalarLaplacian g Φ) =
      smoothScalarDifferential g a := by
    rw [hΦ]
    change smoothScalarDifferentialLinear g (_ - _) = _
    rw [map_sub]
    change smoothScalarDifferential g a - smoothScalarDifferential g (smoothScalarConst _) = _
    rw [smoothScalarDifferential_const, sub_zero]
  obtain ⟨h, hh, U, hU⟩ := exists_smoothHodge_decomposition hRic b
  have hz : smoothTwoFormCodifferentialField h = 0 :=
    (smoothTwoFormCodifferentialField_eq_zero_iff h).mpr
      (funext fun e => funext fun k => ((mem_smoothHarmonicTwoForms h).mp hh).2 e k)
  have hδ : smoothTwoFormCodifferentialField (smoothHodgeLaplacian hRic U) =
      smoothTwoFormCodifferentialField b := by
    rw [hU, smoothTwoFormCodifferentialField_add, hz, zero_add]
  refine ⟨-smoothScalarDifferential g Φ + smoothTwoFormCodifferentialField U, ?_⟩
  rw [map_add, map_neg, smoothOneFormHodgeLaplacian_differential, neg_neg,
    smoothOneFormHodgeLaplacian_codifferential hRic, hdΦ, hδ]
  exact hf.symm

theorem existsUnique_smoothOneFormHodgePoisson (hRic : RicciThree g)
    (f : smoothCovariantFields M 1) :
    ∃! u : smoothCovariantFields M 1, smoothOneFormHodgeLaplacian (o := o) u = f := by
  obtain ⟨u, hu⟩ := exists_smoothOneFormHodgePoisson (o := o) hRic f
  exact ⟨u, hu, fun v hv => smoothOneFormHodgeLaplacian_injective hRic (hv.trans hu.symm)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Summability of the actual positive-time Hodge heat eigenvalues.
The proof integrates the geometric diagonal bound against normalized volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatSection_eigen_integral (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (i : TwoFormEigenIndex (o := o) hRic) :
    (∫ x, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val x‖ ^ 2
      ∂normalizedVolume g) = twoFormHeatWeight hRic t i.1 ^ 2 := by
  calc
    _ = ‖smoothTwoFormToL2
        (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i) : SmoothL2TwoForm o)‖ ^ 2 :=
      (smoothTwoFormToL2_norm_sq _).symm
    _ = ‖twoFormHeat hRic t (twoFormEigenvector hRic i)‖ ^ 2 :=
      congrArg (fun f : TwoFormL2 o => ‖f‖ ^ 2) (twoFormHeatSection_L2 hRic t ht _)
    _ = _ := by
      rw [twoFormHeat_eigenvector, norm_smul, Real.norm_eq_abs,
        (twoFormEigenvector_orthonormal hRic).1 i, mul_one, sq_abs]

theorem twoFormHeat_weight_square_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic => twoFormHeatWeight hRic t i.1 ^ 2) := by
  have := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  obtain ⟨C, _, hC⟩ := twoFormHeat_diagonal_bound (o := o) hRic t ht
  apply summable_of_sum_le (fun _ => sq_nonneg _) (c := C)
  intro s
  have hi (i : TwoFormEigenIndex (o := o) hRic) : Integrable
      (fun x => ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val x‖ ^ 2)
      (normalizedVolume g) :=
    ((smoothTwoForm_norm_continuous _).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ x, ∑ i ∈ s, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val x‖ ^ 2
        ∂normalizedVolume g := by
      rw [integral_finsetSum s (fun i _ => hi i)]
      exact Finset.sum_congr rfl (fun i _ => (twoFormHeatSection_eigen_integral hRic t ht i).symm)
    _ ≤ ∫ _x, C ∂normalizedVolume g := integral_mono
      (integrable_finsetSum s (fun i _ => hi i)) (integrable_const C) (hC s)
    _ = C := by simp

theorem twoFormHeat_weight_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic => twoFormHeatWeight hRic t i.1) := by
  have hs := twoFormHeat_weight_square_summable (o := o) hRic (t / 2) (half_pos ht)
  apply hs.congr
  intro i
  simp only [twoFormHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integral intersection pairing, its exact-form annihilator, and
its signs on the actual harmonic Hodge summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

def twoFormIntersection (u v : smoothTwoForms o) : ℝ :=
  smoothTwoFormL2Inner u (smoothTwoFormHodge o v)

theorem twoFormIntersection_comm (u v : smoothTwoForms o) :
    twoFormIntersection u v = twoFormIntersection v u := by
  unfold twoFormIntersection
  rw [← smoothTwoFormL2Inner_hodge_left, smoothTwoFormL2Inner_comm]

theorem twoFormIntersection_add_left (u v w : smoothTwoForms o) :
    twoFormIntersection (u + v) w = twoFormIntersection u w + twoFormIntersection v w :=
  smoothTwoFormL2Inner_add u v _

omit [CompactSpace M] [Nonempty M] in
theorem twoFormIntersection_smul_left (r : ℝ) (u v : smoothTwoForms o) :
    twoFormIntersection (r • u) v = r * twoFormIntersection u v :=
  smoothTwoFormL2Inner_smul r u _

theorem twoFormIntersection_add_right (u v w : smoothTwoForms o) :
    twoFormIntersection u (v + w) = twoFormIntersection u v + twoFormIntersection u w := by
  rw [twoFormIntersection_comm, twoFormIntersection_add_left,
    twoFormIntersection_comm v u, twoFormIntersection_comm w u]

theorem twoFormIntersection_smul_right (r : ℝ) (u v : smoothTwoForms o) :
    twoFormIntersection u (r • v) = r * twoFormIntersection u v := by
  rw [twoFormIntersection_comm, twoFormIntersection_smul_left, twoFormIntersection_comm v u]

theorem twoFormIntersection_exact_closed (hRic : RicciThree g)
    (a : smoothCovariantFields (M := M) 1) (v : smoothTwoForms o)
    (hv : smoothTwoFormExterior v = 0) :
    twoFormIntersection (smoothOneFormExterior a) v = 0 := by
  unfold twoFormIntersection
  rw [← smoothTwoFormL2Inner_hodge_left]
  exact smoothOneForm_coexact_orthogonal_closed hRic a v hv

def smoothHarmonicIntersection :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] smoothHarmonicTwoForms (o := o) →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => twoFormIntersection u.val v.val
      map_add' := fun v w => twoFormIntersection_add_right u.val v.val w.val
      map_smul' := fun r v => twoFormIntersection_smul_right r u.val v.val }
  map_add' u v := by ext w; exact twoFormIntersection_add_left u.val v.val w.val
  map_smul' r u := by ext v; exact twoFormIntersection_smul_left r u.val v.val

theorem smoothHarmonicIntersection_nondegenerate (hRic : RicciThree g)
    (u : smoothHarmonicTwoForms (o := o))
    (hu : ∀ v, smoothHarmonicIntersection u v = 0) : u = 0 := by
  have h := hu (smoothHarmonicHodge hRic u)
  change smoothTwoFormL2Inner u.val
    (smoothTwoFormHodge o (smoothTwoFormHodge o u.val)) = 0 at h
  rw [smoothTwoFormHodge_involutive] at h
  exact Subtype.ext (smoothTwoFormL2Inner_definite u.val h)

theorem smoothHarmonicIntersection_positive (hRic : RicciThree g)
    (u : smoothHarmonicPositive (o := o) hRic) :
    twoFormIntersection u.val.val u.val.val = smoothTwoFormL2Inner u.val.val u.val.val := by
  have h := congrArg Subtype.val (smoothHarmonicPositive_star hRic u)
  exact congrArg (smoothTwoFormL2Inner u.val.val) h

theorem smoothHarmonicIntersection_negative (hRic : RicciThree g)
    (u : smoothHarmonicNegative (o := o) hRic) :
    twoFormIntersection u.val.val u.val.val = -smoothTwoFormL2Inner u.val.val u.val.val := by
  have h := congrArg Subtype.val (smoothHarmonicNegative_star hRic u)
  change smoothTwoFormHodge o u.val.val = -u.val.val at h
  unfold twoFormIntersection
  rw [h, smoothTwoFormL2Inner_comm, ← neg_one_smul ℝ u.val.val,
    smoothTwoFormL2Inner_smul]
  ring

theorem smoothHarmonicIntersection_orthogonal (hRic : RicciThree g)
    (u : smoothHarmonicPositive (o := o) hRic)
    (v : smoothHarmonicNegative (o := o) hRic) :
    smoothTwoFormL2Inner u.val.val v.val.val = 0 := by
  have hp := congrArg Subtype.val (smoothHarmonicPositive_star hRic u)
  have hn := congrArg Subtype.val (smoothHarmonicNegative_star hRic v)
  change smoothTwoFormHodge o u.val.val = u.val.val at hp
  change smoothTwoFormHodge o v.val.val = -v.val.val at hn
  have h := smoothTwoFormL2Inner_hodge_left u.val.val v.val.val
  rw [hp, hn, smoothTwoFormL2Inner_comm u.val.val (-v.val.val),
    ← neg_one_smul ℝ v.val.val, smoothTwoFormL2Inner_smul,
    smoothTwoFormL2Inner_comm v.val.val u.val.val] at h
  linarith only [h]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth Hodge eigenspace is linearly equivalent to its
finite-dimensional resolvent eigenspace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_resolvent_eigen (hRic : RicciThree g) (μ κ : ℝ)
    (hμκ : μ * (κ + 1) = 1) (u : smoothTwoForms o)
    (hu : smoothHodgeLaplacian hRic u = κ • u) :
    twoFormShiftedResolvent hRic (smoothTwoFormToL2 (u : SmoothL2TwoForm o)) =
      μ • smoothTwoFormToL2 (u : SmoothL2TwoForm o) := by
  have hJ : twoFormH1ToL2 (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) =
      smoothTwoFormToL2 (u : SmoothL2TwoForm o) := twoFormH1ToL2_smooth (u : SmoothH1TwoForm o)
  have hq (v : TwoFormH1 o) :
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) v =
        κ * inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o)) (twoFormH1ToL2 v) := by
    rw [smoothHodgeLaplacian_weak hRic, hu]
    calc
      _ = inner ℝ (κ • smoothTwoFormToL2 (u : SmoothL2TwoForm o)) (twoFormH1ToL2 v) :=
        congrArg (fun z : TwoFormL2 o => inner ℝ z (twoFormH1ToL2 v))
          (smoothTwoFormToL2.map_smul κ (u : SmoothL2TwoForm o))
      _ = _ := by rw [real_inner_smul_left]
  have hs : μ • smoothTwoFormToH1 (u : SmoothH1TwoForm o) =
      twoFormShiftedSolution hRic (smoothTwoFormToL2 (u : SmoothL2TwoForm o)) := by
    apply twoFormShiftedSolution_unique hRic
    intro v
    rw [twoFormHodgeForm_smul_left, map_smul, hJ,
      real_inner_smul_left, hq]
    calc
      _ = (μ * (κ + 1)) * inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o))
          (twoFormH1ToL2 v) := by ring
      _ = _ := by rw [hμκ, one_mul]
  change twoFormH1ToL2 (twoFormShiftedSolution hRic _) = _
  rw [← hs, map_smul]
  exact congrArg (μ • ·) hJ

def TwoFormSmoothEigenSpace (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :=
  Module.End.eigenspace (smoothHodgeLaplacianLinear (o := o) hRic) (μ.val⁻¹ - 1)

def twoFormSmoothEigenL2 (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :
    TwoFormSmoothEigenSpace hRic μ →ₗ[ℝ] TwoFormSpectralSpace hRic μ where
  toFun u := ⟨smoothTwoFormToL2 (u.val : SmoothL2TwoForm o), by
    apply Module.End.mem_eigenspace_iff.mpr
    apply smoothTwoForm_resolvent_eigen hRic μ.val (μ.val⁻¹ - 1) _ u.val
      (Module.End.mem_eigenspace_iff.mp u.property)
    have hne := ne_of_gt (twoFormSpectralValue_bounds hRic μ).1
    field_simp
    ring⟩
  map_add' u v := Subtype.ext (smoothTwoFormToL2.map_add
    (u.val : SmoothL2TwoForm o) (v.val : SmoothL2TwoForm o))
  map_smul' r u := Subtype.ext (smoothTwoFormToL2.map_smul r (u.val : SmoothL2TwoForm o))

theorem twoFormSmoothEigenL2_injective (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    Function.Injective (twoFormSmoothEigenL2 hRic μ) := by
  intro u v h
  exact Subtype.ext (smoothTwoFormToL2_injective (congrArg Subtype.val h))

theorem twoFormSmoothEigenL2_surjective (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    Function.Surjective (twoFormSmoothEigenL2 hRic μ) := by
  intro f
  by_cases hf : f.val = 0
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    change smoothTwoFormToL2 (0 : SmoothL2TwoForm o) = f.val
    rw [map_zero, hf]
  · obtain ⟨w, hw, he⟩ := twoFormResolvent_eigenvector_smooth hRic ⟨f.property, hf⟩
    exact ⟨⟨w, Module.End.mem_eigenspace_iff.mpr he⟩, Subtype.ext hw.symm⟩

def twoFormSmoothEigenEquiv (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    TwoFormSmoothEigenSpace hRic μ ≃ₗ[ℝ] TwoFormSpectralSpace hRic μ :=
  LinearEquiv.ofBijective (twoFormSmoothEigenL2 hRic μ)
    ⟨twoFormSmoothEigenL2_injective hRic μ, twoFormSmoothEigenL2_surjective hRic μ⟩

instance twoFormSmoothEigenFinite (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    FiniteDimensional ℝ (TwoFormSmoothEigenSpace hRic μ) :=
  FiniteDimensional.of_injective (twoFormSmoothEigenL2 hRic μ)
    (twoFormSmoothEigenL2_injective hRic μ)

end
end PositiveEinsteinFour.Geometry
end

end OAI
