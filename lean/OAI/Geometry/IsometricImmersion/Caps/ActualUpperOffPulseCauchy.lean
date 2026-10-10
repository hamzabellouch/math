import OAI.Geometry.IsometricImmersion.Caps.FixedRadiusOffPulseCauchy
import OAI.Geometry.IsometricImmersion.Caps.ReflectedActualCapFlow
import OAI.Geometry.IsometricImmersion.Caps.CauchyReflection

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.Flow.Reflection SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Taylor
open SmoothLocal.Model

theorem exists_actual_upper_off_pulse_cauchy_bounds_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U : Set Coord) (z : Coord → ℝ),
          SmoothPositiveOn g0 U → SmoothPositiveOn (perturbedMetric g0 eta.val) U →
          IsOpen U → modelSquare ⊆ U →
          (∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 8 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
            ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
              (delta/(tau : ℝ))) x‖ ≤ B ∧
            ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
              (delta/(tau : ℝ))) x‖ ≤ B := by
  have hqneg : |-q0| ≤ (1 : ℝ)/20 := by simpa only [abs_neg] using hq0
  obtain ⟨B,hB,hcauchy⟩ := exists_actual_off_pulse_cauchy_bounds_at_radius
    (q0 := -q0) (reflectedMetric_smoothPositive hgStar) (reflectedDomain_isOpen hV)
    (reflectedDomain_contains_modelSquare hSV) M hG hd hkappa hM hqneg hr hrhalf hLr hrsmall K
  refine ⟨B,hB,?_⟩
  intro N delta hdelt
  filter_upwards [hcauchy N delta hdelt] with tau hcauchyTau
  intro g0 eta U z hg0 hg hU hSU hbackground hh hclass hgB hdet hcenter happ x hx n hn
  let g := perturbedMetric g0 eta.val
  let gr := reflectedMetric g
  let zr := reflectedScalar z
  let UR := reflectPoint ⁻¹' U
  let etaR : metricPatchSet gr kappa := ⟨0,reflected_actual_metric_zero_patch eta hclass⟩
  have heR : perturbedMetric gr etaR.val = gr := perturbedMetric_zero gr
  have hgR : SmoothPositiveOn gr UR := reflectedMetric_smoothPositive hg
  have hhR : CapInductionHeight gr UR (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) zr :=
    reflected_capInductionHeight hg hU hSU hh
  have hcR : BoundedAdmissibleHeight gr M zr := hclass.reflected
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨WR,YR,hfR⟩ := exists_actual_reflected_capInductionFlow eta hg0 hg hU hSU
    hG (Nat.cast_nonneg M) hd (one_div_pos.mpr hMR) (one_div_pos.mpr hMR)
    hgB hdet hh hkappa hbackground
  have hg4R : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => gr a i j) p‖ ≤ G := by
    intro i j k hk p hp
    change ‖iteratedFDeriv ℝ k (fun a => reflectedMetric g a i j) p‖ ≤ G
    rw [reflectedMetric_entry_jet_norm]
    exact hgB i j k (by omega) _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hdetR : ∀ p ∈ modelSquare, d ≤ |(gr p).det| := by
    intro p hp
    change d ≤ |(reflectedMetric g p).det|
    rw [reflectedMetric_det]
    exact hdet _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hcenterR : |hessianQuotient gr zr 0-(-q0)| ≤ 1/(100*boundedClassWidth kappa M) := by
    change |hessianQuotient (reflectedMetric g) (reflectedScalar z) 0-(-q0)| ≤ _
    rw [bounded_class_reflected_center hclass q0]
    exact hcenter
  have happR : ∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gr q i j-
        testMetric (reflectedMetric gStar) (-q0) (boundedClassWidth kappa M*r/16)
          N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau := by
    intro i j k hk p hp
    change ‖iteratedFDeriv ℝ k (fun q => reflectedMetric g q i j-
      testMetric (reflectedMetric gStar) (-q0) (boundedClassWidth kappa M*r/16)
        N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau
    rw [reflected_pulse_approximation_jet_norm]
    exact happ i j k hk _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hbound := hcauchyTau gr etaR UR WR zr YR
    (by simpa only [heR] using hgR) (reflectedDomain_isOpen hU)
    (by simpa only [heR] using hhR) (by simpa only [heR] using hfR)
    (by simpa only [heR] using hcR) (by simpa only [heR] using hg4R)
    (by simpa only [heR] using hdetR) (by simpa only [heR] using hcenterR)
    (by simpa only [heR] using happR) x hx n hn
  have he := sheared_reflected_Cauchy_jet_norms z q0 (-delta/(tau : ℝ)) x n
  change (‖iteratedFDeriv ℝ n (heightCauchyValue
      (heightInShearCoordinates (reflectedScalar z) (-q0)) (-delta/(tau : ℝ))) x‖ ≤ B ∧
    ‖iteratedFDeriv ℝ n (heightCauchyVelocity
      (heightInShearCoordinates (reflectedScalar z) (-q0)) (-delta/(tau : ℝ))) x‖ ≤ B) at hbound
  rw [he.1,he.2] at hbound
  simpa only [neg_div,neg_neg] using hbound

end SmoothLocal.Perturbation

end

end OAI
