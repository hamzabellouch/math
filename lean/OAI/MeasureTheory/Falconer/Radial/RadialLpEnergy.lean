import OAI.MeasureTheory.Falconer.Radial.FiniteRadialTestEnergy
import OAI.MeasureTheory.Falconer.Measures.ExtendedDensityNorm

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem radial_Lp_energy_bound (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K : Set Plane} (hK : IsCompact K)
    (hα : ∀ᵐ z ∂α, z ∈ K) {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D)
    (hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x) :
    radialEnergyPrefactor s p *
      (∫⁻ x, (sourceDensityNorm p (α.map (sourceRadialUnit x)))^p ∂β) ≤
        radialEnergyMajorant α β D s t p := by
  simp_rw [← sourceTestNorm_eq_densityNorm _ hpq]
  exact radial_testNorm_energy_bound α β hK hα hpq hp2 hs1 hs2 hD hupt htp hdiam hbound hx

theorem finite_radial_Lp_integral (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K L : Set Plane}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : Disjoint K L)
    (hα : ∀ᵐ z ∂α, z ∈ K) (hβ : ∀ᵐ z ∂β, z ∈ L) {s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hEα : rieszEnergy α s < ∞) (hEβ : rieszEnergy β t < ∞) :
    (∫⁻ x, (sourceDensityNorm p (α.map (sourceRadialUnit x)))^p ∂β) < ∞ := by
  let D := Metric.diam (K ∪ L) + 1
  have hD : 0 < D := add_pos_of_nonneg_of_pos Metric.diam_nonneg zero_lt_one
  have hdist {x y : Plane} (hx : x ∈ K ∪ L) (hy : y ∈ K ∪ L) : dist x y ≤ D :=
    (dist_le_diam_of_mem (hK.union hL).isBounded hx hy).trans
      (le_add_of_nonneg_right zero_le_one)
  have hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D := by
    apply (Measure.ae_prod_iff_ae_ae (p := fun z : Plane × Plane => dist z.1 z.2 ≤ D) ((isClosed_le (continuous_fst.dist continuous_snd) continuous_const).measurableSet)).mpr
    filter_upwards [hβ] with x hx
    filter_upwards [hβ] with y hy
    exact hdist (Or.inr hx) (Or.inr hy)
  have hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D :=
    hβ.mono (fun x hx y hy => hdist (Or.inl hy) (Or.inr hx))
  have hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x := by
    filter_upwards [hβ] with x hx
    filter_upwards [hα] with y hy
    intro he
    exact Set.disjoint_left.mp hKL (he ▸ hy) hx
  simp_rw [← sourceTestNorm_eq_densityNorm _ hpq]
  exact finite_radial_testNorm_integral α β hK hα hpq hp2 hs1 hs2 hD hupt htp hdiam hbound hx hEα hEβ

end PlanarFalconer

end OAI
