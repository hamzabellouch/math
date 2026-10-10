import OAI.MeasureTheory.Falconer.Radial.WeakRadial
import OAI.MeasureTheory.Falconer.Geometry.SmallChartCube
import OAI.MeasureTheory.Falconer.Radial.RadialCapExtension

namespace OAI

/-! # Weak radial pruning on the actual small chart law -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem small_chart_weak_radial (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    {ζ ell e : ℝ} (hζ : 0 < ζ) (hell0 : 0 ≤ ell)
    (hell : ell < ((n:ℝ)/(n+1))*(n:ℝ)) (he : 0 < e) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^(n:ℝ))) →
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (∀ p z, (p,z) ∈ G → z ≠ p) ∧
        (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space (n+1),
          μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
            ENNReal.ofReal (((2:ℝ)^N)^e*(3*(1/(2:ℝ)^j))^ell) := by
  obtain ⟨ε,c,hε,hc,N₀,hN₀⟩ := weak_radial hLW hn hζ hell0 hell he
    (smallChartCube (n+1)) (smallChartCube_side _) (M := Real.sqrt (n+1:ℕ)+1)
    (by nlinarith [Real.sqrt_nonneg (n+1:ℕ)]) (fun _ hx => smallChartCube_norm hx)
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN μ _ hμ hball hslab
  obtain ⟨G,hG,hdiag,hcost,hcap⟩ := hN₀ N hN μ (smallChartCube_full μ hμ) hball hslab
  have hext := radial_cap_extension μ G (Real.one_le_rpow (one_le_pow₀ (by norm_num)) he.le) hell0 hcap
  refine ⟨G,hG,?_,hcost,?_⟩
  · intro p z hp hz
    subst z
    exact hdiag p hp
  · intro p j hj u
    apply hext
    have hh : ((2:ℝ)^N)⁻¹ ≤ ((2:ℝ)^j)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hj)
    simpa only [one_div] using hh.trans (show ((2:ℝ)^j)⁻¹ ≤ 3*((2:ℝ)^j)⁻¹ by linarith [show (0:ℝ) ≤ ((2:ℝ)^j)⁻¹ by positivity])

end Falconer

end OAI
