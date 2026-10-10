import OAI.Analysis.PlanarEndpoint.DualMass
import OAI.Analysis.PlanarEndpoint.DyadicArithmetic
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphDual
import OAI.Analysis.PlanarEndpoint.GraphLocalization
import OAI.Analysis.PlanarEndpoint.TimeSeparation

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace PlanarEndpoint

lemma normalize_mass_energy {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (v : V) {N C m p : ℝ} (hN : 0 < N) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hb : ‖v‖ ≤ C*N^(1/3:ℝ)*m^(1-1/p)) :
    ‖(N^(-(1/3:ℝ))) • v‖^2 ≤ C^2*m^(2-2/p) := by
  have hcan : N^(-(1/3:ℝ))*N^(1/3:ℝ)=1 := by
    rw [← Real.rpow_add hN]
    norm_num
  have h : ‖(N^(-(1/3:ℝ))) • v‖ ≤ C*m^(1-1/p) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hN.le _)]
    have hh := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hN.le (-(1/3:ℝ)))
    calc
      _ ≤ N^(-(1/3:ℝ))*(C*N^(1/3:ℝ)*m^(1-1/p)) := hh
      _ = (N^(-(1/3:ℝ))*N^(1/3:ℝ))*(C*m^(1-1/p)) := by ring
      _ = _ := by rw [hcan, one_mul]
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ C*m^(1-1/p))).2 h
  have he : (m^(1-1/p))^2 = m^(2-2/p) := by
    rw [← Real.rpow_mul_natCast hm]
    congr 1
    norm_num
    ring
  simpa only [mul_pow, he] using hh

lemma normalize_spatial_energy {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (v : V) {N r C m : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hb : ‖v‖^2 ≤ C*(N*r)^(2/3:ℝ)*m) :
    ‖(N^(-(1/3:ℝ))) • v‖^2 ≤ C*r^(2/3:ℝ)*m := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hN.le _), mul_pow]
  have hcan : (N^(-(1/3:ℝ)))^2*N^(2/3:ℝ)=1 := by
    rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_add hN]
    norm_num
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg (N^(-(1/3:ℝ))))
  apply hh.trans_eq
  rw [Real.mul_rpow hN.le hr.le]
  calc
    _ = ((N^(-(1/3:ℝ)))^2*N^(2/3:ℝ))*(C*r^(2/3:ℝ)*m) := by ring
    _ = _ := by rw [hcan, one_mul]

lemma graph_interpolated_bound_of_shortTime {c₀ C₀ p : ℝ} (hp : 2 < p) (hC₀ : 0 < C₀)
    (hshort : ShortTimeWeakEstimate c₀ C₀ p)
    (χ : Plane → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hann : ∀ ξ ∈ tsupport χ, c₀ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀)
    (B : ℝ) (hB : 0 ≤ B) (hχB : ∀ ξ, ‖χ ξ‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ j k : ℕ, k ≤ j →
      ∀ (x₀ : Plane) (t₀ s : ℝ), 0 ≤ s → s ≤ (1/2:ℝ)^(j+k) →
      ∀ (E : Set Plane), MeasurableSet E → E ⊆ Metric.ball x₀ 1 →
      ∀ (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
      (hb : ∀ x, ‖w x‖ ≤ 1), (∀ x ∈ E, T x ∈ Icc t₀ (t₀+s)) →
      ∀ [IsFiniteMeasure (volume.restrict E)],
      ‖(((2:ℝ)^j)^(-(1/3:ℝ))) •
          graphLp (fun ξ => χ (((2:ℝ)^j)⁻¹ • ξ))
            (scaled_cutoff_memLp χ hχ.continuous hc (by positivity))
            (volume.restrict E) T w hT hw hb‖^2 ≤
        C*((((2:ℝ)^(-(1/6:ℝ)))^k)^2)*(volume.real E)^(3/2-1/p) := by
  obtain ⟨Cm,hCm,hmass⟩ := graph_mass_bound_of_shortTime (by linarith : 1 < p) hshort
  obtain ⟨Cs,hCs,hsp⟩ := graph_spatial_bound_of_shortTime hp hC₀ hshort χ hχ hc hann B hB hχB
  refine ⟨(Cm*B)^2+Cs, by positivity, ?_⟩
  intro j k hk x₀ t₀ s hs hs' E hE hEB T w hT hw hb hTs inst
  let N : ℝ := (2:ℝ)^j
  let r : ℝ := ((2:ℝ)^k)⁻¹
  have hN : 0 < N := by positivity
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hs1 : s ≤ N⁻¹ := by
    have hw := hs'.trans_eq (dyadic_width j k)
    exact hw.trans (by dsimp only [N,r] at *; exact div_le_iff₀ hN |>.2 (by simpa using hr1))
  have hs2 : s ≤ r/N := hs'.trans_eq (dyadic_width j k)
  let χN : Plane → ℂ := fun ξ => χ (N⁻¹ • ξ)
  have hχN := scaled_cutoff_memLp χ hχ.continuous hc hN
  have χNm : Measurable χN := (hχ.continuous.comp (continuous_const_smul _)).measurable
  let v := graphLp χN hχN (volume.restrict E) T w hT hw hb
  have hm : 0 ≤ volume.real E := measureReal_nonneg
  have hm1 := hmass j χN χNm hχN B hB (fun ξ => hχB _) (ae_of_all _ (scaled_cutoff_annular hN hann))
    x₀ t₀ s hs hs1 E hE hEB T w hT hw hb hTs
  have h1 : ‖(N^(-(1/3:ℝ))) • v‖^2 ≤ (Cm*B)^2*(volume.real E)^(2-2/p) :=
    normalize_mass_energy v hN (mul_nonneg hCm.le hB) hm hm1
  have hsp1 := hsp (j-k) N r hN hr (dyadic_scale j k hk) x₀ t₀ s hs hs2
    E hE hEB T w hT hw hb hTs
  have hsp2 : ‖v‖^2 ≤ Cs*(N*r)^(2/3:ℝ)*volume.real E := by
    simpa only [v, ← dyadic_scale j k hk] using hsp1
  have h2 := normalize_spatial_energy v hN hr hsp2
  have hh := interpolate_energy (sq_nonneg _) hm hr (sq_nonneg (Cm*B)) hCs.le hp h1 h2
  change _ ≤ ((Cm*B)^2+Cs)*r^(1/3:ℝ)*(volume.real E)^(3/2-1/p) at hh
  simpa only [r, dyadic_decay] using hh

end PlanarEndpoint
end

end OAI
