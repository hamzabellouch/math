import OAI.MeasureTheory.Falconer.Geometry.ChartPairTransfer
import OAI.MeasureTheory.Falconer.Radial.RadialScaleWindow

namespace OAI

/-! # Power-small original pair sets stay power-small after Gaussian slicing -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

 theorem chart_pair_power (h : ℕ) {q c₀ : ℝ} (hq : (h:ℝ) < q) (hc₀ : 0 < c₀) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1) → ∀ E : Set (Space n × Space n), MeasurableSet E →
      (μ.prod μ) E ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c₀)) →
      (∀ x : Space n, ∀ j : ℕ, j ≤ N →
        μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*(1/(2:ℝ)^j)^q)) →
      (∫⁻ A : Fin h → Space (n+1), ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
        (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N))) E ∂gaussianRows (n+1) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨H₀,hH₀⟩ := exists_nat_gt (2*(h:ℝ)/c₀)
  let H := H₀+1
  have hH : 0 < H := by dsimp [H]; omega
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hfar : 0 < c₀-(h:ℝ)/(H:ℝ) := by
    have hh : 2*(h:ℝ)/c₀ < (H:ℝ) := by dsimp [H]; push_cast; linarith
    have hh' := (div_lt_iff₀ hc₀).mp hh
    apply sub_pos.mpr
    apply (div_lt_iff₀ hHr).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  let ε := (q-h)/(4*(H:ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hnear : 0 < (q-h)/(2*(H:ℝ))-ε := by
    have heq : (q-h)/(2*(H:ℝ)) = 2*ε := by dsimp [ε]; ring
    rw [heq]
    linarith
  let C := (4*gaussianPairBandConstant)^h
  let L := 1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))
  have hC : 0 ≤ C := by have := gaussianPairBandConstant_pos; dsimp [C]; positivity
  have hL : 0 ≤ L := by
    have hh : (2:ℝ)^((h:ℝ)-q) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    dsimp [L]
    positivity
  let c := min (c₀-(h:ℝ)/(H:ℝ)) ((q-h)/(2*(H:ℝ))-ε)/2
  have hc : 0 < c := half_pos (lt_min hfar hnear)
  have hcf : c < c₀-(h:ℝ)/(H:ℝ) := by dsimp [c]; have := min_le_left (c₀-(h:ℝ)/(H:ℝ)) ((q-h)/(2*(H:ℝ))-ε); linarith
  have hcn : c < (q-h)/(2*(H:ℝ))-ε := by dsimp [c]; have := min_le_right (c₀-(h:ℝ)/(H:ℝ)) ((q-h)/(2*(H:ℝ))-ε); linarith
  obtain ⟨Nc,hcost⟩ := weak_radial_two_costs hC (mul_nonneg hC hL) hcf hcn
  refine ⟨ε,c,hε,hc,2*H+Nc,?_⟩
  intro N hN μ _ hμ E hE hmass hball
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hf : ((2:ℝ)^(N/H))^(h:ℝ) ≤ R^((h:ℝ)/(H:ℝ)) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hdiv : ((N/H:ℕ):ℝ) ≤ (N:ℝ)/(H:ℝ) := by
      apply (le_div_iff₀ hHr).mpr
      exact_mod_cast Nat.div_mul_le_self N H
    have hh := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg (α := ℝ) h)
    convert hh using 1
    ring
  have hn := radial_scale_window_decay hH (by omega : 2*H ≤ N)
    (j := N/H) le_rfl (sub_pos.mpr hq).le
  have hn' : ((2:ℝ)^(N/H))^((h:ℝ)-q) ≤ R^(-((q-h)/(2*(H:ℝ)))) := by
    convert hn using 1
    ring_nf
  apply (chart_exceptional_pair_transfer μ hμ E hE (by positivity) hq (N/H) N
    (Nat.div_le_self N H) hball).trans
  apply (mul_le_mul' le_rfl (add_le_add
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hf) hmass)
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hn' (by positivity)) hL)))).trans
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = C*R^(-(c₀-(h:ℝ)/(H:ℝ)))+(C*L)*R^(-((q-h)/(2*(H:ℝ))-ε)) := by
      change C*(R^((h:ℝ)/(H:ℝ))*R^(-c₀)+
        R^ε*R^(-((q-h)/(2*(H:ℝ))))*L) = _
      have he₁ : R^((h:ℝ)/(H:ℝ))*R^(-c₀) = R^(-(c₀-(h:ℝ)/(H:ℝ))) := by
        rw [← Real.rpow_add hR]
        congr 1
        ring
      have he₂ : R^ε*R^(-((q-h)/(2*(H:ℝ)))) = R^(-((q-h)/(2*(H:ℝ))-ε)) := by
        rw [← Real.rpow_add hR]
        congr 1
        ring
      rw [he₁,he₂]
      ring
    _ ≤ _ := hcost N (by omega)

end Falconer

end OAI
