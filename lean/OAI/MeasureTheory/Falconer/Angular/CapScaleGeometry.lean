import OAI.MeasureTheory.Falconer.Estimates.NonstationaryPower

namespace OAI

/-!
# The cap and cell replacement error at the graph scales

The geometric constant is explicit. The fixed gap between `10σ` and `30σ`
makes the point-replacement and cap-replacement errors less than half the
failed-test threshold once the displayed power inequality holds.
-/

namespace Falconer

theorem graph_cap_replacement_scale {R σ C a p δ : ℝ}
    (hR : 1 ≤ R) (hσ : 0 ≤ σ) (hC : 0 ≤ C) (_hδ : 0 ≤ δ)
    (hcap : δ ≤ R^(a-p+10*σ)) :
    2*C*R^(-p)+8*δ*(C*R^(-a)) ≤ 10*C*R^(-p+10*σ) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hfirst : R^(-p) ≤ R^(-p+10*σ) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hsecond : δ*R^(-a) ≤ R^(-p+10*σ) := by
    apply (mul_le_mul_of_nonneg_right hcap (by positivity)).trans_eq
    rw [← Real.rpow_add hR0]
    congr 1
    ring
  have h₁ := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 2*C by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 8*C by positivity)
  nlinarith

theorem graph_cap_replacement_small {R σ C a p δ : ℝ}
    (hR : 1 ≤ R) (hσ : 0 ≤ σ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hcap : δ ≤ R^(a-p+10*σ)) (hlarge : 20*C ≤ R^(20*σ)) :
    2*C*R^(-p)+8*δ*(C*R^(-a)) ≤ R^(-p+30*σ)/2 := by
  apply (graph_cap_replacement_scale hR hσ hC hδ hcap).trans
  have h := mul_le_mul_of_nonneg_right hlarge
    (show 0 ≤ R^(-p+10*σ) by positivity)
  have he : R^(20*σ)*R^(-p+10*σ) = R^(-p+30*σ) := by
    rw [← Real.rpow_add (zero_lt_one.trans_le hR)]
    congr 1
    ring
  rw [he] at h
  nlinarith

end Falconer

end OAI
