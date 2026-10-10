import OAI.Probability.InvariantIsing.Magnetic.MagneticImplicitBias

namespace OAI

/-! Local inverse-mean-coordinate calculus used by the prescribed-spin
field comparison. These identities derive the change of curvature and
the second derivative of a pulled-back field variation. -/

noncomputable section
open Filter IsingPerceptron
open scoped Topology

namespace InvariantIsing

lemma inverse_mean_curvature_variation {A C : ℝ × ℝ → ℝ}
    {b : ℝ → ℝ} {t s a c v d : ℝ}
    (hb : ContinuousAt b t) (hc : c ≠ 0)
    (hA : HasFDerivAt A (pairLinear a c) (t, b t))
    (he : ∀ᶠ q in 𝓝 t, A (q, b q) = s)
    (hC : HasFDerivAt C (pairLinear v d) (t, b t)) :
    HasDerivAt (fun q => C (q, b q)) (v - d * a / c) t := by
  have hdb := parametric_bias_hasDerivAt hb hc hA he
  have hd := hC.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hdb)
  convert hd using 1
  all_goals first | rfl | (simp only [pairLinear_apply]; ring)

lemma inverse_mean_pullback_derivative {V Z : ℝ → ℝ} {u c v : ℝ}
    (hZ : HasDerivAt Z (1 / c) u) (hV : HasDerivAt V v (Z u)) :
    HasDerivAt (fun q => V (Z q)) (v / c) u := by
  convert hV.comp u hZ using 1
  all_goals first | rfl | simp [div_eq_mul_inv]

/-- The spatial derivative of the first inverse-coordinate derivative.
This is the local formula behind `delta a = a^2 delta F_uu`. -/
lemma inverse_mean_pullback_quotient {Z V₁ C : ℝ → ℝ} {u c v v₂ d : ℝ}
    (hc : c ≠ 0) (hZ : HasDerivAt Z (1 / c) u)
    (hv : V₁ (Z u) = v) (hcv : C (Z u) = c)
    (hV : HasDerivAt V₁ v₂ (Z u)) (hC : HasDerivAt C d (Z u)) :
    HasDerivAt (fun q => V₁ (Z q) / C (Z q))
      (v₂ / c ^ 2 - v * d / c ^ 3) u := by
  have hn := inverse_mean_pullback_derivative hZ hV
  have hd := inverse_mean_pullback_derivative hZ hC
  have hq := hn.div hd (by rwa [hcv])
  convert hq using 1
  rw [hv, hcv]
  field_simp [hc]

lemma inverse_mean_pullback_second {Z V V₁ C : ℝ → ℝ} {u c v v₂ d : ℝ}
    (hc : c ≠ 0) (hZ : HasDerivAt Z (1 / c) u)
    (hv : V₁ (Z u) = v) (hcv : C (Z u) = c)
    (hV : HasDerivAt V₁ v₂ (Z u)) (hC : HasDerivAt C d (Z u))
    (hZloc : ∀ᶠ q in 𝓝 u, HasDerivAt Z (1 / C (Z q)) q)
    (hVloc : ∀ᶠ q in 𝓝 u, HasDerivAt V (V₁ (Z q)) (Z q)) :
    HasDerivAt (deriv (fun q => V (Z q)))
      (v₂ / c ^ 2 - v * d / c ^ 3) u := by
  apply (inverse_mean_pullback_quotient hc hZ hv hcv hV hC).congr_of_eventuallyEq
  filter_upwards [hZloc, hVloc] with q hZq hVq
  exact (inverse_mean_pullback_derivative hZq hVq).deriv

lemma inverse_mean_variation_identity {c v v₂ d : ℝ} (hc : c ≠ 0) :
    c ^ 2 * (v₂ / c ^ 2 - v * d / c ^ 3) = v₂ - d * v / c := by
  field_simp [hc]

end InvariantIsing

end

end OAI
