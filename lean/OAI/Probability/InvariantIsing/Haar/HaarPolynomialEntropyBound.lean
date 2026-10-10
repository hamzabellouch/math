import OAI.Probability.InvariantIsing.Haar.HaarHeatFisherBound

namespace OAI

/-! The entropy inequality for positive polynomials with bounded logarithmic gradient. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem haarPolynomial_entropy_bound {N d : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : haarPolynomialSpace N d) (ε C : ℝ) (hε : 0 < ε)
    (hp : ∀ U : SpecialOrthogonal N, ε ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    (hC : ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤
        C*(haarPolynomialValue (p : MatrixPolynomial N) U)^2) :
    (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U*
      Real.log (haarPolynomialValue (p : MatrixPolynomial N) U) ∂μ)-
      (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ)*
        Real.log (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ) ≤
    C*(∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ)/(2*((N:ℝ)-2)) := by
  let ρ := (N:ℝ)-2
  let m := ∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ
  let k := m*C/(2*ρ)
  let I (t : ℝ) := ∫ U, haarPolynomialValue (haarPolynomialGamma
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U/
    haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∂μ
  let J (t : ℝ) := haarHeatEntropy μ p t-k*Real.exp (-2*ρ*t)
  have hρ : 0 < ρ := by
    have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
    dsimp only [ρ]
    linarith
  have hkc : k*(2*ρ)=m*C := by
    dsimp only [k]
    field_simp
  have hD (t : ℝ) (ht : 0 < t) :
      HasDerivAt J (-I t+m*C*Real.exp (-2*ρ*t)) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (-2*ρ*s))
        (-2*ρ*Real.exp (-2*ρ*t)) t := by
      convert ((hasDerivAt_id t).const_mul (-2*ρ)).exp using 1
      all_goals simp only [id_eq]
      all_goals ring
    have hd := (haarHeatEntropy_hasDerivAt μ p ε hε hp ht).sub (he.const_mul k)
    convert hd using 1
    change -I t+m*C*Real.exp (-2*ρ*t) = -I t-k*(-2*ρ*Real.exp (-2*ρ*t))
    rw [← hkc]
    ring
  have hnon (t : ℝ) (ht : 0 < t) : 0 ≤ -I t+m*C*Real.exp (-2*ρ*t) := by
    have hb := haarHeat_fisher_bound μ p ε C hε hp hC ht.le
    change I t ≤ C*Real.exp (-2*ρ*t)*m at hb
    nlinarith
  have hcont : ContinuousOn J (Ici 0) :=
    (continuousOn_haarPolynomialHeat_test_integral μ p (fun x => x*Real.log x)
      Real.continuous_mul_log).sub
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn)
  have hmono : MonotoneOn J (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont
      (f' := fun t => -I t+m*C*Real.exp (-2*ρ*t))
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
      exact (hD t ht').hasDerivWithinAt
    · intro t ht
      exact hnon t (by simpa only [interior_Ici,mem_Ioi] using ht)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-2*ρ*t)) atTop (𝓝 0) := by
    have he := (tendsto_haar_gradient_envelope hN 1).comp
      (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
    convert he using 1
    funext t
    simp only [one_mul,Function.comp_def,id_eq]
    congr 1
    dsimp only [ρ]
    ring
  have hE : Tendsto (haarHeatEntropy μ p) atTop (𝓝 (m*Real.log m)) :=
    haarPolynomialHeat_test_tendsto_mean hN μ p (fun x => x*Real.log x) Real.continuous_mul_log
  have hJ : Tendsto J atTop (𝓝 (m*Real.log m)) := by
    simpa only [mul_zero,sub_zero] using hE.sub (hexp.const_mul k)
  have h0 : J 0 ≤ m*Real.log m := ge_of_tendsto hJ (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact hmono (by simp) ht ht)
  have hz : J 0 = (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U*
      Real.log (haarPolynomialValue (p : MatrixPolynomial N) U) ∂μ)-k := by
    simp only [J,haarHeatEntropy,haarPolynomialHeat_zero,mul_zero,Real.exp_zero,mul_one]
  rw [hz] at h0
  change _-m*Real.log m ≤ C*m/(2*ρ)
  dsimp only [k] at h0
  linear_combination h0

end InvariantIsing

end

end OAI
