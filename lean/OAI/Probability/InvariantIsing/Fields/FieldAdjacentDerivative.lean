import OAI.Probability.InvariantIsing.Fields.FieldCompensatedTangent

namespace OAI

/-! The adjacent-variance cancellation for a single field height. Its
derivative is the negative conditional squared spin mean. This proves
the local identity underlying `fld:backward-derivative` directly from
the Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing.FieldSmoothFamily

theorem parameter_derivative {I : Set ℝ} (F : FieldSmoothFamily I)
    (t z : ℝ) (ht : t ∈ I) :
    HasDerivAt (fun s => F.U (s, z)) (F.T (t, z)) t := by
  have hmap : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  have hd := (F.derivative (t, z) ht).comp_hasDerivAt t hmap
  simpa [pairLinear, Function.comp_def] using hd

theorem negative_variance_compensation {I : Set ℝ} (F : FieldSmoothFamily I)
    (hI : IsOpen I) (b η : ℝ) (hv : ∀ t ∈ I, 0 < b - t)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) (hT : ∀ y, F.T (p.1, y) = 0) :
    (F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hv)).T p +
      (1 / 2 : ℝ) *
        ((F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hv)).XX p + η *
          ((F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hv)).X p) ^ 2) = 0 := by
  have hc := F.compensated_tangent b 0 1 η η hp
  have hz : (fun y => F.T (p.1, y) + (0 : ℝ) / 2 *
      (F.XX (p.1, y) + η * (F.X (p.1, y)) ^ 2)) = fun _ => 0 := by
    funext y
    simp only [hT y, zero_div, zero_mul, add_zero]
  have hm : Measurable (fun y => F.U (p.1, y)) := F.mU.comp (by fun_prop)
  rw [hz, field_gaussianTiltAverage_const _ _ hm (F.growth p.1)] at hc
  change F.tangent b (-1) η p + (1 / 2 : ℝ) *
    (F.curvature b (-1) η p + η * (F.mean b (-1) η p) ^ 2) = 0
  simpa only [sub_self, sub_zero, zero_sub, zero_div, zero_mul] using hc

theorem adjacent_tangent {I : Set ℝ} (F : FieldSmoothFamily I)
    (hI : IsOpen I) (a b ζ η : ℝ)
    (hplus : ∀ t ∈ I, 0 < a + t) (hminus : ∀ t ∈ I, 0 < b - t)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) (hT : ∀ y, F.T (p.1, y) = 0) :
    let G := F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hminus)
    let H := G.transform hI a 1 ζ (by simpa only [one_mul] using hplus)
    H.T p = -(η - ζ) / 2 * gaussianTiltAverage (a + p.1) ζ
      (fun y => G.U (p.1, y)) (fun y => (G.X (p.1, y)) ^ 2) p.2 := by
  let G := F.transform hI b (-1) η (by simpa only [neg_one_mul, sub_eq_add_neg] using hminus)
  change G.tangent a 1 ζ p = -(η - ζ) / 2 *
    gaussianTiltAverage (a + p.1) ζ (fun y => G.U (p.1, y))
      (fun y => (G.X (p.1, y)) ^ 2) p.2
  have hc := G.compensated_tangent a 1 0 ζ η hp
  have hz : (fun y => G.T (p.1, y) + (1 : ℝ) / 2 *
      (G.XX (p.1, y) + η * (G.X (p.1, y)) ^ 2)) = fun _ => 0 := by
    funext y
    exact F.negative_variance_compensation hI b η hminus hp hT
  have hm : Measurable (fun y => G.U (p.1, y)) := G.mU.comp (by fun_prop)
  rw [hz, field_gaussianTiltAverage_const _ _ hm (G.growth p.1)] at hc
  simp only [sub_zero, one_mul, zero_div, zero_mul, add_zero] at hc
  calc
    G.tangent a 1 ζ p = _ := hc
    _ = _ := by ring

end InvariantIsing.FieldSmoothFamily

end

end OAI
