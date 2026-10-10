import OAI.Probability.InvariantIsing.Fields.FieldGaussianFamilyGenerator

namespace OAI

/-! The affine-variance generator needs no separate uniform-growth
hypothesis: the bounded spatial derivative and joint differentiability
produce it on a neighborhood of each positive-variance point. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology NNReal

namespace InvariantIsing

theorem field_gaussianFamily_local_hasFDerivAt
    {U T X XX : ℝ × ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hU : Measurable U) (hT : Measurable T) (hX : Measurable X) (hXX : Measurable XX)
    {CT CX CXX : ℝ} (hCT : ∀ q, q.1 ∈ I → |T q| ≤ CT)
    (hCX : ∀ q, |X q| ≤ CX) (hCXX : ∀ q, |XX q| ≤ CXX)
    (hd : ∀ q, q.1 ∈ I → HasFDerivAt U (pairLinear (T q) (X q)) q)
    (dx : ∀ t y, HasDerivAt (fun z => U (t, z)) (X (t, y)) y)
    (dxx : ∀ t y, HasDerivAt (fun z => X (t, z)) (XX (t, y)) y)
    (a v ζ : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I) (hv : 0 < a + v * p.1) :
    HasFDerivAt
      (fun q : ℝ × ℝ => gaussianTransform (a + v * q.1) ζ (fun y => U (q.1, y)) q.2)
      (pairLinear
        (gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y)) (fun y => T (p.1, y)) p.2 +
          v / 2 * gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y))
            (fun y => XX (p.1, y) + ζ * (X (p.1, y)) ^ 2) p.2)
        (gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y)) (fun y => X (p.1, y)) p.2)) p := by
  have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX (0, 0))
  have hpair : ContinuousAt (fun t : ℝ => (t, (0 : ℝ))) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hc : ContinuousAt (fun t => U (t, 0)) p.1 :=
    ContinuousAt.comp (f := fun t : ℝ => (t, (0 : ℝ))) (x := p.1)
      (hd (p.1, 0) hp).continuousAt hpair
  have hg := field_parameter_growth_eventually hCX0 hCX dx hc
  have hvcont : ContinuousAt (fun t : ℝ => a + v * t) p.1 := by fun_prop
  have hvset : {t : ℝ | (a + v * p.1) / 2 < a + v * t ∧
      a + v * t < a + v * p.1 + 1} ∈ 𝓝 p.1 :=
    hvcont (Ioo_mem_nhds (by linarith) (by linarith))
  have hset : {t : ℝ | t ∈ I ∧
      (∀ y, |U (t, y)| ≤ |U (p.1, 0)| + 1 + CX * |y|) ∧
      (a + v * p.1) / 2 < a + v * t ∧ a + v * t < a + v * p.1 + 1} ∈ 𝓝 p.1 := by
    filter_upwards [hI.mem_nhds hp, hg, hvset] with t ht hgt hvt
    exact ⟨ht, hgt, hvt⟩
  obtain ⟨J, hJsub, hJopen, hpJ⟩ := mem_nhds_iff.mp hset
  exact field_gaussianFamily_hasFDerivAt hJopen hU hT hX hXX
    (K := |U (p.1, 0)| + 1) (L := CX) (by positivity) hCX0
    (fun q hq => (hJsub hq).2.1 q.2)
    (fun q hq => hCT q (hJsub hq).1) hCX hCXX
    (fun q hq => hd q (hJsub hq).1) dx dxx a v ζ
    (m := (a + v * p.1) / 2) (V := a + v * p.1 + 1) (by positivity)
    (fun t ht => (hJsub ht).2.2.1.le)
    (fun t ht => (hJsub ht).2.2.2.le) hpJ

end InvariantIsing

end

end OAI
