import OAI.Probability.InvariantIsing.Fields.FieldGaussianFamilyRaw

namespace OAI

/-! The Gaussian generator with a varying, linearly growing scalar
payoff. This is the covariance derivative used in the finite field chain. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology NNReal

namespace InvariantIsing

theorem field_gaussianFamily_hasFDerivAt
    {U T X XX : ℝ × ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hU : Measurable U) (hT : Measurable T) (hX : Measurable X) (hXX : Measurable XX)
    {K L CT CX CXX : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hg : ∀ q, q.1 ∈ I → |U q| ≤ K + L * |q.2|)
    (hCT : ∀ q, q.1 ∈ I → |T q| ≤ CT) (hCX : ∀ q, |X q| ≤ CX)
    (hCXX : ∀ q, |XX q| ≤ CXX)
    (hd : ∀ q, q.1 ∈ I → HasFDerivAt U (pairLinear (T q) (X q)) q)
    (dx : ∀ t y, HasDerivAt (fun z => U (t, z)) (X (t, y)) y)
    (dxx : ∀ t y, HasDerivAt (fun z => X (t, z)) (XX (t, y)) y)
    (a v ζ : ℝ) {m V : ℝ} (hm : 0 < m)
    (hlo : ∀ t ∈ I, m ≤ a + v * t) (hhi : ∀ t ∈ I, a + v * t ≤ V)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt
      (fun q : ℝ × ℝ => gaussianTransform (a + v * q.1) ζ (fun y => U (q.1, y)) q.2)
      (pairLinear
        (gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y)) (fun y => T (p.1, y)) p.2 +
          v / 2 * gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y))
            (fun y => XX (p.1, y) + ζ * (X (p.1, y)) ^ 2) p.2)
        (gaussianTiltAverage (a + v * p.1) ζ (fun y => U (p.1, y)) (fun y => X (p.1, y)) p.2)) p := by
  let r := Real.sqrt (a + v * p.1)
  let F := fun y => U (p.1, y)
  let ν := (gaussianReal 0 1).tilted (fun z => ζ * F (p.2 + r * z))
  have hFm : Measurable F := hU.comp (by fun_prop)
  have hFg : HasLinearGrowth F := ⟨K, L, hK, hL, fun y => by
    simpa only [F, Real.norm_eq_abs] using hg (p.1, y) hp⟩
  have hshift : Measurable (fun z => F (p.2 + r * z)) := hFm.comp (by fun_prop)
  have hshiftG : HasLinearGrowth (fun z => F (p.2 + r * z)) :=
    (hFg.add_left p.2).scale_argument r
  have hExp := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hshift hshiftG ζ
  have : IsProbabilityMeasure ν := MeasureTheory.isProbabilityMeasure_tilted hExp
  have hT0 : Measurable (fun z => T (p.1, p.2 + r * z)) := hT.comp (by fun_prop)
  have hX0 : Measurable (fun z => X (p.1, p.2 + r * z)) := hX.comp (by fun_prop)
  have hiT : Integrable (fun z => T (p.1, p.2 + r * z)) ν :=
    Integrable.of_bound hT0.aestronglyMeasurable CT
      (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs] using hCT (p.1, p.2 + r * z) hp)
  have hiX : Integrable (fun z => X (p.1, p.2 + r * z)) ν :=
    Integrable.of_bound hX0.aestronglyMeasurable CX
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hCX _)
  have hZXg : HasLinearGrowth (fun z => z * X (p.1, p.2 + r * z)) := by
    refine ⟨0, |CX|, le_rfl, abs_nonneg _, fun z => ?_⟩
    rw [abs_mul, Real.norm_eq_abs, zero_add]
    calc
      _ ≤ |z| * |CX| := mul_le_mul_of_nonneg_left ((hCX _).trans (le_abs_self CX)) (abs_nonneg z)
      _ = _ := mul_comm _ _
  have hiZX : Integrable (fun z => z * X (p.1, p.2 + r * z)) ν := by
    apply (integrable_tilted_iff hExp _).mpr
    exact field_exp_mul_linear_integrable 1 0 ζ hshift hshiftG (measurable_id.mul hX0) hZXg
  have hefun : (fun z => T (p.1, p.2 + r * z) + X (p.1, p.2 + r * z) * (v / (2 * r) * z)) =
      fun z => T (p.1, p.2 + r * z) + (v / (2 * r)) * (z * X (p.1, p.2 + r * z)) := by
    funext z
    ring
  have hiA : Integrable
      (fun z => T (p.1, p.2 + r * z) + X (p.1, p.2 + r * z) * (v / (2 * r) * z)) ν := by
    rw [hefun]
    exact hiT.add (hiZX.const_mul _)
  have hraw := field_gaussianFamily_raw_hasFDerivAt hI hU hT hX hK hL hg hCT hCX hd
    a v ζ hm hlo hhi hp
  change HasFDerivAt _
    (∫ z, pairLinear (T (p.1, p.2 + r * z) + X (p.1, p.2 + r * z) * (v / (2 * r) * z))
      (X (p.1, p.2 + r * z)) ∂ν) p at hraw
  rw [integral_pairLinear ν hiA hiX] at hraw
  have he : (∫ z, T (p.1, p.2 + r * z) + X (p.1, p.2 + r * z) * (v / (2 * r) * z) ∂ν) =
      (∫ z, T (p.1, p.2 + r * z) ∂ν) +
        v / 2 * (∫ z, XX (p.1, p.2 + r * z) + ζ * (X (p.1, p.2 + r * z)) ^ 2 ∂ν) := by
    rw [hefun, integral_add hiT (hiZX.const_mul _), integral_const_mul]
    have hibp := field_gaussian_tilted_ibp hFm hFg
      (hX.comp (by fun_prop)) (hXX.comp (by fun_prop))
      (fun y => hCX (p.1, y)) (fun y => hCXX (p.1, y)) (dx p.1) (dxx p.1) r ζ p.2
    change (∫ z, z * X (p.1, p.2 + r * z) ∂ν) =
      r * (∫ z, XX (p.1, p.2 + r * z) + ζ * (X (p.1, p.2 + r * z)) ^ 2 ∂ν) at hibp
    rw [hibp]
    have hr : r ≠ 0 := (Real.sqrt_pos.mpr (hm.trans_le (hlo _ hp))).ne'
    field_simp [hr]
  rw [he] at hraw
  exact hraw

end InvariantIsing

end

end OAI
