import OAI.Probability.InvariantIsing.Fields.FieldGaussianFamilyEnvelope
import OAI.Probability.InvariantIsing.Fields.FieldParameterGrowth

namespace OAI

/-! The raw two-coordinate derivative for a scalar Gaussian recursion
with affine variance and a locally uniformly linearly growing payoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology NNReal

namespace InvariantIsing

theorem field_gaussianFamily_raw_hasFDerivAt
    {U T X : ℝ × ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hU : Measurable U) (hT : Measurable T) (hX : Measurable X)
    {K L CT CX : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hg : ∀ q, q.1 ∈ I → |U q| ≤ K + L * |q.2|)
    (hCT : ∀ q, q.1 ∈ I → |T q| ≤ CT) (hCX : ∀ q, |X q| ≤ CX)
    (hd : ∀ q, q.1 ∈ I → HasFDerivAt U (pairLinear (T q) (X q)) q)
    (a v ζ : ℝ) {m V : ℝ} (hm : 0 < m)
    (hlo : ∀ t ∈ I, m ≤ a + v * t) (hhi : ∀ t ∈ I, a + v * t ≤ V)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt
      (fun q : ℝ × ℝ => gaussianTransform (a + v * q.1) ζ (fun y => U (q.1, y)) q.2)
      (∫ z, pairLinear (T (p.1, p.2 + Real.sqrt (a + v * p.1) * z) +
          X (p.1, p.2 + Real.sqrt (a + v * p.1) * z) *
            (v / (2 * Real.sqrt (a + v * p.1)) * z))
        (X (p.1, p.2 + Real.sqrt (a + v * p.1) * z))
        ∂(gaussianReal 0 1).tilted
          (fun z => ζ * U (p.1, p.2 + Real.sqrt (a + v * p.1) * z))) p := by
  let S : Set (ℝ × ℝ) := (Prod.fst ⁻¹' I) ∩
    (Prod.snd ⁻¹' Ioo (p.2 - 1) (p.2 + 1))
  let R := |v| / (2 * Real.sqrt m)
  let F := fun z : ℝ => K + L * (|p.2| + 1 + Real.sqrt V * |z|)
  let B := fun z : ℝ => CT + CX * (R * |z|) + CX
  let E := fun z : ℝ => Real.exp (|ζ| * F z)
  have hCX0 : 0 ≤ CX := (abs_nonneg _).trans (hCX (0, 0))
  have hCT0 : 0 ≤ CT := (abs_nonneg _).trans (hCT (p.1, 0) hp)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hS : S ∈ 𝓝 p :=
    Filter.inter_mem ((hI.preimage continuous_fst).mem_nhds hp)
      ((isOpen_Ioo.preimage continuous_snd).mem_nhds ⟨by linarith, by linarith⟩)
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have hB : Measurable B := by dsimp only [B]; fun_prop
  have hFg : HasLinearGrowth F := by
    refine ⟨K + L * (|p.2| + 1), L * Real.sqrt V, by positivity, by positivity, fun z => ?_⟩
    dsimp only [F]
    rw [abs_of_nonneg (by positivity), Real.norm_eq_abs]
    exact le_of_eq (by ring)
  have hBg : HasLinearGrowth B := by
    refine ⟨CT + CX, CX * R, by positivity, by positivity, fun z => ?_⟩
    dsimp only [B]
    rw [abs_of_nonneg (by positivity), Real.norm_eq_abs]
    exact le_of_eq (by ring)
  have hEB : Integrable (fun z => E z * B z) (gaussianReal 0 1) :=
    field_exp_mul_linear_integrable 1 0 |ζ| hF hFg hB hBg
  have hBi : Integrable B (gaussianReal 0 1) := field_gaussian_linear_integrable 1 0 hB hBg
  have hbase : HasLinearGrowth (fun z => U (p.1, p.2 + Real.sqrt (a + v * p.1) * z)) := by
    refine ⟨K + L * |p.2|, L * Real.sqrt (a + v * p.1), by positivity, by positivity, fun z => ?_⟩
    calc
      _ ≤ K + L * |p.2 + Real.sqrt (a + v * p.1) * z| :=
        hg (p.1, p.2 + Real.sqrt (a + v * p.1) * z) hp
      _ ≤ K + L * (|p.2| + Real.sqrt (a + v * p.1) * |z|) := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ hL
        calc
          _ ≤ |p.2| + |Real.sqrt (a + v * p.1) * z| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = _ := by rw [Real.norm_eq_abs]; ring
  have hbaseM : Measurable (fun z => U (p.1, p.2 + Real.sqrt (a + v * p.1) * z)) := by
    exact hU.comp (by fun_prop)
  have hi := field_gaussian_linear_integrable 1 0 hbaseM hbase
  have hexp := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hbaseM hbase ζ
  apply field_average_hasFDerivAt_of_envelope (gaussianReal 0 1)
    (U := fun q z => U (q.1, q.2 + Real.sqrt (a + v * q.1) * z))
    (D := fun q z => pairLinear (T (q.1, q.2 + Real.sqrt (a + v * q.1) * z) +
      X (q.1, q.2 + Real.sqrt (a + v * q.1) * z) *
        (v / (2 * Real.sqrt (a + v * q.1)) * z))
      (X (q.1, q.2 + Real.sqrt (a + v * q.1) * z)))
    hS (fun q => hU.comp (by fun_prop))
    ((measurable_pairLinear ((hT.comp (by fun_prop)).add
      ((hX.comp (by fun_prop)).mul (by fun_prop))) (hX.comp (by fun_prop))).aestronglyMeasurable)
    hi ζ hexp B E hBi hEB
  · intro q hq z
    refine (norm_pairLinear_le _ _).trans (add_le_add ?_ (hCX _))
    refine (abs_add_le _ _).trans (add_le_add (hCT _ hq.1) ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (hCX _)
      (mul_le_mul_of_nonneg_right (abs_div_two_sqrt_le hm (hlo q.1 hq.1) v) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCX0
  · intro q hq z
    apply Real.exp_le_exp.mpr
    have hq2 : |q.2| ≤ |p.2| + 1 := by
      have hdiff : |q.2 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
      calc
        _ = |q.2 - p.2 + p.2| := by congr 1; ring
        _ ≤ |q.2 - p.2| + |p.2| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hroot := Real.sqrt_le_sqrt (hhi q.1 hq.1)
    have hshift : |q.2 + Real.sqrt (a + v * q.1) * z| ≤
        |p.2| + 1 + Real.sqrt V * |z| := by
      calc
        _ ≤ |q.2| + |Real.sqrt (a + v * q.1) * z| := abs_add_le _ _
        _ = |q.2| + Real.sqrt (a + v * q.1) * |z| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ _ := add_le_add hq2 (mul_le_mul_of_nonneg_right hroot (abs_nonneg z))
    calc
      ζ * U (q.1, q.2 + Real.sqrt (a + v * q.1) * z) ≤
          |ζ| * |U (q.1, q.2 + Real.sqrt (a + v * q.1) * z)| := by
        simpa only [abs_mul] using le_abs_self (ζ * U (q.1, q.2 + Real.sqrt (a + v * q.1) * z))
      _ ≤ |ζ| * F z := mul_le_mul_of_nonneg_left
        ((hg (q.1, q.2 + Real.sqrt (a + v * q.1) * z) hq.1).trans
          (add_le_add_right (mul_le_mul_of_nonneg_left hshift hL) K))
        (abs_nonneg ζ)
  · intro q hq z
    exact affine_gaussian_shift_hasFDerivAt hd a v z hq.1
      (hm.trans_le (hlo q.1 hq.1))

end InvariantIsing

end

end OAI
