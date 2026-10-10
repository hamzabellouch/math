import OAI.Probability.InvariantIsing.Fields.FieldSecondBounds
import OAI.Probability.InvariantIsing.Fields.FieldGaussianPairDerivative

namespace OAI

/-! Applying the quadratic-envelope differentiation theorem to the
actual affine Gaussian shift of a finite scalar-field family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing
namespace FieldSmoothFamily

variable {I : Set ℝ} (F : FieldSmoothFamily I)

def affineShift (a v : ℝ) (p : ℝ × ℝ) (u : ℝ) : ℝ :=
  F.U (p.1, p.2 + Real.sqrt (a + v * p.1) * u)

def affineDifferential (a v : ℝ) (p : ℝ × ℝ) (u : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  pairLinear
    (F.T (p.1, p.2 + Real.sqrt (a + v * p.1) * u) +
      F.X (p.1, p.2 + Real.sqrt (a + v * p.1) * u) *
        (fieldAmplitudeSlope a v p.1 * u))
    (F.X (p.1, p.2 + Real.sqrt (a + v * p.1) * u))

lemma affine_average_hasFDerivAt (hI : IsOpen I)
    (A : (ℝ × ℝ) → ℝ → ℝ)
    (DA : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    (a v ζ : ℝ) {m V : ℝ} (hm : 0 < m)
    (hlo : ∀ t ∈ I, m ≤ a + v * t) (hhi : ∀ t ∈ I, a + v * t ≤ V)
    {CA CE : ℝ} (hCA : 0 ≤ CA) (hCE : 0 ≤ CE)
    (hA : ∀ q, Measurable (A q))
    (hDA : ∀ q, AEStronglyMeasurable (DA q) (gaussianReal 0 1))
    (hAb : ∀ q, q.1 ∈ I → ∀ u, |A q u| ≤ CA * (1 + |u|))
    (hEb : ∀ q, q.1 ∈ I → ∀ u, ‖DA q u‖ ≤ CE * (1 + |u|) ^ 2)
    (dA : ∀ q, q.1 ∈ I → ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt (fun q => ∫ u, A q u
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v q u))
      ((∫ u, DA p u + (ζ * A p u) • F.affineDifferential a v p u
          ∂(gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v p u)) -
        (∫ u, A p u
          ∂(gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v p u)) •
          (∫ u, ζ • F.affineDifferential a v p u
            ∂(gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v p u))) p := by
  let R := |v| / (2 * Real.sqrt m)
  let CD := F.KT + F.KX * R + F.KX
  let K := |F.U (p.1, 0)| + 1
  let C := |ζ| * (K + F.KX * (|p.2| + 1))
  let L := |ζ| * F.KX * Real.sqrt V
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hX := F.kx_nonneg
  have hT : 0 ≤ F.KT := (abs_nonneg _).trans (F.bT (p.1, 0) hp)
  have hCD : 0 ≤ CD := by dsimp only [CD]; positivity
  have hpair : ContinuousAt (fun t : ℝ => (t, (0 : ℝ))) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hc : ContinuousAt (fun t => F.U (t, 0)) p.1 :=
    ContinuousAt.comp (f := fun t : ℝ => (t, (0 : ℝ))) (x := p.1)
      (F.derivative (p.1, 0) hp).continuousAt hpair
  have hg := field_parameter_growth_eventually hX F.bX F.spatial hc
  have hset : {t : ℝ | t ∈ I ∧ ∀ y,
      |F.U (t, y)| ≤ K + F.KX * |y|} ∈ 𝓝 p.1 := by
    filter_upwards [hI.mem_nhds hp, hg] with t ht hgt
    exact ⟨ht, hgt⟩
  obtain ⟨J, hJsub, hJopen, hpJ⟩ := mem_nhds_iff.mp hset
  let S : Set (ℝ × ℝ) := (Prod.fst ⁻¹' J) ∩
    (Prod.snd ⁻¹' Ioo (p.2 - 1) (p.2 + 1))
  have hS : S ∈ 𝓝 p :=
    Filter.inter_mem ((hJopen.preimage continuous_fst).mem_nhds hpJ)
      ((isOpen_Ioo.preimage continuous_snd).mem_nhds ⟨by linarith, by linarith⟩)
  have hpS : p ∈ S := ⟨hpJ, by constructor <;> linarith⟩
  apply field_gaussianPair_hasFDerivAt (F.affineShift a v) A
    (F.affineDifferential a v) DA hS hpS ζ C L CA CD CE hCA hCD hCE
    (fun q => F.mU.comp (by fun_prop)) hA
    ((measurable_pairLinear
      ((F.mT.comp (by fun_prop)).add ((F.mX.comp (by fun_prop)).mul (by
        dsimp only [fieldAmplitudeSlope]
        fun_prop))) (F.mX.comp (by fun_prop))).aestronglyMeasurable)
    (hDA p)
  · intro q hq u
    have hqI := (hJsub hq.1).1
    have hq2 : |q.2| ≤ |p.2| + 1 := by
      have hh : |q.2 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
      calc
        |q.2| = |q.2 - p.2 + p.2| := by congr 1; ring
        _ ≤ |q.2 - p.2| + |p.2| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hshift : |q.2 + Real.sqrt (a + v * q.1) * u| ≤
        |p.2| + 1 + Real.sqrt V * |u| := by
      calc
        _ ≤ |q.2| + |Real.sqrt (a + v * q.1) * u| := abs_add_le _ _
        _ = |q.2| + Real.sqrt (a + v * q.1) * |u| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ _ := add_le_add hq2
          (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hhi q.1 hqI)) (abs_nonneg _))
    apply Real.exp_le_exp.mpr
    calc
      ζ * F.affineShift a v q u ≤ |ζ| * |F.affineShift a v q u| := by
        simpa only [abs_mul] using le_abs_self (ζ * F.affineShift a v q u)
      _ ≤ |ζ| * (K + F.KX * |q.2 + Real.sqrt (a + v * q.1) * u|) :=
        mul_le_mul_of_nonneg_left ((hJsub hq.1).2 _) (abs_nonneg _)
      _ ≤ |ζ| * (K + F.KX * (|p.2| + 1 + Real.sqrt V * |u|)) := by gcongr
      _ = C + L * |u| := by dsimp only [C, L]; ring
  · intro q hq u
    exact hAb q (hJsub hq.1).1 u
  · intro q hq u
    have hqI := (hJsub hq.1).1
    have hc : |fieldAmplitudeSlope a v q.1| ≤ R := abs_div_two_sqrt_le hm (hlo q.1 hqI) v
    unfold affineDifferential
    refine (norm_pairLinear_le _ _).trans ?_
    calc
      _ ≤ F.KT + F.KX * (R * |u|) + F.KX := by
        refine add_le_add ((abs_add_le _ _).trans (add_le_add (F.bT _ hqI) ?_)) (F.bX _)
        rw [abs_mul, abs_mul]
        gcongr
        exact F.bX _
      _ ≤ CD * (1 + |u|) := by
        dsimp only [CD]
        nlinarith [mul_nonneg hT (abs_nonneg u), mul_nonneg hX (abs_nonneg u)]
  · intro q hq u
    exact hEb q (hJsub hq.1).1 u
  · intro q hq u
    exact affine_gaussian_shift_hasFDerivAt F.derivative a v u (hJsub hq.1).1
      (hm.trans_le (hlo q.1 (hJsub hq.1).1))
  · intro q hq u
    exact dA q (hJsub hq.1).1 u

end FieldSmoothFamily
end InvariantIsing

end

end OAI
