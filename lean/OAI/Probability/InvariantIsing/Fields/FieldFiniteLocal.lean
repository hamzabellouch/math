import OAI.Probability.InvariantIsing.Fields.FieldFiniteMoments

namespace OAI

/-! A local Gaussian domination envelope for the finite vector of field
heights. Its constants are uniform over a neighborhood of the height vector
and the spatial field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma local_envelope (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {V R : ℝ} (hR : 0 ≤ R)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    ∃ (S : Set (FieldCovariate n)) (C L CD : ℝ),
      S ∈ 𝓝 p ∧ p ∈ S ∧ (∀ q ∈ S, q.1 ∈ I) ∧ 0 ≤ CD ∧
      (∀ q ∈ S, ∀ u, Real.exp (ζ * F.affineShift a v q u) ≤ Real.exp (C + L * |u|)) ∧
      (∀ q ∈ S, ∀ u, ‖F.affineDifferential a v q u‖ ≤ CD * (1 + |u|)) := by
  have hX := F.kx_nonneg
  have hP := F.kp_nonneg
  let K := |F.U (p.1, 0)| + 1
  let C := |ζ| * (K + F.KX * (|p.2| + 1))
  let L := |ζ| * F.KX * Real.sqrt V
  let A := F.KP + F.KX * R
  let CD := (n : ℝ) * A + F.KX
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hCD : 0 ≤ CD := by dsimp only [CD]; positivity
  have hpair : ContinuousAt (fun t : Fin n → ℝ => (t, (0 : ℝ))) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hct : ContinuousAt (fun t : Fin n → ℝ => F.U (t, 0)) p.1 :=
    ContinuousAt.comp (f := fun t : Fin n → ℝ => (t, (0 : ℝ)))
      (x := p.1) (F.derivative (p.1, 0) hp).continuousAt hpair
  have he : ∀ᶠ t in 𝓝 p.1, |F.U (t, 0)| < K :=
    (tendsto_order.1 hct.abs).2 _ (lt_add_one _)
  have hset : {t : Fin n → ℝ | t ∈ I ∧ |F.U (t, 0)| < K} ∈ 𝓝 p.1 :=
    Filter.inter_mem (hI.mem_nhds hp) he
  obtain ⟨J, hJsub, hJopen, hpJ⟩ := mem_nhds_iff.mp hset
  let S : Set (FieldCovariate n) := (Prod.fst ⁻¹' J) ∩
    (Prod.snd ⁻¹' Ioo (p.2 - 1) (p.2 + 1))
  have hS : S ∈ 𝓝 p :=
    Filter.inter_mem ((hJopen.preimage continuous_fst).mem_nhds hpJ)
      ((isOpen_Ioo.preimage continuous_snd).mem_nhds ⟨by linarith, by linarith⟩)
  refine ⟨S, C, L, CD, hS, ⟨hpJ, by constructor <;> linarith⟩,
    (fun q hq => (hJsub hq.1).1), hCD, ?_, ?_⟩
  · intro q hq u
    have hqI := (hJsub hq.1).1
    have hg (y : ℝ) : |F.U (q.1, y)| ≤ K + F.KX * |y| := by
      calc
        _ = |F.U (q.1, y) - F.U (q.1, 0) + F.U (q.1, 0)| := by congr 1; ring
        _ ≤ |F.U (q.1, y) - F.U (q.1, 0)| + |F.U (q.1, 0)| := abs_add_le _ _
        _ ≤ F.KX * |y| + K := add_le_add
          (by simpa only [sub_zero] using F.spatial_abs_sub_le q.1 hqI y 0)
          (hJsub hq.1).2.le
        _ = _ := by ring
    have hq2 : |q.2| ≤ |p.2| + 1 := by
      have hh : |q.2 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
      calc
        |q.2| = |q.2 - p.2 + p.2| := by congr 1; ring
        _ ≤ |q.2 - p.2| + |p.2| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hshift : |q.2 + Real.sqrt (fieldFiniteVariance a v q.1) * u| ≤
        |p.2| + 1 + Real.sqrt V * |u| := by
      calc
        _ ≤ |q.2| + |Real.sqrt (fieldFiniteVariance a v q.1) * u| := abs_add_le _ _
        _ = |q.2| + Real.sqrt (fieldFiniteVariance a v q.1) * |u| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ _ := add_le_add hq2
          (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hhi q.1 hqI)) (abs_nonneg _))
    apply Real.exp_le_exp.mpr
    calc
      ζ * F.affineShift a v q u ≤ |ζ| * |F.affineShift a v q u| := by
        simpa only [abs_mul] using le_abs_self (ζ * F.affineShift a v q u)
      _ ≤ |ζ| * (K + F.KX * |q.2 + Real.sqrt (fieldFiniteVariance a v q.1) * u|) :=
        mul_le_mul_of_nonneg_left (hg _) (abs_nonneg _)
      _ ≤ |ζ| * (K + F.KX * (|p.2| + 1 + Real.sqrt V * |u|)) := by gcongr
      _ = C + L * |u| := by dsimp only [C, L]; ring
  · intro q hq u
    have hqI := (hJsub hq.1).1
    unfold affineDifferential
    calc
      _ ≤ (∑ i, |F.shiftedTangent a v i u q|) + |F.shiftedMean a v u q| :=
        norm_fieldFiniteLinear_le _ _
      _ ≤ (∑ _i : Fin n, A * (1 + |u|)) + F.KX :=
        add_le_add (Finset.sum_le_sum (fun i _ =>
          F.shiftedTangent_bound a v i u hqI hR (hc q.1 hqI i))) (F.bX _ hqI)
      _ = (n : ℝ) * (A * (1 + |u|)) + F.KX := by simp
      _ ≤ CD * (1 + |u|) := by
        dsimp only [CD]
        nlinarith [mul_nonneg F.kx_nonneg (abs_nonneg u)]

end FieldFiniteFamily
end InvariantIsing

end

end OAI
