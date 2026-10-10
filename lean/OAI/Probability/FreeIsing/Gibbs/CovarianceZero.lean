import OAI.Probability.FreeIsing.Estimates.FreeIsingMeasure
import OAI.Probability.FreeIsing.Estimates.RadialSummability
import OAI.Probability.FreeIsing.Gibbs.CovarianceL2Limit
import OAI.Probability.FreeIsing.Gibbs.PosteriorSymmetry
import OAI.Probability.FreeIsing.Trees.AutDistance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology

namespace Problem367

local instance covarianceZeroNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

theorem HasFreeIsingLaw.finiteIsingPosterior_zero_eq_integral
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (q : (D → IsingSpin) → ℝ) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (fun _ => 0) =
      ∫ sigma, q (D.restrict sigma) ∂μ := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  rw [← integral_map D.measurable_restrict.aemeasurable
    (measurable_of_finite q).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  have hmass (eta : D → IsingSpin) :
      (μ.map D.restrict).real {eta} =
        Real.exp (finiteIsingEnergy beta D eta) /
          (2 * (2 * Real.cosh beta) ^ (inducedEdges D).card) := by
    rw [Measure.real, hμ.restrict_atom D hD eta, freeCylinderWeight_tanh_eq_exp,
      ENNReal.toReal_ofReal (by positivity)]
    rfl
  simp only [hmass, smul_eq_mul, FinitePosterior.fieldMean,
    FinitePosterior.fieldEnergy, zero_mul, Finset.sum_const_zero, add_zero]
  rw [show (∑ eta : D → IsingSpin, Real.exp (finiteIsingEnergy beta D eta)) =
      2 * (2 * Real.cosh beta) ^ (inducedEdges D).card from
    finiteIsing_partitionFunction beta D hD, Finset.sum_div]
  exact Finset.sum_congr rfl (fun eta _ => by ring)

theorem finiteGibbsCovarianceOn_zero {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v w : D) :
    finiteGibbsCovarianceOn beta D v w (fun _ => 0) =
      Real.tanh beta ^ reducedWordDistance v.1.1 w.1.1 := by
  let μ := freeIsingMeasure d (Real.tanh beta)
  have hμ : HasFreeIsingLaw (Real.tanh beta) μ :=
    freeIsingMeasure_hasFreeIsingLaw d (Real.neg_one_lt_tanh beta).le
      (Real.tanh_lt_one beta).le
  rw [finiteGibbsCovarianceOn, finiteIsingPosteriorMean_zero,
    finiteIsingPosteriorMean_zero, zero_mul, sub_zero,
    hμ.finiteIsingPosterior_zero_eq_integral D hD]
  exact hμ.pair_correlation (Real.neg_one_lt_tanh beta).le
    (Real.tanh_lt_one beta).le v.1 w.1

theorem finiteGibbsCovariance_zero {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) :
    finiteGibbsCovariance beta v w n (fun _ => 0) =
      if w ∈ connectedExhaustion v n then
        Real.tanh beta ^ reducedWordDistance v.1 w.1 else 0 := by
  classical
  unfold finiteGibbsCovariance
  split_ifs with hw
  · exact finiteGibbsCovarianceOn_zero beta (connectedExhaustion v n)
      (connectedExhaustion_connected v n) ⟨v, mem_connectedExhaustion v n⟩ ⟨w, hw⟩
  · rfl

@[simp] theorem finiteGibbsPairMean_zero {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) (n : ℕ) :
    finiteGibbsPairMean beta v w n (fun _ => 0) =
      Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
  have h := finiteGibbsCovarianceOn_zero beta (pairExhaustion v w n)
    (pairExhaustion_connected v w n)
    ⟨v, mem_pairExhaustion_left v w n⟩ ⟨w, mem_pairExhaustion_right v w n⟩
  simp only [finiteGibbsCovarianceOn, finiteIsingPosteriorMean_zero,
    zero_mul, sub_zero] at h
  exact h

@[simp] theorem infiniteGibbsPairMean_zero {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) :
    infiniteGibbsPairMean beta v w (fun _ => 0) =
      Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
  have hb : |Real.tanh beta ^ reducedWordDistance v.1 w.1| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (le_of_lt (abs_lt.mpr
      ⟨Real.neg_one_lt_tanh beta, Real.tanh_lt_one beta⟩))
  unfold infiniteGibbsPairMean
  simp only [finiteGibbsPairMean_zero]
  rw [tendsto_const_nhds.limUnder_eq, min_eq_right (abs_le.mp hb).2,
    max_eq_right (abs_le.mp hb).1]

@[simp] theorem infiniteGibbsCovariance_zero {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) :
    infiniteGibbsCovariance beta v w (fun _ => 0) =
      Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
  simp only [infiniteGibbsCovariance, infiniteGibbsPairMean_zero,
    infiniteGibbsSpinMean_zero, zero_mul, sub_zero]

@[simp] theorem infiniteGibbsResponse_zero {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) :
    infiniteGibbsResponse beta v w (fun _ => 0) =
      Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
  simp only [infiniteGibbsResponse, infiniteGibbsCovariance_zero,
    infiniteGibbsSpinMean_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one]

lemma infiniteGibbsResponse_zero_sq {d : ℕ} (beta : ℝ)
    (v w : TreeVertex d) :
    infiniteGibbsResponse beta v w (fun _ => 0) ^ 2 =
      (Real.tanh beta ^ 2) ^ reducedWordDistance v.1 w.1 := by
  rw [infiniteGibbsResponse_zero, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem summable_infiniteGibbsResponse_zero_sq_iff {d : ℕ} (hd : 1 ≤ d)
    (beta : ℝ) (v : TreeVertex d) :
    Summable (fun w => infiniteGibbsResponse beta v w (fun _ => 0) ^ 2) ↔
      ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1 := by
  obtain ⟨g, _, hdist⟩ := exists_treeAut_to_root_distance v
  have heq (w : TreeVertex d) :
      infiniteGibbsResponse beta v (g.toEquiv.symm w) (fun _ => 0) ^ 2 =
        (Real.tanh beta ^ 2) ^ w.1.length := by
    rw [infiniteGibbsResponse_zero_sq, ← hdist, Equiv.apply_symm_apply]
  have hs := (summable_geometric_radial_iff d hd (sq_nonneg (Real.tanh beta)))
  constructor
  · intro h
    apply hs.mp
    have hh := g.toEquiv.symm.summable_iff.mpr h
    simpa only [Function.comp_def, heq] using hh
  · intro h
    apply g.toEquiv.symm.summable_iff.mp
    simpa only [Function.comp_def, heq] using hs.mpr h

theorem infiniteGibbsResponseRow_zero_of_strict {d : ℕ} (beta : ℝ)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (v : TreeVertex d) :
    infiniteGibbsResponseRow beta v (fun _ => 0) =
      1 + (d : ℝ) * Real.tanh beta ^ 2 /
        (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) := by
  obtain ⟨g, _, hdist⟩ := exists_treeAut_to_root_distance v
  unfold infiniteGibbsResponseRow
  rw [← g.toEquiv.symm.tsum_eq]
  simp only [infiniteGibbsResponse_zero_sq, ← hdist, Equiv.apply_symm_apply]
  exact tsum_geometric_radial d (sq_nonneg _) hstrict

theorem not_summable_infiniteGibbsResponse_zero_sq_of_critical
    {d : ℕ} (hd : 1 ≤ d) (beta : ℝ)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (v : TreeVertex d) :
    ¬ Summable (fun w => infiniteGibbsResponse beta v w (fun _ => 0) ^ 2) := by
  rw [summable_infiniteGibbsResponse_zero_sq_iff hd, hcritical]
  exact lt_irrefl _

theorem infiniteGibbsCovariance_brownian_zero {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (beta : ℝ)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i)) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν), ∀ v w,
      infiniteGibbsCovariance beta v w
        (fun i => (0 : ℝ) * spinSign (p.1 i) + B i 0 (p.2 i)) =
          Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
  filter_upwards [brownian_ising_array_zero_ae μ ν hB] with p hp
  intro v w
  simpa only [zero_mul, zero_add, hp] using infiniteGibbsCovariance_zero beta v w

end Problem367

end

end OAI
