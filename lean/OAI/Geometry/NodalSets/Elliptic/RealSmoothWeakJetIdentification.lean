import OAI.Geometry.NodalSets.Elliptic.RealL2PointwiseLimit
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetConvolution

namespace OAI

namespace Yau
open MeasureTheory Set Filter Yau.Analysis
open scoped ContDiff Convolution Topology
noncomputable section

theorem real_smooth_partialJet_convolution {n : ℕ} (v k : Coord n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (ds : List (Fin n)) :
    partialJet (v ⋆ k) ds=partialJet v ds ⋆ k := by
  apply real_weak_jet_convolution (partialJet v) ds.length
    (fun es _ ↦ (partialJet_smooth v hv es).continuous.locallyIntegrable)
  · intro es _ i psi hp hc
    have h := (real_compact_test_derivative (partialJet v es) psi
      (partialJet_smooth v hv es) hp hc i univ (subset_univ _)).2.2
    simp only [Measure.restrict_univ] at h
    simpa only [neg_neg,partialJet,coordPartial] using congrArg Neg.neg h.symm
  · exact hk
  · exact hc
  · exact le_rfl

theorem real_smooth_weak_jet_ae {n : ℕ}
    (U : List (Fin n) → Coord n → ℝ) (N : ℕ)
    (hU : ∀ es, es.length ≤ N → MemLp (U es) 2 volume ∧ HasCompactSupport (U es))
    (hw : ∀ es, es.length < N → ∀ i psi,
      ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, U es x*coordPartial psi x i)=-(∫ x, U (i::es) x*psi x))
    (v : Coord n → ℝ) (hv : ContDiff ℝ ∞ v) (ha : v =ᵐ[volume] U [])
    (ds : List (Fin n)) (hd : ds.length ≤ N) :
    partialJet v ds =ᵐ[volume] U ds := by
  let b : ℕ → ContDiffBump (0 : Coord n) := realMollifierBump 1 (by norm_num)
  let w : ℕ → Coord n → ℝ := fun j ↦ U ds ⋆ (b j).normed volume
  have hs (j : ℕ) : ContDiff ℝ ∞ (w j) ∧ HasCompactSupport (w j) :=
    real_compact_convolution_smooth _ _ ((hU ds hd).1.locallyIntegrable (by norm_num))
      (hU ds hd).2 (b j).contDiff_normed (b j).hasCompactSupport_normed
  have he (j : ℕ) : w j=partialJet v ds ⋆ (b j).normed volume := by
    rw [← real_smooth_partialJet_convolution v _ hv (b j).contDiff_normed (b j).hasCompactSupport_normed ds,
      convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) ha Filter.EventuallyEq.rfl,
      real_weak_jet_convolution U N (fun es hh ↦ (hU es hh).1.locallyIntegrable (by norm_num))
        hw _ (b j).contDiff_normed (b j).hasCompactSupport_normed ds hd]
  have hl := real_compact_convolution_L2_tendsto (U ds) (hU ds hd).1 (hU ds hd).2 b
    (realMollifierBump_radius_tendsto 1 (by norm_num))
  apply real_L2_pointwise_limit_ae w
    (fun j ↦ real_compact_continuous_memLp _ (hs j).1.continuous (hs j).2)
    (U ds) (partialJet v ds) (hU ds hd).1 hl
  intro x
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (Coord n)))
    (realMollifierBump_radius_tendsto (n := n) 1 (by norm_num))
    (partialJet_smooth v hv ds).continuous x
  convert ht using 1
  funext j
  rw [he,convolution_lsmul_swap,convolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ by
    dsimp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
    ring)

end
end Yau

end OAI
