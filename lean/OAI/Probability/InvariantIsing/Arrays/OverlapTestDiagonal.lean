import OAI.Probability.InvariantIsing.Arrays.OverlapTestTransport
import OAI.Probability.InvariantIsing.Cavity.CavitySlowDepth
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

namespace OAI

/-! A single diagonal of finite cavity depths works for every continuous
overlap test. Compactness is used only on the overlap interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

abbrev CompactOverlapTest := C(Icc (0 : ℝ) 1, ℝ)

def compactOverlapTestExtension (f : CompactOverlapTest) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f (Set.projIcc 0 1 zero_le_one x))
    (f.continuous.comp continuous_projIcc) ‖f‖
    (fun x => f.norm_coe_le_norm (Set.projIcc 0 1 zero_le_one x))

lemma compactOverlapTestExtension_apply (f : CompactOverlapTest) (q : OverlapPath) (s : ℝ) :
    compactOverlapTestExtension f (q s) = f ⟨q s,q.nonneg s,q.le_one s⟩ := by
  simp only [compactOverlapTestExtension, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    Set.projIcc_of_mem zero_le_one ⟨q.nonneg s,q.le_one s⟩]

lemma compact_overlap_test_difference_le (f g : CompactOverlapTest) (q B : OverlapPath) :
    |(∫ s, compactOverlapTestExtension f (q s)*(B s-q s) ∂pathMeasure) -
      ∫ s, compactOverlapTestExtension g (q s)*(B s-q s) ∂pathMeasure| ≤ ‖f-g‖ := by
  rw [← integral_sub (integrable_overlap_weighted_test q B (compactOverlapTestExtension f))
    (integrable_overlap_weighted_test q B (compactOverlapTestExtension g))]
  have hb := norm_integral_le_of_norm_le_const (μ := pathMeasure) (C := ‖f-g‖)
    (f := fun s => compactOverlapTestExtension f (q s)*(B s-q s) -
      compactOverlapTestExtension g (q s)*(B s-q s)) (ae_of_all _ fun s => by
        rw [← sub_mul, Real.norm_eq_abs, abs_mul, compactOverlapTestExtension_apply,
          compactOverlapTestExtension_apply]
        have hf : |f ⟨q s,q.nonneg s,q.le_one s⟩-g ⟨q s,q.nonneg s,q.le_one s⟩| ≤ ‖f-g‖ :=
          (f-g).norm_coe_le_norm _
        have hd : |B s-q s| ≤ 1 := abs_le.mpr
          ⟨by linarith [B.nonneg s,q.le_one s],by linarith [B.le_one s,q.nonneg s]⟩
        exact (mul_le_mul hf hd (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hb

theorem exists_diagonal_overlap_tests (q B : ℕ → ℕ → OverlapPath)
    (htest : ∀ n (Φ : ℝ →ᵇ ℝ), Tendsto
      (fun k => ∫ s, Φ (q n k s)*(B n k s-q n k s) ∂pathMeasure) atTop (𝓝 0)) :
    ∃ d : ℕ → ℕ, StrictMono d ∧ ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun n => ∫ s, Φ (q n (d n) s)*(B n (d n) s-q n (d n) s) ∂pathMeasure)
      atTop (𝓝 0) := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq CompactOverlapTest
  let F := fun n k j => ∫ s, compactOverlapTestExtension (u j) (q n k s)*
    (B n k s-q n k s) ∂pathMeasure
  obtain ⟨d, hd, hlim⟩ := cavity_choose_diagonal_errors F
    (fun n j => htest n (compactOverlapTestExtension (u j)))
  refine ⟨d, hd, ?_⟩
  intro Φ
  let f : CompactOverlapTest := ⟨fun x => Φ x, Φ.continuous.comp continuous_subtype_val⟩
  have he n : (∫ s, Φ (q n (d n) s)*(B n (d n) s-q n (d n) s) ∂pathMeasure) =
      ∫ s, compactOverlapTestExtension f (q n (d n) s)*
        (B n (d n) s-q n (d n) s) ∂pathMeasure := by
    apply integral_congr_ae
    filter_upwards [] with s
    rw [compactOverlapTestExtension_apply]
    rfl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := hu.exists_dist_lt f (half_pos hε)
  have hj' : ‖f-u j‖ < ε/2 := by simpa only [dist_eq_norm] using hj
  have ht := (hlim j).eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
  filter_upwards [ht] with n hn
  rw [he, Real.dist_eq, sub_zero]
  have hn' : |F n (d n) j| < ε/2 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hn
  have hb := compact_overlap_test_difference_le f (u j) (q n (d n)) (B n (d n))
  have ha := abs_add_le
    ((∫ s, compactOverlapTestExtension f (q n (d n) s)*
      (B n (d n) s-q n (d n) s) ∂pathMeasure)-F n (d n) j) (F n (d n) j)
  rw [sub_add_cancel] at ha
  change |(∫ s, compactOverlapTestExtension f (q n (d n) s)*
    (B n (d n) s-q n (d n) s) ∂pathMeasure)-F n (d n) j| ≤ ‖f-u j‖ at hb
  linarith

end InvariantIsing

end

end OAI
