import OAI.Probability.InvariantIsing.Spectral.SpectralArrayGG
import Mathlib.MeasureTheory.Measure.Prokhorov

namespace OAI

/-! Compact array/center subsequences and constant limiting diagonals. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma spectralArray_center_subsequence (m : ℕ) (L : ℕ → ProbabilityMeasure (SpectralArray m))
    (c : ℕ → Fin m → Set.Icc (0 : ℝ) 1) :
    ∃ Q : ProbabilityMeasure (SpectralArray m), ∃ q : Fin m → Set.Icc (0 : ℝ) 1,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (L ∘ φ) atTop (nhds Q) ∧
        Tendsto (c ∘ φ) atTop (nhds q) := by
  obtain ⟨p, φ, hφ, hp⟩ := CompactSpace.tendsto_subseq (fun k => (L k, c k))
  refine ⟨p.1, p.2, φ, hφ, ?_, ?_⟩
  · exact (continuous_fst.tendsto p).comp hp
  · exact (continuous_snd.tendsto p).comp hp

/-- Vanishing actual L1 self-overlap fluctuations and converging compact
centers give deterministic diagonals in the weak limiting array. -/
theorem spectralArray_constant_diagonal_of_weak_limit {m : ℕ}
    (L : ℕ → ProbabilityMeasure (SpectralArray m)) (Q : ProbabilityMeasure (SpectralArray m))
    (hL : Tendsto L atTop (nhds Q)) (center : ℕ → Fin m → ℝ) (q : Fin m → ℝ)
    (hc : Tendsto center atTop (nhds q))
    (hdiag : ∀ i a, Tendsto
      (fun k => ∫ x, |(x (i, i) a : ℝ) - center k a| ∂(L k : Measure (SpectralArray m)))
      atTop (nhds 0)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i, i) a : ℝ) = q a := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro a
  let F := fun x : SpectralArray m => |(x (i, i) a : ℝ) - q a|
  have hF : Continuous F := by fun_prop
  have hfixed : Tendsto (fun k => ∫ x, F x ∂(L k : Measure (SpectralArray m))) atTop
      (nhds (∫ x, F x ∂(Q : Measure (SpectralArray m)))) := by
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  have hbound (k : ℕ) : (∫ x, F x ∂(L k : Measure (SpectralArray m))) ≤
      (∫ x, |(x (i, i) a : ℝ) - center k a| ∂(L k : Measure (SpectralArray m))) + |center k a - q a| := by
    have hg : Continuous (fun x : SpectralArray m => |(x (i, i) a : ℝ) - center k a|) := by fun_prop
    calc
      _ ≤ ∫ x, |(x (i, i) a : ℝ) - center k a| + |center k a - q a|
          ∂(L k : Measure (SpectralArray m)) :=
        integral_mono (compact_integrable hF) (compact_integrable (hg.add continuous_const))
          (fun x => abs_sub_le _ _ _)
      _ = _ := by
        rw [integral_add (compact_integrable hg) (integrable_const _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hcenter : Tendsto (fun k => |center k a - q a|) atTop (nhds 0) := by
    simpa only [sub_self, abs_zero] using
      (((tendsto_pi_nhds.mp hc a).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => q a) atTop (nhds (q a)))).abs)
  have hzero : Tendsto (fun k => ∫ x, F x ∂(L k : Measure (SpectralArray m))) atTop (nhds 0) :=
    squeeze_zero (fun k => integral_nonneg (fun x => abs_nonneg _)) hbound
      (by simpa only [add_zero] using (hdiag i a).add hcenter)
  have hz : (∫ x, F x ∂(Q : Measure (SpectralArray m))) = 0 := tendsto_nhds_unique hfixed hzero
  have hae := (integral_eq_zero_iff_of_nonneg (fun x : SpectralArray m => abs_nonneg ((x (i, i) a : ℝ) - q a))
    (compact_integrable hF)).mp hz
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (abs_eq_zero.mp hx)

end InvariantIsing

end

end OAI
