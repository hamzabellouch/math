import OAI.Probability.FreeIsing.Cavity.MomentTransport
import OAI.Probability.FreeIsing.Conditioning.SelectedPosteriorEvenConditioning
import OAI.Probability.FreeIsing.Energy.SelectedCriticalFieldMoments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.selectedGaussianField_abs_identDistrib_cond_spin
    {d : ℕ} {ι : Type*} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (t : ℝ≥0) (v : ι → TreeVertex d) (r w : TreeVertex d) (s : IsingSpin) :
    IdentDistrib (fun p => |selectedGaussianField μ t v r p|)
      (fun p => |selectedGaussianField μ t v r p|)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 w = s}])
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
  hμ.selected_gaussian_field_abs_identDistrib_cond_spin t t v r w s

theorem HasFreeIsingLaw.integrable_selectedGaussianField_cond_abs_pow
    {d : ℕ} {ι : Type*} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (hr : r ∈ Set.range v) (w : TreeVertex d) (s : IsingSpin) (p : ℕ) :
    Integrable (fun q => |selectedGaussianField μ t v r q| ^ p)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{q | q.1 w = s}]) := by
  have h := (hμ.selectedGaussianField_abs_identDistrib_cond_spin t v r w s).comp
    (measurable_id.pow_const p)
  exact h.integrable_iff.mpr (hμ.integrable_selectedGaussianField_abs_pow hb t v r hr p)

theorem HasFreeIsingLaw.childComponentField_cond_abs_identDistrib
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (t : ℝ≥0) (c a : Fin d)
    (w : TreeVertex d) (s : IsingSpin) :
    IdentDistrib
      (fun p => |selectedGaussianField μ t (childComponentIndexVertex c a)
        (prefixFlip c (RootedBroadcast.branchRoot a)) p|)
      (fun p => |selectedGaussianField μ t (componentIndexVertex (c := c))
        (RootedBroadcast.branchRoot c) p|)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 w = s}])
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have hF : Measurable (Function.uncurry
      (fun (a : IsingSpin) (z : ℝ) => (t : ℝ) * spinSign a + z)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add
      measurable_snd
  have ha : Measurable (fun x : ℝ => |Real.artanh x|) := by
    unfold Real.artanh
    fun_prop
  apply (hμ.selectedGaussianField_abs_identDistrib_cond_spin t
    (childComponentIndexVertex c a) (prefixFlip c (RootedBroadcast.branchRoot a)) w s).trans
  exact (childComponentPosterior_identDistrib hμ (gaussianReal 0 t) hF c a).comp ha

theorem HasFreeIsingLaw.childComponentField_cond_response_moment
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c a : Fin d) (w : TreeVertex d) (s : IsingSpin) (p : ℕ) :
    Integrable
      (fun q => |cavityMessage (Real.tanh beta)
        (selectedGaussianField μ t (childComponentIndexVertex c a)
          (prefixFlip c (RootedBroadcast.branchRoot a)) q)| ^ p)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{q | q.1 w = s}]) ∧
    (∫ q, |cavityMessage (Real.tanh beta)
      (selectedGaussianField μ t (childComponentIndexVertex c a)
        (prefixFlip c (RootedBroadcast.branchRoot a)) q)| ^ p
      ∂((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{q | q.1 w = s}])) ≤
      (Real.tanh beta) ^ p * ∫ q,
        |selectedGaussianField μ t (componentIndexVertex (c := c))
          (RootedBroadcast.branchRoot c) q| ^ p
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) := by
  have h0 := tanh_nonneg_of_beta_nonneg hb
  have h1 := (Real.tanh_lt_one beta).le
  have hr : RootedBroadcast.branchRoot c ∈ Set.range (componentIndexVertex (c := c)) := by
    apply mem_range_componentIndexVertex.mpr
    exact ⟨[], by simp [RootedBroadcast.branchRoot]⟩
  exact response_abs_moment_of_identDistrib_abs
    (hμ.childComponentField_cond_abs_identDistrib t c a w s)
    (lipschitzWith_cavityMessage h0 h1).continuous.measurable
    (measurable_selectedGaussianField μ t _ _)
    (cavityMessage_abs_le_mul h0 h1) p
    (hμ.integrable_selectedGaussianField_abs_pow hb t _ _ hr p)

end Problem367

end

end OAI
