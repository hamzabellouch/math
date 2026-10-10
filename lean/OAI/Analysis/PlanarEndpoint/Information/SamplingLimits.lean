import OAI.Analysis.PlanarEndpoint.Information.Expectations
import OAI.Analysis.PlanarEndpoint.Information.JointCompactness
import OAI.Analysis.PlanarEndpoint.Information.JointLaws
import OAI.Analysis.PlanarEndpoint.Information.Sampling
import OAI.Analysis.PlanarEndpoint.Information.TailBounds
import OAI.Analysis.PlanarEndpoint.Information.WeakLimits

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S : ℕ → Type} [∀ n, Fintype (S n)]
  {V Y : ℕ → ℕ → Type} [∀ n i, Fintype (V n i)] [∀ n i, Fintype (Y n i)]
  (L : ℕ → ℝ) (w : (n : ℕ) → S n → ℝ)
  (hw : ∀ n s, 0 ≤ w n s) (hw1 : ∀ n, ∑ s, w n s = 1)
  (v : (n i : ℕ) → S n → V n i) (y : (n i : ℕ) → S n → Y n i)

def sampledJointLaws (n : ℕ) : ProbabilityMeasure (ℕ → ℝ) :=
  sampledJointLaw (L n) (w n) (hw n) (hw1 n) (v n) (y n)

lemma sampledJointLaws_coordinate_tight (hL : ∀ n, 2 ≤ L n)
    (C : ℕ → ℝ) (hcard : ∀ n i, (Fintype.card (Y n i) : ℝ) ≤ (L n) ^ (C i)) :
    ∀ i : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ, ∀ n,
      (sampledJointLaws L w hw hw1 v y n : Measure (ℕ → ℝ))
        {x | R < |x i|} ≤ ε := by
  intro i ε hε
  have ht : Tendsto (fun A : ℝ => ENNReal.ofReal ((2 : ℝ) ^ (C i-A))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (polynomial_alphabet_mass_envelope_tendsto_zero (C i))
  obtain ⟨R, hRC, hRε⟩ := ((eventually_ge_atTop (C i)).and
    (ht.eventually (gt_mem_nhds hε))).exists
  refine ⟨R, fun n => ?_⟩
  exact ((sampledJointLaw_mass_tail_le (L n) (by linarith [hL n]) (w n)
    (hw n) (hw1 n) (v n) (y n) i R).trans
      (ENNReal.ofReal_le_ofReal (polynomial_alphabet_mass_bound (hL n) (hcard n i) hRC))).trans hRε.le

lemma sampledJointLaws_uniform_expected_tail (hL : ∀ n, 2 ≤ L n)
    (C : ℕ → ℝ) (hcard : ∀ n i, (Fintype.card (Y n i) : ℝ) ≤ (L n) ^ (C i))
    (i : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → ∀ n,
      (∫ x, if A < x i then x i else 0
        ∂(sampledJointLaws L w hw hw1 v y n : Measure (ℕ → ℝ))) < ε := by
  intro ε hε
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    ((polynomial_alphabet_envelope_tendsto_zero (C i)).eventually (gt_mem_nhds hε))
  refine ⟨max a (2*C i), fun A hA n => ?_⟩
  exact ((sampledJointLaw_expected_tail_le (L n) (by linarith [hL n]) (w n)
    (hw n) (hw1 n) (v n) (y n) i A).trans
      (polynomial_alphabet_tail_bound (hL n) (hcard n i)
        ((le_max_right _ _).trans hA))).trans_lt (ha A ((le_max_left _ _).trans hA))

lemma sampledJointLaws_sharp_upper_tails (hL : ∀ n, 2 ≤ L n)
    (hLlim : Tendsto L atTop atTop) (c : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (C i)))
    (hcard : ∀ n i, (Fintype.card (Y n i) : ℝ) ≤ (L n) ^ (c n i))
    (i : ℕ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => (sampledJointLaws L w hw hw1 v y n : Measure (ℕ → ℝ))
      {x | C i + η < x i}) atTop (𝓝 0) := by
  have henv : Tendsto (fun n => ENNReal.ofReal ((L n) ^ (-(η/2)))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.tendsto_ofReal
      ((tendsto_rpow_neg_atTop (half_pos hη)).comp hLlim)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henv
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [(hc i).eventually (gt_mem_nhds (by linarith : C i < C i + η/2))] with n hn
  have hLn : 0 < L n := by linarith [hL n]
  have hsub : {x : ℕ → ℝ | C i + η < x i} ⊆ {x | C i + η < |x i|} := by
    intro x hx
    change C i + η < x i at hx
    change C i + η < |x i|
    exact lt_of_lt_of_le hx (le_abs_self _)
  refine (measure_mono hsub).trans ?_
  apply (sampledJointLaw_mass_tail_le (L n) (by linarith [hL n]) (w n)
    (hw n) (hw1 n) (v n) (y n) i (C i+η)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (Fintype.card (Y n i) : ℝ) * (L n) ^ (-(C i+η)) ≤
        (L n) ^ (c n i) * (L n) ^ (-(C i+η)) :=
      mul_le_mul_of_nonneg_right (hcard n i) (Real.rpow_nonneg hLn.le _)
    _ = (L n) ^ (c n i - (C i+η)) := by
      rw [sub_eq_add_neg, Real.rpow_add hLn]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith [hL n]) (by linarith)

theorem exists_sampled_information_limit (hL : ∀ n, 2 ≤ L n)
    (hLlim : Tendsto L atTop atTop) (c : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (C i)))
    (hcard : ∀ n i, (Fintype.card (Y n i) : ℝ) ≤ (L n) ^ (c n i)) :
    ∃ μ : ProbabilityMeasure (ℕ → ℝ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto ((sampledJointLaws L w hw hw1 v y) ∘ φ) atTop (𝓝 μ) ∧
      (∀ᵐ x ∂(μ : Measure (ℕ → ℝ)), ∀ i, 0 ≤ x i ∧ x i ≤ C i) ∧
      ∀ i, Integrable (fun x => x i) (μ : Measure (ℕ → ℝ)) ∧
        Tendsto (fun n => ∑ s, w (φ n) s *
          sampledInformation (L (φ n)) (w (φ n)) (v (φ n) i) (y (φ n) i) s)
          atTop (𝓝 (∫ x, x i ∂(μ : Measure (ℕ → ℝ)))) := by
  have hb : ∀ i, ∃ D : ℝ, ∀ n, c n i ≤ D := by
    intro i
    obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto _ (hc i)).bddAbove
    exact ⟨D, fun n => hD (Set.mem_range_self n)⟩
  choose D hD using hb
  have hcardD : ∀ n i, (Fintype.card (Y n i) : ℝ) ≤ (L n) ^ (D i) := by
    intro n i
    exact (hcard n i).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith [hL n]) (hD i n))
  obtain ⟨μ, φ, hφ, hμ⟩ := exists_joint_weak_limit
    (sampledJointLaws_coordinate_tight L w hw hw1 v y hL D hcardD)
  have hnonneg : ∀ i, ∀ᵐ x ∂(μ : Measure (ℕ → ℝ)), 0 ≤ x i := by
    intro i
    apply ae_nonneg_of_weak_limit_tails hμ (continuous_apply i)
    intro η hη
    have hz : ∀ n, (sampledJointLaws L w hw hw1 v y (φ n) : Measure (ℕ → ℝ))
        {x | x i < -η} = 0 := by
      intro n
      apply le_antisymm _ bot_le
      have hn := sampledJointLaw_nonneg (L (φ n)) (by linarith [hL (φ n)])
        (w (φ n)) (hw (φ n)) (hw1 (φ n)) (v (φ n)) (y (φ n)) i
      have hn' := ae_iff.mp hn
      exact (measure_mono (fun x hx => by
        change x i < -η at hx
        change ¬0 ≤ x i
        linarith)).trans_eq hn'
    simpa only [Function.comp_apply, hz] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  have hupper : ∀ i, ∀ᵐ x ∂(μ : Measure (ℕ → ℝ)), x i ≤ C i := by
    intro i
    have h := ae_le_on_open_of_weak_limit_tails hμ isOpen_univ (continuous_apply i) (C i)
      (fun η hη => by
        simpa only [Set.univ_inter, Function.comp_def] using
          (sampledJointLaws_sharp_upper_tails L w hw hw1 v y hL hLlim c C hc hcard i hη).comp hφ.tendsto_atTop)
    exact h.mono (fun x hx => hx (Set.mem_univ x))
  refine ⟨μ, φ, hφ, hμ, ae_all_iff.mpr (fun i => (hnonneg i).and (hupper i)), ?_⟩
  intro i
  have he := expected_information_tendsto hμ (continuous_apply i)
    (fun n => sampledJointLaw_integrable (L (φ n)) (w (φ n)) (hw (φ n)) (hw1 (φ n))
      (v (φ n)) (y (φ n)) i)
    (fun n => sampledJointLaw_nonneg (L (φ n)) (by linarith [hL (φ n)])
      (w (φ n)) (hw (φ n)) (hw1 (φ n)) (v (φ n)) (y (φ n)) i)
    (hnonneg i) (hupper i) (fun ε hε => by
      obtain ⟨A₀, hA₀⟩ := sampledJointLaws_uniform_expected_tail L w hw hw1 v y hL D hcardD i ε hε
      exact ⟨A₀, fun A hA n => hA₀ A hA (φ n)⟩)
  refine ⟨he.1, ?_⟩
  simpa only [Function.comp_apply, sampledJointLaws, sampledJointLaw_integral] using he.2

end PlanarEndpoint.TransverseInformation
end

end OAI
