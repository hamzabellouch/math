import Mathlib.Analysis.SpecificLimits.Normed
import OAI.Analysis.FactorGeneration.MonotoneTrace
import OAI.Analysis.FactorGeneration.PredualRange

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Given-predual evaluations are uniformly small on operator order
intervals bounded by positive contractions with small trace. This is derived
from the constructed tail majorants, without assuming predual normality. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

theorem predual_summable_trace_sandwich (x : X) (a p : ℕ → M.toStarSubalgebra)
    (hp : ∀ n, 0 ≤ (p n).val) (hpn : ∀ n, ‖p n‖ ≤ 1)
    (hpt : Summable (fun n => (τ.trace (p n)).re))
    (hal : ∀ n, -(p n).val ≤ (a n).val) (hau : ∀ n, (a n).val ≤ (p n).val) :
    Tendsto (fun n => predualFunctional M.toStarSubalgebra e x (a n)) atTop (𝓝 0) := by
  obtain ⟨b, _, _, hbanti, hpb, _, hbg⟩ := exists_positive_trace_tail_majorants τ p hp hpn hpt
  exact predualFunctional_order_squeeze_tendsto_zero M.toStarSubalgebra e x a b hbanti hbg
    (fun n => (neg_le_neg (hpb n)).trans (hal n)) (fun n => (hau n).trans (hpb n))

theorem predual_small_of_small_trace_sandwich (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a p : M.toStarSubalgebra,
      0 ≤ p.val → ‖p‖ ≤ 1 → (τ.trace p).re < δ →
      -p.val ≤ a.val → a.val ≤ p.val →
      ‖predualFunctional M.toStarSubalgebra e x a‖ < ε := by
  by_contra h
  push Not at h
  have hseq (n : ℕ) := h ((1/2 : ℝ)^n) (pow_pos (by norm_num) n)
  choose a p hp hpn hpt hal hau hbad using hseq
  have hsum : Summable (fun n => (τ.trace (p n)).re) :=
    Summable.of_nonneg_of_le (fun n => ambient_trace_nonneg τ _ (hp n))
      (fun n => (hpt n).le) (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))
  have ht := predual_summable_trace_sandwich τ e x a p hp hpn hsum hal hau
  have he := Metric.tendsto_nhds.mp ht ε hε
  obtain ⟨n, hn⟩ := he.exists
  exact (not_lt_of_ge (hbad n)) (by simpa only [dist_zero_right] using hn)

theorem predual_trace_sandwich_tendsto_zero {I : Type*} {l : Filter I}
    (x : X) (a p : I → M.toStarSubalgebra)
    (hp : ∀ i, 0 ≤ (p i).val) (hpn : ∀ i, ‖p i‖ ≤ 1)
    (hpt : Tendsto (fun i => (τ.trace (p i)).re) l (𝓝 0))
    (hal : ∀ i, -(p i).val ≤ (a i).val) (hau : ∀ i, (a i).val ≤ (p i).val) :
    Tendsto (fun i => predualFunctional M.toStarSubalgebra e x (a i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := predual_small_of_small_trace_sandwich τ e x ε hε
  filter_upwards [hpt.eventually (gt_mem_nhds hδ)] with i hi
  simpa only [dist_zero_right] using hsmall (a i) (p i) (hp i) (hpn i) hi (hal i) (hau i)

/-! Given-predual evaluation is uniformly trace-two-norm continuous on every
operator-norm bounded ball. No WOT continuity premise is used. -/

theorem predual_small_of_small_norm₂_selfAdjoint (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : M.toStarSubalgebra,
      IsSelfAdjoint a.val → ‖a‖ ≤ 1 → τ.norm₂ a < δ →
      ‖predualFunctional M.toStarSubalgebra e x a‖ < ε := by
  obtain ⟨δ, hδ, hs⟩ := predual_small_of_small_trace_sandwich τ e x ε hε
  refine ⟨δ, hδ, fun a ha hn ht => hs a (ambientAbsoluteValue a)
    (ambientAbsoluteValue_nonneg a) ?_ ?_ (ambient_neg_absoluteValue_le a ha)
    (ambient_le_absoluteValue a ha)⟩
  · exact (ambientAbsoluteValue_norm a).le.trans hn
  · exact (ambientAbsoluteValue_trace_le_norm₂ τ a).trans_lt ht

theorem predual_small_of_small_norm₂ (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : M.toStarSubalgebra,
      ‖a‖ ≤ 1 → τ.norm₂ a < δ →
      ‖predualFunctional M.toStarSubalgebra e x a‖ < ε := by
  obtain ⟨δ, hδ, hs⟩ := predual_small_of_small_norm₂_selfAdjoint τ e x (ε/2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro a hn ht
  have hrsa : IsSelfAdjoint ((realPart a : M.toStarSubalgebra).val) :=
    congrArg (fun b : M.toStarSubalgebra => b.val) (realPart a).property
  have hisa : IsSelfAdjoint ((imaginaryPart a : M.toStarSubalgebra).val) :=
    congrArg (fun b : M.toStarSubalgebra => b.val) (imaginaryPart a).property
  have hr := hs (realPart a) hrsa ((realPart.norm_le a).trans hn)
    ((norm₂_realPart_le τ a).trans_lt ht)
  have hi := hs (imaginaryPart a) hisa ((imaginaryPart.norm_le a).trans hn)
    ((norm₂_imaginaryPart_le τ a).trans_lt ht)
  let f := predualFunctional M.toStarSubalgebra e x
  have he : f a = f (realPart a) + Complex.I * f (imaginaryPart a) := by
    change f a = f (realPart a) + Complex.I • f (imaginaryPart a)
    rw [← map_smul, ← map_add, realPart_add_I_smul_imaginaryPart]
  rw [he]
  have hb := norm_add_le (f (realPart a)) (Complex.I * f (imaginaryPart a))
  rw [norm_mul, Complex.norm_I, one_mul] at hb
  exact hb.trans_lt (by linarith)

theorem predual_norm₂_tendsto_zero_unitBall {I : Type*} {l : Filter I}
    (x : X) (a : I → M.toStarSubalgebra) (hn : ∀ i, ‖a i‖ ≤ 1)
    (ht : Tendsto (fun i => τ.norm₂ (a i)) l (𝓝 0)) :
    Tendsto (fun i => predualFunctional M.toStarSubalgebra e x (a i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := predual_small_of_small_norm₂ τ e x ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with i hi
  simpa only [dist_zero_right] using hs (a i) (hn i) hi

theorem predual_norm₂_tendsto_zero {I : Type*} {l : Filter I}
    (x : X) (a : I → M.toStarSubalgebra) (C : ℝ) (hn : ∀ i, ‖a i‖ ≤ C)
    (ht : Tendsto (fun i => τ.norm₂ (a i)) l (𝓝 0)) :
    Tendsto (fun i => predualFunctional M.toStarSubalgebra e x (a i)) l (𝓝 0) := by
  let D : ℝ := |C|+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hDn : ‖((D⁻¹ : ℝ) : ℂ)‖ = D⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hD.le)]
  let b (i : I) : M.toStarSubalgebra := ((D⁻¹ : ℝ) : ℂ) • a i
  have hb (i : I) : ‖b i‖ ≤ 1 := by
    change ‖((D⁻¹ : ℝ) : ℂ) • a i‖ ≤ 1
    rw [norm_smul, hDn]
    apply (inv_mul_le_iff₀ hD).mpr
    rw [mul_one]
    exact (hn i).trans ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))
  have hbt : Tendsto (fun i => τ.norm₂ (b i)) l (𝓝 0) := by
    simpa only [b, τ.norm₂_smul, hDn, mul_zero] using ht.const_mul D⁻¹
  have h := (predual_norm₂_tendsto_zero_unitBall τ e x b hb hbt).const_smul (D : ℂ)
  have he (i : I) : (D : ℂ) • predualFunctional M.toStarSubalgebra e x (b i) =
      predualFunctional M.toStarSubalgebra e x (a i) := by
    rw [← map_smul]
    congr 1
    simp only [b, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hD.ne',
      Complex.ofReal_one, one_smul]
  simpa only [he, smul_zero] using h

theorem predual_norm₂_tendsto {I : Type*} {l : Filter I}
    (x : X) (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra)
    (C : ℝ) (hn : ∀ i, ‖a i‖ ≤ C)
    (ht : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    Tendsto (fun i => predualFunctional M.toStarSubalgebra e x (a i)) l
      (𝓝 (predualFunctional M.toStarSubalgebra e x b)) := by
  have h := predual_norm₂_tendsto_zero τ e x (fun i => a i-b) (C+‖b‖)
    (fun i => (norm_sub_le _ _).trans (_root_.add_le_add (hn i) le_rfl)) ht
  simpa only [map_sub, tendsto_sub_nhds_zero_iff] using h

end

/-! Every evaluation from the given Banach predual belongs to the constructed
cyclic predual. In particular, the original separable-predual hypothesis
supplies trace-orbit separability without an additional continuity premise. -/
open UltrapowerBridge
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra)

include τ in
theorem predualFunctional_unitBall_continuous (x : X) :
    Continuous (fun T : weakOperatorBall M 1 =>
      predualFunctional M.toStarSubalgebra e x ⟨T.val.toCLM, T.property.1⟩) := by
  let f := predualFunctional M.toStarSubalgebra e x
  have hr := unitBall_functional_continuous_of_norm₂ τ
    (Complex.reCLM.comp (f.restrictScalars ℝ)) (fun a b hn ht =>
      Complex.continuous_re.tendsto _ |>.comp (predual_norm₂_tendsto τ e x a b 1 hn ht))
  have hi := unitBall_functional_continuous_of_norm₂ τ
    (Complex.imCLM.comp (f.restrictScalars ℝ)) (fun a b hn ht =>
      Complex.continuous_im.tendsto _ |>.comp (predual_norm₂_tendsto τ e x a b 1 hn ht))
  have h := (Complex.continuous_ofReal.comp hr).add
    ((Complex.continuous_ofReal.comp hi).mul (continuous_const (y := Complex.I)))
  change Continuous (fun T : weakOperatorBall M 1 =>
    ((f ⟨T.val.toCLM, T.property.1⟩).re : ℂ) +
      ((f ⟨T.val.toCLM, T.property.1⟩).im : ℂ) * Complex.I) at h
  simpa only [Complex.re_add_im] using h

theorem predualFunctional_mem_cyclicPredual (x : X) :
    predualFunctional M.toStarSubalgebra e x ∈ cyclicPredual τ :=
  mem_cyclicPredual_of_unitBall_continuous τ _ (predualFunctional_unitBall_continuous τ e x)

theorem traceOrbit_isSeparable_of_separablePredual
    (hsep : HasSeparablePredual M.toStarSubalgebra) :
    TopologicalSpace.IsSeparable (Set.range (baseVector τ)) := by
  obtain ⟨X, g, s, c, hs, ⟨e⟩⟩ := hsep
  exact traceOrbit_isSeparable_of_given_membership τ e (predualFunctional_mem_cyclicPredual τ e)

end Generator.Tracial

end

end OAI
