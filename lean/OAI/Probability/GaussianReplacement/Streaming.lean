import OAI.Probability.GaussianReplacement.SamplingLaw

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace CurrentProjection

namespace StreamKernel
open NoiselessRegression unitInterval
namespace CompletedLearner
variable {d M T : ℕ} (K : CompletedLearner d M T)




lemma borel_estimateLaw_ae (hd : 3 ≤ d) :
    ∀ᵐ z ∂((NoiselessRegression.uniformSphere d).prod (sampleLaw d T)),
      K.borel.estimateLaw z.1 z.2 = K.estimateLaw z.1 z.2 := by
  let : NeZero d := ⟨by omega⟩
  have hobs (n : ℕ) (a : State M) (i : Fin T) :
      ∀ᵐ z ∂((NoiselessRegression.uniformSphere d).prod (sampleLaw d T)),
        K.borel.transition n a (z.2 i,⟪z.2 i,z.1.val⟫) =
          K.transition n a (z.2 i,⟪z.2 i,z.1.val⟫) := by
    have h := NoiselessRegression.sphere_sample_observation_quasi
      (E:=NoiselessRegression.Vector d) (by simpa using hd) i
    simpa only [NoiselessRegression.uniformSphere, NoiselessRegression.sphereLaw,
      NoiselessRegression.sampleLaw, real_inner_comm] using h.ae (K.borel_transition_ae n a)
  have hall : ∀ᵐ z ∂((NoiselessRegression.uniformSphere d).prod (sampleLaw d T)),
      ∀ n a i, K.borel.transition n a (z.2 i,⟪z.2 i,z.1.val⟫) =
          K.transition n a (z.2 i,⟪z.2 i,z.1.val⟫) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun a => ae_all_iff.2 fun i => hobs n a i
  filter_upwards [hall] with z hz
  have hr (n : ℕ) : K.borel.runLaw z.1 z.2 n = K.runLaw z.1 z.2 n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [runLaw, runLaw, ih]
      congr 1
      funext a
      cases a with
      | inr done => rfl
      | inl a =>
        unfold nextLaw
        split_ifs with hn
        · change (K.borel.transition (n+1) a (z.2 ⟨n,hn⟩,⟪z.2 ⟨n,hn⟩,z.1.val⟫)).map _ =
            (K.transition (n+1) a (z.2 ⟨n,hn⟩,⟪z.2 ⟨n,hn⟩,z.1.val⟫)).map _
          rw [hz (n+1) a ⟨n,hn⟩]
        · rfl
  unfold estimateLaw
  rw [hr T]
  rfl

lemma borel_uniformSuccess (hd : 3 ≤ d) (ε : ℝ) :
    K.borel.uniformSuccess ε = K.uniformSuccess ε := by
  unfold uniformSuccess
  apply lintegral_congr_ae
  filter_upwards [K.borel_estimateLaw_ae hd] with z hz
  rw [hz]

end CompletedLearner
end StreamKernel



namespace StreamKernel
open NoiselessRegression

lemma exists_seed_success {Ξ : Type*} [MeasurableSpace Ξ]
    (π : Measure Ξ) [IsProbabilityMeasure π] (f : Ξ → ℝ≥0∞)
    {p : ℝ≥0∞} (hp : p ≠ ∞) (hs : p ≤ ∫⁻ ξ, f ξ ∂π) :
    ∃ ξ, p ≤ f ξ := by
  by_contra h
  push Not at h
  have hle : (∫⁻ ξ, f ξ ∂π) ≤ p := by
    calc
      _ ≤ ∫⁻ _ : Ξ, p ∂π := lintegral_mono (fun ξ => (h ξ).le)
      _ = p := by simp
  have hlt := lintegral_strict_mono (IsProbabilityMeasure.ne_zero π)
    (aemeasurable_const (μ:=π) (b:=p)) (ne_top_of_le_ne_top hp hle)
      (Filter.Eventually.of_forall h)
  have : (∫⁻ ξ, f ξ ∂π) < p := by simpa using hlt
  exact (not_lt_of_ge hs) this




lemma completed_fixed_three_fifths {d M T : ℕ} (K : CompletedLearner d M T)
    (hd : 32 ≤ d) (hM : (M : ℝ) ≤ (d : ℝ)^2)
    {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1/10)
    (hs : (3/5 : ℝ≥0∞) ≤ K.uniformSuccess ε) :
    (1/(4*(600000+200*(1:ℝ)))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  let : NeZero d := ⟨by omega⟩
  let R := K.sampling
  have hs' : (3/5 : ℝ≥0∞) ≤ R.program.uniformSuccess (coinLaw (T+1)) ε := by
    rw [R.uniformSuccess_eq, K.borel_uniformSuccess (by omega)]
    exact hs
  have hT : d ≤ 8*T := by
    by_contra h
    have hb := hs'.trans (R.program.linear_success_bound_three_fifths (coinLaw (T+1))
      (by omega) (by omega) hε10 R.admissible)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    norm_num [ENNReal.toReal_div] at hr
  let q := (d-1)/4
  let a := 2*q
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hqa : 2*q ≤ a := le_rfl
  have ha : 2*a ≤ d-1 := by dsimp [a,q]; omega
  have hdq : d ≤ 8*q := by dsimp [q]; omega
  have hda : d ≤ 4*a := by dsimp [a]; omega
  exact precision_from_stream_bound_three_fifths hd hT (by omega) hdq hda
    (by simpa using hM) (by norm_num) hε (by linarith)
    (R.program.streaming_success_bound_real_three_fifths (coinLaw (T+1)) R.admissible
      (by omega) hε ha hq hqa hs')



theorem streaming_three_fifths : StreamingMain (3/5) := by
  refine ⟨1/(4*(600000+200*(1:ℝ))), by positivity, ?_⟩
  intro M hM
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max 32 d₂, ?_⟩
  intro d hd T ε hε hε10 Ξ _ _ π _ K _ hs
  obtain ⟨ξ,hξ⟩ := exists_seed_success π (fun ξ => (K ξ).uniformSuccess ε)
    (ENNReal.div_ne_top (by norm_num) (by norm_num) : (3/5 : ℝ≥0∞) ≠ ∞) hs
  have hmem : (M d : ℝ) ≤ (d : ℝ)^2 := by
    have hm := hd₂ d (by omega)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (M d) : (0 : ℝ) ≤ M d),
      abs_of_nonneg (sq_nonneg (d : ℝ))] using hm
  exact completed_fixed_three_fifths (K ξ) (by omega) hmem hε hε10 hξ

lemma StreamingMain.mono {p q : ℝ≥0∞} (h : StreamingMain p) (hpq : p ≤ q) :
    StreamingMain q := by
  obtain ⟨c,hc,h⟩ := h
  refine ⟨c,hc,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := h M hM
  refine ⟨d₀,?_⟩
  intro d hd T ε hε hε10 Ξ _ _ π _ K hm hs
  exact hd₀ d hd T ε hε hε10 Ξ π K hm (hpq.trans hs)
lemma three_fifths_le_two_thirds : (3/5 : ℝ≥0∞) ≤ 2/3 := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).1
  norm_num [ENNReal.toReal_div]
end StreamKernel



theorem criticalStreamingMain : CriticalStreamingMain := StreamKernel.streaming_three_fifths


theorem levelsStreamingMain : LevelsStreamingMain :=
  StreamKernel.streaming_three_fifths.mono StreamKernel.three_fifths_le_two_thirds


theorem hybridStreamingMain : HybridStreamingMain :=
  StreamKernel.streaming_three_fifths.mono StreamKernel.three_fifths_le_two_thirds


theorem fiberStreamingMain : FiberStreamingMain :=
  StreamKernel.streaming_three_fifths.mono StreamKernel.three_fifths_le_two_thirds




end CurrentProjection

end

end OAI
