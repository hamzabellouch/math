import OAI.Probability.DilutedSpin.CountableTagSelection
import OAI.Probability.DilutedSpin.ExternalRoot

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot Filter Set
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

noncomputable def clipParameters (u : K×ℕ → ℝ) (i : K×ℕ) : ℝ :=
  boundParameter (probeLow i.2) (probeHigh i.2) (u i)

lemma boundParameter_idem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    boundParameter a b (boundParameter a b x) = boundParameter a b x :=
  boundParameter_eq (boundParameter_mem hab x)

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  [∀ q, Fintype (A q)] in
lemma spinFactor_clip (u : K×ℕ → ℝ) : spinFactor D E (clipParameters u) = spinFactor D E u := by
  funext i σ y
  simp only [spinFactor,clipParameters,boundParameter_idem (probeLow_lt_high _).le]

omit [Countable K] [MeasurableSingletonClass K] [IsProbabilityMeasure ν] in
lemma scoreError_clip (M : Model p) (C H : ℝ) (j : K×ℕ) (N : ℕ) (u : K×ℕ → ℝ) :
    scoreError ν Q m D E M C H j N (clipParameters u) = scoreError ν Q m D E M C H j N u := by
  have hf : parameterFactor Prod.fst (fun i : K×ℕ => probeLow i.2)
      (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
      (siteObservable D N) (siteObservable E N) (clipParameters u) =
      parameterFactor Prod.fst (fun i => probeLow i.2) (fun i => probeHigh i.2)
        (fun i => extractionProbe i.2) (siteObservable D N) (siteObservable E N) u := by
    funext i x y
    simp only [parameterFactor,clipParameters,boundParameter_idem (probeLow_lt_high _).le]
  simp only [scoreError,normalizedParameterError,parameterError,hf,clipParameters,
    boundParameter_idem (probeLow_lt_high _).le]

omit [Countable K] [MeasurableSingletonClass K] [DecidableEq K]
  [IsProbabilityMeasure ν] in
lemma increment_clip (M : Model p) (N : ℕ) (u : K×ℕ → ℝ) :
    increment ν Q m D E M N (clipParameters u) = increment ν Q m D E M N u := by
  simp only [increment,spinFactor_clip]

 
theorem actual_parameter_selection (M : Model p) {C H c : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hm : ∀ l, c ≤ m l) (hend : m (Fin.last L) = 1)
    (hw : ∀ j, 0 < ν.real {j})
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → K×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, increment ν Q m D E M (Ns n) (us n) ≤ liminf (pressure M) atTop+ε) ∧
      (∀ j, Tendsto (fun n => scoreError ν Q m D E M C H j (Ns n+1) (us n)) atTop (𝓝 0)) := by
  let π := Measure.infinitePi (fun i : K×ℕ => intervalParameterLaw (probeLow i.2) (probeHigh i.2))
  let (i : K×ℕ) : IsProbabilityMeasure (intervalParameterLaw (probeLow i.2) (probeHigh i.2)) :=
    intervalParameterLaw_probability (probeLow_lt_high i.2)
  let : IsProbabilityMeasure π := by dsimp [π]; infer_instance
  have hm' (l) : 0 < m l := hc.trans_le (hm l)
  let B := Real.log 2+H+(2*p+1)*C*M.alpha+3
  have hB : 0 ≤ B := by
    dsimp [B]
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hi (N : ℕ) : Integrable (increment ν Q m D E M N) π :=
    integrable_increment ν Q m D E π M hθi hhi hm' hend hD hE N
  have he (j : K×ℕ) (N : ℕ) : Integrable (scoreError ν Q m D E M C H j (N+1)) π :=
    integrable_scoreError ν Q m D E π M C H hD hE j (N+1)
  have hn (j : K×ℕ) (N : ℕ) (u) : 0 ≤ scoreError ν Q m D E M C H j (N+1) u :=
    scoreError_nonneg ν Q m D E M C H hw j (N+1) u
  have hl (N : ℕ) (u) : -B ≤ increment ν Q m D E M N u :=
    (abs_le.mp (uniform_increment ν Q m D E M hC hH hθ hh hm' hD hE N u)).1
  have hav (n : ℕ) : ∃ N, n ≤ N ∧ (∫ u, increment ν Q m D E M N u ∂π) ≤
      liminf (pressure M) atTop+ε/2 :=
    low_averaged_increment ν Q m D E π M hθi hhi hm' hend hD hE (by linarith) n
  have ht (j : K×ℕ) : Tendsto (fun N => ∫ u, scoreError ν Q m D E M C H j (N+1) u ∂π) atTop (𝓝 0) :=
    (scoreError_tendsto ν Q m D E M hC hH hc hm hw hD hE j).comp (tendsto_add_atTop_nat 1)
  obtain ⟨Ns,us,hNs,hu,he'⟩ := countable_tag_parameter_selection π (increment ν Q m D E M)
    (fun j N => scoreError ν Q m D E M C H j (N+1)) hi he hn hB
    (show liminf (pressure M) atTop+ε/2 < liminf (pressure M) atTop+ε by linarith) hl hav ht
  refine ⟨Ns,fun n => clipParameters (us n),hNs,?_,?_,?_⟩
  · intro n i
    exact boundParameter_mem (probeLow_lt_high i.2).le (us n i)
  · intro n
    rw [increment_clip]
    exact hu n
  · intro j
    simpa only [scoreError_clip] using he' j

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
