import OAI.Probability.InvariantIsing.Haar.MedianMean

namespace OAI

/-! Uniform centered Haar tails for bounded Lipschitz observables. The threshold
is independent of the particular observable and of its additive normalization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem uniform_bounded_haar_mean_tail (hpub : HaarConcentrationInput) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ K ε : ℝ, 0 < K → 0 < ε → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 3 ≤ N →
      ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
      ∀ f : SpecialOrthogonal N → ℝ, Measurable f →
        (∀ U, |f U| ≤ K) →
        (∀ U V, |f U-f V| ≤ K*frobeniusDistance U V) →
      μ.real {U | ε ≤ |f U-(∫ V, f V ∂μ)|} ≤
        C*Real.exp (-a*(N : ℝ)*(ε/2)^2/K^2) := by
  obtain ⟨C,a,hC,ha,hinput⟩ := hpub
  refine ⟨C,a,hC,ha,?_⟩
  intro K ε hK hε
  let d : ℝ := a*(ε/4)^2/K^2
  have hd : 0 < d := by dsimp [d]; positivity
  have hlin : Tendsto (fun n : ℕ => -d*(n : ℝ)) atTop atBot := by
    simpa only [Function.comp_def,neg_mul] using
      tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hd)
  have hlim : Tendsto (fun n : ℕ => ε/4+2*K*(C*Real.exp (-d*(n : ℝ)))) atTop (𝓝 (ε/4)) := by
    simpa only [mul_zero,add_zero,Function.comp_def] using
      (((Real.tendsto_exp_atBot.comp hlin).const_mul C).const_mul (2*K)).const_add (ε/4)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hlim.eventually
    (Iio_mem_nhds (by linarith : ε/4<ε/2)))
  refine ⟨N₀,?_⟩
  intro N hN hN3 μ hμ hInv f hf hbound hLip
  let : IsProbabilityMeasure μ := hμ
  obtain ⟨m,hl,hu,ht⟩ := hinput N hN3 μ hμ hInv f hf K hK hLip
  have hm : |m| ≤ K := abs_median_le_bound μ f m K hbound hl hu
  have hdev U : |f U-m| ≤ 2*K := by
    have hh := (abs_sub (f U) m).trans (add_le_add (hbound U) hm)
    linarith
  have hfi : Integrable f μ := (integrable_const K).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun U => by simpa only [Real.norm_eq_abs] using hbound U)
  have hmean := abs_integral_sub_le_deviation_tail μ f hf hfi m (2*K) (ε/4)
    (by positivity) hdev
  have hmean' := hmean.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (ht (ε/4) (by positivity)) (by positivity : 0 ≤ 2*K)))
  have heq : -a*(N : ℝ)*(ε/4)^2/K^2= -d*(N : ℝ) := by dsimp [d]; ring
  rw [heq] at hmean'
  have hclose : |(∫ V, f V ∂μ)-m| < ε/2 := hmean'.trans_lt (hN₀ N hN)
  have hs : {U | ε ≤ |f U-(∫ V, f V ∂μ)|} ⊆ {U | ε/2 ≤ |f U-m|} := by
    intro U hU
    have hh := abs_sub_le (f U) m (∫ V, f V ∂μ)
    rw [abs_sub_comm m (∫ V, f V ∂μ)] at hh
    change ε/2 ≤ |f U-m|
    change ε ≤ |f U-(∫ V, f V ∂μ)| at hU
    linarith
  exact (measureReal_mono hs).trans (ht (ε/2) (by positivity))

end InvariantIsing

end

end OAI
