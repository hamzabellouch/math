import OAI.Probability.SLE.Loewner.SlitChartLimitUniqueness

namespace OAI

/-! Continuity of initial-subarc capacity at its terminal time. Compactness
of the actual inverse charts identifies every scalar subsequential limit. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.capacity_eq_initial_final {p : C(unitInterval,ℂ)}
    (P : SimpleSlitChart p) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    P.capacity = initialCapacity p hi h0 hH 1 := by
  have h1 : (1:unitInterval)≠0 := by norm_num
  rw [initialCapacity,dite_eq_right h1]
  have hr : range (initialSubarc p 1)=range p := by
    ext z
    simp only [mem_range,initialSubarc_apply,one_mul]
  exact le_antisymm
    (P.capacity_le_of_range_subset (initialSlitChart p hi h0 hH 1 h1) hr.ge)
    ((initialSlitChart p hi h0 hH 1 h1).capacity_le_of_range_subset P hr.le)

lemma initialCapacity_terminal_limit_value (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} {c : ℝ}
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) (ht : Tendsto t atTop (𝓝 1))
    (hcap : Tendsto (fun n => initialCapacity p hi h0 hH (t n)) atTop (𝓝 c)) :
    c = initialCapacity p hi h0 hH 1 := by
  obtain ⟨P⟩ := exists_simpleSlitChart p hi h0 hH
  have heq := initialInverse_limit_eq_final p hi h0 hH P hF hlim ht
  have hcoef := inverse_hydrodynamic_coefficient P.coefficient P.inverse_normalized P.right_inverse
  have hmass := (hydrodynamic_vertical_limits (c := P.capacity) hcoef).2
  have hle : P.capacity≤c := by
    apply le_of_tendsto hmass
    apply Eventually.of_forall
    intro n
    have hb := initialInverse_limit_displacement p hi h0 hH hlim hcap (verticalInfinity_mem n)
    rw [heq (verticalInfinity_mem n)] at hb
    have him := (Complex.im_le_norm (P.inverse (verticalInfinity n)-verticalInfinity n)).trans hb
    have hy : 0<(n:ℝ)+1 := by positivity
    have hbound := (le_div_iff₀ hy).mp (show
      (P.inverse (verticalInfinity n)-verticalInfinity n).im≤c/((n:ℝ)+1) from by
        simpa only [verticalInfinity,mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero]
          using him)
    nlinarith
  have hge : c ≤ initialCapacity p hi h0 hH 1 := by
    apply le_of_tendsto hcap
    exact Eventually.of_forall fun n => initialCapacity_monotone p hi h0 hH
      (show t n≤1 from le_top)
  rw [P.capacity_eq_initial_final hi h0 hH] at hle
  exact le_antisymm hge hle

theorem initialCapacity_continuousAt_one (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ContinuousAt (initialCapacity p hi h0 hH) 1 := by
  apply tendsto_of_subseq_tendsto
  intro t ht
  have hb (n : ℕ) : initialCapacity p hi h0 hH (t n)∈
      Icc 0 (initialCapacity p hi h0 hH 1) :=
    ⟨initialCapacity_nonneg p hi h0 hH _,initialCapacity_monotone p hi h0 hH le_top⟩
  obtain ⟨c,_,φ,hφ,hcap⟩ := isCompact_Icc.tendsto_subseq hb
  obtain ⟨ψ,F,hψ,hF,hFlim⟩ := initialInverseChart_subsequence p hi h0 hH (t ∘ φ)
  have ht' : Tendsto (fun n => t (φ (ψ n))) atTop (𝓝 1) :=
    (ht.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hc' := hcap.comp hψ.tendsto_atTop
  have he := initialCapacity_terminal_limit_value p hi h0 hH hF hFlim ht' hc'
  refine ⟨φ ∘ ψ,?_⟩
  change Tendsto (fun n => initialCapacity p hi h0 hH (t (φ (ψ n))))
    atTop (𝓝 (initialCapacity p hi h0 hH 1))
  change Tendsto (fun n => initialCapacity p hi h0 hH (t (φ (ψ n)))) atTop (𝓝 c) at hc'
  rwa [he] at hc'

end SLEExactGauge

end

end OAI
