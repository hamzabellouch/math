import OAI.NumberTheory.JointDickman.Amplification.LargeAlternativeBound
import OAI.NumberTheory.JointDickman.Amplification.MultiplicityMargins

namespace OAI

/-! # Vanishing contribution of each large high-endpoint class -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem largeMultiplicityLoss_nonneg {Δ δ τ ε : ℝ}
    (hΔ : 0 ≤ Δ) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1/100) (hε : 0 ≤ ε) :
    0 ≤ largeMultiplicityLoss Δ δ τ ε := by
  have hlog : Real.log (2*δ) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have hdiff : 0 ≤ Real.log 2-Real.log (2*δ) := by
    have hh := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hhigh := highOmissionExponent_nonneg hτ hτ1
  unfold largeMultiplicityLoss
  positivity

noncomputable def largeClassError (K η ν : ℝ) (B : ℕ) : ℝ :=
  (K/η)*(Real.log B+1)^3/(B : ℝ)^((32/100 : ℝ)-ν)

theorem largeClassError_tendsto {K η ν : ℝ} (hν : ν < 32/100) :
    Tendsto (largeClassError K η ν) atTop (𝓝 0) := by
  have hh := ((log_add_one_cube_div_rpow_tendsto (sub_pos.mpr hν)).comp
    tendsto_natCast_atTop_atTop).const_mul (K/η)
  unfold largeClassError
  simpa only [mul_zero,mul_div_assoc,Function.comp_apply] using hh

theorem large_high_class_error_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε η : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) (hη : 0 < η) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      largeMultiplicityLoss Δ δ τ ε < 4/100 →
      ∃ K : ℝ, 0 < K ∧
        Tendsto (largeClassError K η (largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε)) atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j d f : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedLargeHighPairCount B L k j d f τ C Δ A D V ≤
            largeClassError K η (largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε) B := by
  obtain ⟨τ₁,hτ₁,hbound⟩ := large_high_alternative_bound hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hε
  refine ⟨min τ₁ (1/1000),lt_min hτ₁ (by norm_num),?_⟩
  intro τ hτ hτsmall hloss
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hτsmall' : τ ≤ 1/1000 := hτsmall.trans (min_le_right _ _)
  obtain ⟨K,hK,hestimate⟩ := hbound τ hτ hτ₁'
  let ν := largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε
  have hν : ν < 32/100 := by
    have hh := largeMultiplicityBase_bounds.2
    dsimp only [ν]
    linarith
  have hν0 : 0 ≤ ν := add_nonneg largeMultiplicityBase_bounds.1.le
    (largeMultiplicityLoss_nonneg hΔ.le hδ hδ1 hτ.le (by linarith) hε.le)
  refine ⟨K,hK,largeClassError_tendsto hν,?_⟩
  filter_upwards [hestimate,auxiliaryLogLength_between,eventually_gt_atTop 1] with B hB hℓB hB1
  intro C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB hjlow
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB1.le)
  have hL : 1 ≤ L := (mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2
  have hcard (R : Finset ℕ) (hR : RegularPrimeSet B L τ C R) : (R.card : ℝ)+1 ≤ Real.log B+1 := by
    have hh := hR.total_upper hL
    have hc : (1/2+τ)*auxiliaryLogLength B ≤ auxiliaryLogLength B := by
      have hm := mul_le_mul_of_nonneg_right (show 1/2+τ ≤ (1 : ℝ) by linarith) hℓB.1
      simpa only [one_mul] using hm
    linarith [hh.trans hc,hℓB.2]
  have hprod : ((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1) ≤ (Real.log B+1)^3 := by
    have hp := mul_le_mul (mul_le_mul (hcard A hAr) (hcard D hDr) (by positivity) (by positivity))
      (hcard V hVr) (by positivity) (by positivity)
    nlinarith
  have hexp : Real.exp (ν*auxiliaryLogLength B) ≤ (B : ℝ)^ν := by
    rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hℓB.2 hν0]
  have hjinv : K/(j : ℝ) ≤ K/(η*(B : ℝ)^(32/100 : ℝ)) :=
    div_le_div_of_nonneg_left hK.le (by positivity) hjlow
  have hh := hB C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB
  refine hh.trans ?_
  change K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
    Real.exp (ν*auxiliaryLogLength B) ≤ _
  calc
    _ = (K/(j : ℝ))*(((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1))*
        Real.exp (ν*auxiliaryLogLength B) := by ring
    _ ≤ (K/(η*(B : ℝ)^(32/100 : ℝ)))*(Real.log B+1)^3*(B : ℝ)^ν :=
      mul_le_mul (mul_le_mul hjinv hprod (by positivity) (by positivity)) hexp
        (Real.exp_pos _).le (by positivity)
    _ = _ := by
      dsimp only [largeClassError,ν]
      rw [Real.rpow_sub hB0]
      field_simp

theorem large_high_class_vanishing
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε η : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) (hη : 0 < η) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      largeMultiplicityLoss Δ δ τ ε < 4/100 →
      ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j d f : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedLargeHighPairCount B L k j d f τ C Δ A D V ≤ E B := by
  obtain ⟨τ₀,hτ₀,hbound⟩ := large_high_class_error_bound hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hε hη
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ hτ hτsmall hloss
  obtain ⟨K,_,hlim,hK⟩ := hbound τ hτ hτsmall hloss
  exact ⟨_,hlim,hK⟩

end JointDickman

end OAI
