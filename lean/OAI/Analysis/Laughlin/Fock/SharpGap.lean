import OAI.Analysis.Laughlin.FourBody.BesselAllowance
import OAI.Analysis.Laughlin.Fock.SpectralDistance

namespace OAI

namespace Laughlin
open Filter
open scoped Topology BigOperators

noncomputable def gammaStar : ℝ := 4616733319001 / 10^14

theorem gammaStar_budget :
    1 - (93527408868499 / 10^14 : ℝ) - 61/4096 - 1222*(3/10^6) = gammaStar := by
  norm_num [gammaStar]

theorem one_twenty_fifth_lt_gammaStar : (1/25 : ℝ) < gammaStar := by
  norm_num [gammaStar]

theorem sharp_scalar_budget (error : ℕ → ℝ)
    (he : Tendsto error atTop (𝓝 0)) (γ : ℝ) (hγ : γ < gammaStar) :
    ∀ᶠ Q : ℕ in atTop, γ ≤
      1-93527408868499/10^14-deltaFormula Q-1222*(3/10^6)-error Q := by
  have ht : Tendsto (fun Q : ℕ =>
      1-93527408868499/10^14-deltaFormula Q-1222*(3/10^6)-error Q) atTop
      (𝓝 ((1-93527408868499/10^14)-61/4096-1222*(3/10^6)-(0 : ℝ))) :=
    ((tendsto_const_nhds.sub deltaFormula_tendsto).sub tendsto_const_nhds).sub he
  have hlim : γ < (1-93527408868499/10^14)-61/4096-1222*(3/10^6)-(0 : ℝ) := by
    simpa only [sub_zero, gammaStar_budget] using hγ
  exact ((tendsto_order.mp ht).1 _ hlim).mono fun _ hQ => le_of_lt hQ

namespace Fock

theorem physical_fock_sharp_budget_eventually :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 25 ≤ Q, ∀ x : Space Q,
      sourceKForm Q (by omega) x +
        (1-93527408868499/10^14-deltaFormula Q-1222*(3/10^6)-averagedFourTransferError Q) *
          sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  filter_upwards [physical_threeBody_budget_eventually,eventually_ge_atTop 25] with Q h3 h25
  obtain ⟨h15,h3⟩ := h3
  refine ⟨h25,fun x => ?_⟩
  have h3x := h3 x
  change sourceA3Form Q x-deltaFormula Q*sourceFockEnergy Q x ≤ _ at h3x
  have h4 := sourceA4Form_bessel_bound Q h25 x
  have hs := sourceFockHamiltonian_normal_square Q (by omega) x
  rw [sourceKForm_decomposition Q h25]
  nlinarith

theorem physical_fock_square_eventually_sharp (γ : ℝ) (hγ : γ < gammaStar) :
    ∀ᶠ Q : ℕ in atTop, ∀ x : Space Q,
      γ*sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  filter_upwards [physical_fock_sharp_budget_eventually,
    sharp_scalar_budget averagedFourTransferError averagedFourTransferError_tendsto γ hγ]
    with Q h hs
  obtain ⟨hQ,h⟩ := h
  intro x
  have hE : 0 ≤ sourceFockEnergy Q x := Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  have hm := mul_le_mul_of_nonneg_right hs hE
  have hk := sourceKForm_nonneg Q (by omega) x
  have hx := h x
  linarith

theorem physical_fock_square_uniform_sharp (γ : ℝ) (hγ : γ < gammaStar) :
    ∃ Q₀ : ℕ, 25 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q → ∀ x : Space Q,
      γ*sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  obtain ⟨q,hq⟩ := eventually_atTop.mp (physical_fock_square_eventually_sharp γ hγ)
  exact ⟨max 25 q,le_max_left _ _,fun Q hQ => hq Q (le_trans (le_max_right _ _) hQ)⟩

theorem physical_fock_eigenvalue_gap_uniform_sharp (γ : ℝ) (hγ : γ < gammaStar) :
    ∃ Q₀ : ℕ, 25 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q → ∀ x : Space Q, x ≠ 0 → ∀ a : ℝ,
      sourceFockHamiltonian Q x=(a : ℂ) • x → a=0 ∨ γ ≤ a := by
  obtain ⟨Q₀,h25,h⟩ := physical_fock_square_uniform_sharp γ hγ
  refine ⟨Q₀,h25,fun Q hQ x hx a he => ?_⟩
  have hn : 0 < occupationNormSq Q x :=
    lt_of_le_of_ne (occupationNormSq_nonneg Q x) (Ne.symm (mt (occupationNormSq_eq_zero Q x).mp hx))
  have ha := sourceFock_eigen_nonneg Q x hx a he
  have hs := h Q hQ x
  rw [sourceFock_eigen_energy Q x a he,he,occupationNormSq_smul] at hs
  have hnorm : ‖(a : ℂ)‖^2=a^2 := by simp
  rw [hnorm] at hs
  have hs' : γ*a ≤ a^2 := by nlinarith
  by_cases hz : a=0
  · exact Or.inl hz
  · right
    have hp : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    nlinarith

theorem physical_fock_kernel_distance_uniform_sharp (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ : γ < gammaStar) :
    ∃ Q₀ : ℕ, 25 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q → ∀ x : Space Q,
      ∃ y : Space Q, sourceFockHamiltonian Q y=0 ∧
        γ*occupationNormSq Q (x-y) ≤ sourceFockEnergy Q x := by
  obtain ⟨Q₀,h25,hgap⟩ := physical_fock_eigenvalue_gap_uniform_sharp γ hγ
  refine ⟨Q₀,h25,fun Q hQ x => ?_⟩
  have hg : ∀ v : EuclideanSpace ℂ (Finset (Fin (Q+1))), v≠0 → ∀ a : ℝ,
      euclideanFockHamiltonian Q v=(a : ℂ) • v → a=0 ∨ γ≤a := by
    intro v hv a he
    obtain ⟨u,rfl⟩ := (occupationEuclidean Q).surjective v
    apply hgap Q hQ u (by intro hu; simp [hu] at hv) a
    apply (occupationEuclidean Q).injective
    simpa only [euclideanFockHamiltonian_apply,map_smul] using he
  obtain ⟨z,hz,hb⟩ := spectral_kernel_distance (euclideanFockHamiltonian Q)
    (euclideanFockHamiltonian_symmetric Q) γ hγ0 hg (occupationEuclidean Q x)
  obtain ⟨y,rfl⟩ := (occupationEuclidean Q).surjective z
  refine ⟨y,?_,?_⟩
  · apply (occupationEuclidean Q).injective
    simpa only [euclideanFockHamiltonian_apply,map_zero] using hz
  · rw [← map_sub,occupationEuclidean_norm,euclideanFockHamiltonian_apply,
      occupationEuclidean_inner,sourceFockHamiltonian_quadratic,Complex.ofReal_re] at hb
    exact hb

end Fock
end Laughlin

end OAI
