import OAI.Analysis.PureInfiniteness.UltrapowerSpectralCompression

namespace OAI

/-! The finite approximation part of KR02 Lemma 7.12, obtained by choosing
first a small spectral cut and then a mesh small enough for its fixed bound. -/

noncomputable section
open Filter Topology
open scoped BigOperators NNReal

namespace WeakPureInfiniteness

variable {A I : Type*} [NonUnitalCStarAlgebra A] [Fintype I] [DecidableEq I]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem ultrapower_finite_abelianization_approx (hP : MainGap.PropertyP A)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j))
    (b : N) (hb : IsSelfAdjoint b) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : N, ‖v‖ ≤ 1 ∧ ∀ i,
      ‖star v * a i * v - a i‖ < ε ∧
      ‖star v * (a i * a i) * v - a i * a i‖ < ε ∧
      ‖a i * (star v * b * v) - (star v * b * v) * a i‖ < ε := by
  let ρ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hρ : Tendsto ρ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hρpos (n : ℕ) : 0 < ρ n := by dsimp [ρ]; positivity
  have hsmall : ∀ᶠ n in atTop, ρ n < 1 ∧ ∀ i,
      ρ n * ‖a i‖ < ε ∧ ρ n * ‖a i * a i‖ < ε := by
    have h1 : ∀ᶠ n in atTop, ρ n < 1 := hρ.eventually (gt_mem_nhds zero_lt_one)
    have h2 : ∀ᶠ n in atTop, ∀ i,
        ρ n * ‖a i‖ < ε ∧ ρ n * ‖a i * a i‖ < ε := by
      apply eventually_all.mpr
      intro i
      have he1 : Tendsto (fun n => ρ n * ‖a i‖) atTop (𝓝 0) := by
        simpa only [zero_mul] using hρ.mul_const ‖a i‖
      have he2 : Tendsto (fun n => ρ n * ‖a i * a i‖) atTop (𝓝 0) := by
        simpa only [zero_mul] using hρ.mul_const ‖a i * a i‖
      exact (he1.eventually (gt_mem_nhds hε)).and (he2.eventually (gt_mem_nhds hε))
    exact h1.and h2
  obtain ⟨n, hn1, hn⟩ := hsmall.exists
  let δ : ℝ≥0 := ⟨ρ n / 2, le_of_lt (half_pos (hρpos n))⟩
  have hδ : 0 < δ := half_pos (hρpos n)
  have hsum : ((δ + δ : ℝ≥0) : ℝ) = ρ n := by change ρ n / 2 + ρ n / 2 = ρ n; ring
  have hcut : (δ + δ : ℝ≥0) < 1 := by change ((δ + δ : ℝ≥0) : ℝ) < 1; rwa [hsum]
  obtain ⟨C, _, hbound⟩ := ultrapower_spectral_compression_bounds U hP a ha hc b hb δ δ hδ hδ hcut
  let f₁ (i : I) (r : ℝ) :=
    (2 * r * Real.sqrt ((5 : ℝ) ^ Fintype.card I)) * C +
      (r + (δ + δ : ℝ≥0) * (‖a i‖ + r))
  let f₂ (i : I) (r : ℝ) :=
    (‖a i‖ + ((∑ k, ‖a k‖) + 2)) *
      ((2 * r * Real.sqrt ((5 : ℝ) ^ Fintype.card I)) * C) +
      (r ^ 2 + (δ + δ : ℝ≥0) * (‖a i * a i‖ + r ^ 2))
  let f₃ (i : I) (r : ℝ) :=
    (2 * r + 2 * Real.sqrt (r ^ 2 + r * (2 * ‖a i‖ + r))) * ‖b‖
  have hevent : ∀ᶠ k in atTop, ∀ i,
      f₁ i (ρ k) < ε ∧ f₂ i (ρ k) < ε ∧ f₃ i (ρ k) < ε := by
    apply eventually_all.mpr
    intro i
    have hc1 : Continuous (f₁ i) := by dsimp [f₁]; fun_prop
    have hc2 : Continuous (f₂ i) := by dsimp [f₂]; fun_prop
    have hc3 : Continuous (f₃ i) := by dsimp [f₃]; fun_prop
    have h10 : f₁ i 0 < ε := by simpa [f₁, hsum] using (hn i).1
    have h20 : f₂ i 0 < ε := by simpa [f₂, hsum] using (hn i).2
    have h30 : f₃ i 0 < ε := by simpa [f₃] using hε
    exact ((hc1.continuousAt.tendsto.comp hρ).eventually (gt_mem_nhds h10)).and
      (((hc2.continuousAt.tendsto.comp hρ).eventually (gt_mem_nhds h20)).and
        ((hc3.continuousAt.tendsto.comp hρ).eventually (gt_mem_nhds h30)))
  obtain ⟨k, hk, he⟩ := (hρ.eventually (gt_mem_nhds zero_lt_one) |>.and hevent).exists
  obtain ⟨v, hv, he'⟩ := hbound (ρ k) (hρpos k) hk.le
  exact ⟨v, hv, fun i => ⟨((he' i).1).trans_lt (he i).1,
    ((he' i).2.1).trans_lt (he i).2.1, ((he' i).2.2).trans_lt (he i).2.2⟩⟩

end WeakPureInfiniteness

end

end OAI
