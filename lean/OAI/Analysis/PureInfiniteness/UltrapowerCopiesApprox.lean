import OAI.Analysis.PureInfiniteness.UltrapowerCopyBounds

namespace OAI

/-! Small cut and mesh give finite amplification to any desired accuracy. -/

noncomputable section
open Filter Topology
open scoped BigOperators NNReal

namespace WeakPureInfiniteness

variable {A I M : Type*} [NonUnitalCStarAlgebra A]
  [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem ultrapower_copies_approx (hP : MainGap.PropertyP A)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v : M → N, (∀ j, ‖v j‖ ≤ 1) ∧ ∀ i,
      (∀ j k, ‖star (v j) * a i * v k - (if j = k then a i else 0)‖ < ε) ∧
      (∀ j, ‖star (v j) * (a i * a i) * v j - a i * a i‖ < ε) := by
  let ρ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hρ : Tendsto ρ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hρpos (n : ℕ) : 0 < ρ n := by dsimp [ρ]; positivity
  have hsmall : ∀ᶠ n in atTop, ρ n < 1 ∧ ∀ i,
      ρ n * ‖a i‖ < ε ∧ ρ n * ‖a i * a i‖ < ε := by
    have h1 := hρ.eventually (gt_mem_nhds zero_lt_one)
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
  let δ : ℝ≥0 := ⟨ρ n, (hρpos n).le⟩
  have hδcoe : (δ : ℝ) = ρ n := rfl
  obtain ⟨C, _, hbound⟩ := ultrapower_copy_compression_bounds (M := M) U hP a ha hc δ
    (hρpos n) hn1
  let f₁ (i : I) (r : ℝ) :=
    (2 * r * Real.sqrt ((Fintype.card M : ℝ) * (5 : ℝ) ^ Fintype.card I)) * C +
      (r + δ * (‖a i‖ + r))
  let f₂ (i : I) (r : ℝ) :=
    (‖a i‖ + ((∑ k, ‖a k‖) + 2)) *
      ((2 * r * Real.sqrt ((Fintype.card M : ℝ) * (5 : ℝ) ^ Fintype.card I)) * C) +
      (r ^ 2 + δ * (‖a i * a i‖ + r ^ 2))
  have hevent : ∀ᶠ k in atTop, ∀ i, f₁ i (ρ k) < ε ∧ f₂ i (ρ k) < ε := by
    apply eventually_all.mpr
    intro i
    have hc1 : Continuous (f₁ i) := by dsimp [f₁]; fun_prop
    have hc2 : Continuous (f₂ i) := by dsimp [f₂]; fun_prop
    have h10 : f₁ i 0 < ε := by simpa [f₁, hδcoe] using (hn i).1
    have h20 : f₂ i 0 < ε := by simpa [f₂, hδcoe] using (hn i).2
    exact ((hc1.continuousAt.tendsto.comp hρ).eventually (gt_mem_nhds h10)).and
      ((hc2.continuousAt.tendsto.comp hρ).eventually (gt_mem_nhds h20))
  obtain ⟨k, hk, he⟩ := (hρ.eventually (gt_mem_nhds zero_lt_one) |>.and hevent).exists
  obtain ⟨v, hv, hve⟩ := hbound (ρ k) (hρpos k) hk.le
  exact ⟨v, hv, fun i => ⟨fun j k => ((hve i).1 j k).trans_lt (he i).1,
    fun j => ((hve i).2 j).trans_lt (he i).2⟩⟩

end WeakPureInfiniteness

end

end OAI
