import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingRegimes

namespace OAI

/-!
# Divergence of the logarithmic shearing window

Noncentral return matrices approaching the identity have positive scale
tending to zero. Their logarithmic time window tends to infinity, and
the two exponential regimes have exactly the bounds needed for the
common-time selection theorem.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootShearingKappa_one {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rootShearingKappa i j (1 : G n) = 0 := by
  have hoff : rootShearingOffDiagonalSize i j (1 : G n) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i ∨ k = j
    · simp only [hk, ite_true]
    · have hki : k ≠ i := fun h => hk (Or.inl h)
      have hkj : k ≠ j := fun h => hk (Or.inr h)
      simp [Matrix.SpecialLinearGroup.coe_one, hki, hkj, hkj.symm]
  simp [rootShearingKappa, rootShearingMovingSize, hoff,
    Matrix.SpecialLinearGroup.coe_one, hij.symm]

def rootShearingLogTime {n : ℕ} (i j : Fin n) (g : G n) : ℝ :=
  -Real.log (rootShearingKappa i j g) / 4

theorem rootShearingLogTime_normalizes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g) :
    rootShearingKappa i j g = Real.exp (-4 * rootShearingLogTime i j g) := by
  have hk := rootShearingKappa_pos_of_noncentral hij g hnot
  have he : -4 * rootShearingLogTime i j g = Real.log (rootShearingKappa i j g) := by
    unfold rootShearingLogTime
    ring
  rw [he, Real.exp_log hk]

theorem rootShearingLogTime_nonneg {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1) : 0 ≤ rootShearingLogTime i j g := by
  have hk := rootShearingKappa_pos_of_noncentral hij g hnot
  have hl := Real.log_nonpos hk.le hsmall
  exact div_nonneg (neg_nonneg.mpr hl) (by norm_num)

theorem rootShearingLogTime_tendsto {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g m) :
    Tendsto (fun m => rootShearingLogTime i j (g m)) atTop atTop := by
  have hk : Tendsto (fun m => rootShearingKappa i j (g m)) atTop (𝓝 0) := by
    change Tendsto (rootShearingKappa i j ∘ g) atTop (𝓝 0)
    simpa only [rootShearingKappa_one hij] using
      ((continuous_rootShearingKappa i j).tendsto 1).comp hg
  have hkgt : Tendsto (fun m => rootShearingKappa i j (g m)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hk, Eventually.of_forall fun m =>
      rootShearingKappa_pos_of_noncentral hij (g m) (hnot m)⟩
  have hl := Real.tendsto_log_nhdsGT_zero.comp hkgt
  have hn : Tendsto (fun m => -Real.log (rootShearingKappa i j (g m))) atTop atTop :=
    tendsto_neg_atBot_atTop.comp hl
  exact (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).mpr hn

theorem rootShearingKappa_two_regimes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1) :
    ∃ θ : ℝ, 4 * rootShearingLogTime i j g ≤ θ ∧
      θ ≤ 5 * rootShearingLogTime i j g ∧
      ∀ τ ∈ Icc 0 (rootShearingLogTime i j g),
        (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹ =
          Real.exp (4 * rootShearingLogTime i j g) ∨
        (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹ = Real.exp (θ - τ) := by
  obtain ⟨θ, hlo, hhi, hθ⟩ := exists_two_exponential_shearing_regimes
    |g.val j j - g.val i i| (rootShearingMovingSize i j g) (rootShearingLogTime i j g)
    (abs_nonneg _) (rootShearingMovingSize_nonneg i j g)
    (rootShearingLogTime_nonneg hij g hnot hsmall)
    (rootShearingLogTime_normalizes hij g hnot)
  refine ⟨θ, hlo, hhi, ?_⟩
  intro τ hτ
  simpa only [rootShearingKappa_conjugate hij] using hθ τ hτ

end DukePrimeDegree

end

end OAI
