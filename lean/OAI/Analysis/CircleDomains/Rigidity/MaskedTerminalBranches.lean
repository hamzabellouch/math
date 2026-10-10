import OAI.Analysis.CircleDomains.Rigidity.MaskedCircleFillings
import OAI.Analysis.CircleDomains.Topology.CircleTerminalBranches

namespace OAI

/-!
# Actual nonsingular terminal branches and their summed excess

Only the nonsingular terminal subfamily is used for each coordinate.
The real branches project to the filled circle maps on full collars,
and the original band bound gives the required square-sum estimate.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem terminal_staircase_is_actual_masked_branch
    {J : Type*} [Fintype J] {n : ℕ}
    {D : J → Set (ℝ × ℝ)} (hD : ∀ j, IsOpen (D j))
    {Ω A O : Set (ℝ × ℝ)} (hO : IsOpen O) (hAO : A ⊆ O)
    (hA : ∀ x ∈ A, ∀ j, x ∉ D j)
    (M : Fin n → Set (ℝ × ℝ)) (f F : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ u : (ℝ × ℝ) → ℝ) (l : Fin n)
    (hu : ContDiffOn ℝ ∞ u O) (hproj : ∀ x ∈ O, (u x : UnitAddCircle) = f l x)
    (hχone : ∀ x ∈ O, χ x = 1)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : Fin n → ℝ)
    (hF : IsMaskedFilledCircleFamily D Ω M (circleCutoffFamily f χ N δ θ) F) :
    ContDiffOn ℝ ∞ (fun x => shiftedStaircase (reciprocalGridStep N) δ (θ l) (u x)) O ∧
      ∀ᶠ x in 𝓝ˢ A, (shiftedStaircase (reciprocalGridStep N) δ (θ l) (u x) : UnitAddCircle) = F l x := by
  have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ (θ l) (r + 1) =
      shiftedStaircase (reciprocalGridStep N) δ (θ l) r + 1 := by
    simpa only [reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ (θ l) r
  refine ⟨(contDiff_shiftedStaircase (reciprocalGridStep_pos N) hδ hδh (θ l)).comp_contDiffOn hu, ?_⟩
  filter_upwards [hF.2.eventuallyEq_near_set hD hA, hO.mem_nhdsSet.mpr hAO] with x hx hxO
  have heq := circleCutoff_eq_lift (f l) χ hP (hproj x hxO)
  have hc := cutoffStaircase_of_one (u := u)
    (P := shiftedStaircase (reciprocalGridStep N) δ (θ l)) (hχone x hxO)
  exact (congrArg ((↑) : ℝ → UnitAddCircle) hc).symm.trans (heq.symm.trans (hx l).symm)

/-- Directly consume the uniform staircase oscillation supplied by the
physical terminal construction. The width may be selected afterwards. -/
theorem actual_masked_terminal_branches_of_staircase_bound
    {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}
    {D : J → Set (ℝ × ℝ)} (hD : ∀ j, IsOpen (D j))
    {Ω : Set (ℝ × ℝ)} (A O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hAO : ∀ i, A i ⊆ O i) (hAD : ∀ i x, x ∈ A i → ∀ j, x ∉ D j)
    (M : Fin n → Set (ℝ × ℝ)) (f F : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (u : I → Fin n → (ℝ × ℝ) → ℝ)
    (S : Fin n → Finset I) (a : I → Fin n → ℝ)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ l i, i ∈ S l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (N : ℕ) {δ η : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : Fin n → ℝ)
    (hF : IsMaskedFilledCircleFamily D Ω M (circleCutoffFamily f χ N δ θ) F)
    (ha : ∀ l i, i ∈ S l → 0 ≤ a i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ A i, ∀ y ∈ A i,
      |shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l x) -
        shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l y)| ≤
          a i l + 4 * reciprocalGridStep N)
    (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ w : I → Fin n → (ℝ × ℝ) → ℝ,
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (O i) ∧
        ∀ᶠ x in 𝓝ˢ (A i), (w i l x : UnitAddCircle) = F l x) ∧
      ∀ l, Real.sqrt (∑ i ∈ S l, max (Metric.diam (w i l '' A i) - a i l) 0 ^ 2) < 4 * η := by
  classical
  let w : I → Fin n → (ℝ × ℝ) → ℝ := fun i l x =>
    shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l x)
  refine ⟨w, ?_, ?_⟩
  · intro l i hi
    exact terminal_staircase_is_actual_masked_branch hD (hO i) (hAO i) (hAD i)
      M f F χ (u i l) l (hu l i hi) (hproj l i hi) (hχone i) N hδ hδh θ hF
  · intro l
    have hd (i : I) (hi : i ∈ S l) : Metric.diam (w i l '' A i) ≤ a i l + 4 * reciprocalGridStep N :=
      staircase_branch_diameter_le (u i l) (shiftedStaircase (reciprocalGridStep N) δ (θ l))
        (by positivity [ha l i hi, reciprocalGridStep_pos N]) (hbound l i hi)
    exact sqrt_sum_terminal_excess_sq_lt (S l) Finset.univ (Finset.subset_univ _)
      (fun i => Metric.diam (w i l '' A i)) (fun i => a i l)
      (le_of_lt (reciprocalGridStep_pos N)) hd
      (by simpa only [Finset.card_univ] using hsmall)

theorem actual_masked_terminal_branches_and_excess
    {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}
    {D : J → Set (ℝ × ℝ)} (hD : ∀ j, IsOpen (D j))
    {Ω : Set (ℝ × ℝ)} (A O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hAO : ∀ i, A i ⊆ O i) (hAD : ∀ i x, x ∈ A i → ∀ j, x ∉ D j)
    (M : Fin n → Set (ℝ × ℝ)) (f F : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (u : I → Fin n → (ℝ × ℝ) → ℝ)
    (S : Fin n → Finset I) (a : I → Fin n → ℝ)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ l i, i ∈ S l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (N : ℕ) {δ η : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : Fin n → ℝ)
    (hF : IsMaskedFilledCircleFamily D Ω M (circleCutoffFamily f χ N δ θ) F)
    (ha : ∀ l i, i ∈ S l → 0 ≤ a i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ A i, ∀ y ∈ A i,
      |u i l x - u i l y| ≤ a i l + 2 * reciprocalGridStep N)
    (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ w : I → Fin n → (ℝ × ℝ) → ℝ,
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (O i) ∧
        ∀ᶠ x in 𝓝ˢ (A i), (w i l x : UnitAddCircle) = F l x) ∧
      ∀ l, Real.sqrt (∑ i ∈ S l, max (Metric.diam (w i l '' A i) - a i l) 0 ^ 2) < 4 * η := by
  classical
  let w : I → Fin n → (ℝ × ℝ) → ℝ := fun i l x =>
    shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l x)
  refine ⟨w, ?_, ?_⟩
  · intro l i hi
    exact terminal_staircase_is_actual_masked_branch hD (hO i) (hAO i) (hAD i)
      M f F χ (u i l) l (hu l i hi) (hproj l i hi) (hχone i) N hδ hδh θ hF
  · intro l
    have hd (i : I) (hi : i ∈ S l) : Metric.diam (w i l '' A i) ≤ a i l + 4 * reciprocalGridStep N := by
      apply staircase_branch_diameter_le (u i l)
        (shiftedStaircase (reciprocalGridStep N) δ (θ l))
        (by positivity [ha l i hi, reciprocalGridStep_pos N])
      intro x hx y hy
      have hpx := abs_le.mp (abs_shiftedStaircase_sub_le (reciprocalGridStep_pos N) δ (θ l) (u i l x))
      have hpy := abs_le.mp (abs_shiftedStaircase_sub_le (reciprocalGridStep_pos N) δ (θ l) (u i l y))
      have hxy := abs_le.mp (hbound l i hi x hx y hy)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact sqrt_sum_terminal_excess_sq_lt (S l) Finset.univ (Finset.subset_univ _)
      (fun i => Metric.diam (w i l '' A i)) (fun i => a i l)
      (le_of_lt (reciprocalGridStep_pos N)) hd
      (by simpa only [Finset.card_univ] using hsmall)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
