import OAI.Analysis.CircleDomains.Topology.CircleCutoffFillings
import OAI.Analysis.CircleDomains.Modulus.TerminalOscillation

namespace OAI

/-!
# Actual terminal branches of the transferred circle maps

A real branch on a terminal collar remains a branch after cutoff and
filling. Its boundary oscillation therefore has the stated staircase
bound, even when the completed circle map has no global real lift.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem IsFilledCircleFamily.eventuallyEq_near_set
    {I L : Type*} [Fintype I] [Fintype L] {D : I → Set (ℝ × ℝ)} {Ω A : Set (ℝ × ℝ)}
    {v F : L → (ℝ × ℝ) → UnitAddCircle} (hF : IsFilledCircleFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) (hA : ∀ x ∈ A, ∀ i, x ∉ D i) :
    ∀ᶠ x in 𝓝ˢ A, ∀ l, F l x = v l x := by
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  exact eventually_all.mpr (fun l => hF.eventuallyEq_outside hD (hA x hx) l)

/-- The explicit terminal staircase is a smooth real lift of the actual
transferred circle map on a full neighborhood of the terminal boundary. -/
theorem terminal_staircase_is_actual_branch
    {I : Type*} [Fintype I]
    {D : I → Set (ℝ × ℝ)} (hD : ∀ i, IsOpen (D i))
    {Ω A O : Set (ℝ × ℝ)} (hO : IsOpen O) (hAO : A ⊆ O)
    (hA : ∀ x ∈ A, ∀ i, x ∉ D i)
    (f F : (ℝ × ℝ) → UnitAddCircle) (u χ : (ℝ × ℝ) → ℝ)
    (hu : ContDiffOn ℝ ∞ u O)
    (hproj : ∀ x ∈ O, (u x : UnitAddCircle) = f x)
    (hχone : ∀ x ∈ O, χ x = 1)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : ℝ)
    (hF : IsFilledCircleFamily D Ω
      (fun _ : Unit => circleCutoff f χ (shiftedStaircase (reciprocalGridStep N) δ θ))
      (fun _ => F)) :
    ContDiffOn ℝ ∞ (fun x => shiftedStaircase (reciprocalGridStep N) δ θ (u x)) O ∧
      ∀ᶠ x in 𝓝ˢ A, (shiftedStaircase (reciprocalGridStep N) δ θ (u x) : UnitAddCircle) = F x := by
  have hP (r : ℝ) : shiftedStaircase (reciprocalGridStep N) δ θ (r + 1) =
      shiftedStaircase (reciprocalGridStep N) δ θ r + 1 := by
    simpa only [reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ θ r
  refine ⟨(contDiff_shiftedStaircase (reciprocalGridStep_pos N) hδ hδh θ).comp_contDiffOn hu, ?_⟩
  filter_upwards [hF.eventuallyEq_near_set hD hA, hO.mem_nhdsSet.mpr hAO] with x hx hxO
  have heq := circleCutoff_eq_lift f χ hP (hproj x hxO)
  have hc := cutoffStaircase_of_one (u := u)
    (P := shiftedStaircase (reciprocalGridStep N) δ θ) (hχone x hxO)
  exact (congrArg ((↑) : ℝ → UnitAddCircle) hc).symm.trans (heq.symm.trans (hx ()).symm)

/-- Boundary diameter of the actual chosen real branch. -/
theorem staircase_branch_diameter_le
    {A : Set (ℝ × ℝ)} (u : (ℝ × ℝ) → ℝ) (P : ℝ → ℝ) {a h : ℝ}
    (hbound : 0 ≤ a + 4 * h)
    (hosc : ∀ x ∈ A, ∀ y ∈ A, |P (u x) - P (u y)| ≤ a + 4 * h) :
    Metric.diam ((fun x => P (u x)) '' A) ≤ a + 4 * h := by
  apply Metric.diam_le_of_forall_dist_le hbound
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  simpa only [Real.dist_eq] using hosc p hp q hq

end CircleDomainRigidity.FiniteTransfer

end

end OAI
