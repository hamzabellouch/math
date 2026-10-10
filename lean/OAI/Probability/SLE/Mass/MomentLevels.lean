import OAI.Probability.SLE.MomentGauge

namespace OAI

/-!
The prescribed retained level in the first paper's moment-batch construction.
Its definition counts bad positive integer levels. Monotonicity makes those
levels an initial segment, so one plus their cardinal is a good level.
The moment convergence hypotheses here are explicit internal proof inputs.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge.Target

theorem batchLevel_ge_one (κ : ℝ) (W : WienerLaw) (n : ℕ) :
    1 ≤ batchLevel κ W n := by
  unfold batchLevel
  omega

theorem finite_bad_moment_levels (κ : ℝ) (W : WienerLaw) (n : ℕ)
    (hm : 0 < moment κ W n)
    (hlim : Tendsto (fun j : ℕ => finiteMoment κ W n j) atTop (𝓝 (moment κ W n))) :
    {j : ℕ | 1 ≤ j ∧ finiteMoment κ W n j ≤ 3 * moment κ W n / 4}.Finite := by
  have hlt : 3 * moment κ W n / 4 < moment κ W n := by linarith
  have hevent : ∀ᶠ j : ℕ in atTop, 3 * moment κ W n / 4 < finiteMoment κ W n j :=
    (tendsto_order.mp hlim).1 _ hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  apply (finite_Iio N).subset
  intro j hj
  show j < N
  by_contra hjN
  exact (not_le_of_gt (hN j (le_of_not_gt hjN))) hj.2

/-- The actual `Target.batchLevel`, not a separately chosen large level,
retains more than three quarters of the limiting moment. -/
theorem finiteMoment_batchLevel_gt (κ : ℝ) (W : WienerLaw) (n : ℕ)
    (hmono : Monotone (fun j : ℕ => finiteMoment κ W n j))
    (hm : 0 < moment κ W n)
    (hlim : Tendsto (fun j : ℕ => finiteMoment κ W n j) atTop (𝓝 (moment κ W n))) :
    3 * moment κ W n / 4 < finiteMoment κ W n (batchLevel κ W n) := by
  classical
  let B := {j : ℕ // 1 ≤ j ∧ finiteMoment κ W n j ≤ 3 * moment κ W n / 4}
  let : Finite B := (finite_bad_moment_levels κ W n hm hlim).to_subtype
  by_contra hbad
  have hbad' : finiteMoment κ W n (batchLevel κ W n) ≤ 3 * moment κ W n / 4 :=
    le_of_not_gt hbad
  let f : Fin (batchLevel κ W n) → B := fun j =>
    ⟨(j : ℕ) + 1, by
      refine ⟨by omega, ?_⟩
      exact (hmono (Nat.succ_le_of_lt j.isLt)).trans hbad'⟩
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Subtype.val hij
    dsimp only [f] at hval
    omega
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_fin] at hcard
  change 1 + Nat.card B ≤ Nat.card B at hcard
  omega

theorem batchLevel_retains_moment (κ : ℝ) (W : WienerLaw) (n : ℕ)
    (hmono : Monotone (fun j : ℕ => finiteMoment κ W n j))
    (hm : 0 < moment κ W n)
    (hlim : Tendsto (fun j : ℕ => finiteMoment κ W n j) atTop (𝓝 (moment κ W n))) :
    1 ≤ batchLevel κ W n ∧
      3 * moment κ W n / 4 < finiteMoment κ W n (batchLevel κ W n) :=
  ⟨batchLevel_ge_one κ W n, finiteMoment_batchLevel_gt κ W n hmono hm hlim⟩

end SLEExactGauge.Target

end

end OAI
