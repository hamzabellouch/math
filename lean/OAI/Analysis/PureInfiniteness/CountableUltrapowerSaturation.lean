import OAI.Analysis.PureInfiniteness.FiniteUltrapowerSaturation

namespace OAI

/-! Countably many polynomial conditions with one uniform norm bound. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace NormUltra

variable {A J : Type*} [NormedAddCommGroup A] [Countable J] [Nonempty J]

theorem bounded_epsilon_test_countable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
    (C : ℝ) (hC : 0 ≤ C) (g : J → ℕ → A → ℝ) (hg : ∀ j k x, 0 ≤ g j k x)
    (hsupply : ∀ F : Finset J, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in (U : Filter ℕ),
      ∃ x : A, ‖x‖ ≤ C ∧ ∀ j ∈ F, g j k x < ε) :
    ∃ x : lp (fun _ : ℕ => A) ∞, (∀ k, ‖x k‖ ≤ C) ∧
      ∀ j, Tendsto (fun k => g j k (x k)) (U : Filter ℕ) (𝓝 0) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat J
  obtain ⟨x, hxn, hx⟩ := bounded_epsilon_test U hfree C hC (fun j => g (e j))
    (fun j => hg (e j)) (fun m ε hε => by
      filter_upwards [hsupply ((Finset.range (m + 1)).image e) ε hε] with k ⟨x, hxn, hx⟩
      refine ⟨x, hxn, fun j hj => hx (e j) ?_⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
  refine ⟨x, hxn, ?_⟩
  intro j
  obtain ⟨i, rfl⟩ := he j
  exact hx i

end NormUltra

end

end OAI
