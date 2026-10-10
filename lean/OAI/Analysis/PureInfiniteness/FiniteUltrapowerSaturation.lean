import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerEpsilonTest
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerPositive

namespace OAI

/-! The bounded epsilon test for the finite list of polynomial conditions
used by spectral abelianization, including its norm bound. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace NormUltra

variable {A J : Type*} [NormedAddCommGroup A] [Finite J] [Nonempty J]

theorem bounded_epsilon_test_finite (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
    (C : ℝ) (hC : 0 ≤ C) (g : J → ℕ → A → ℝ) (hg : ∀ j k x, 0 ≤ g j k x)
    (hsupply : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in (U : Filter ℕ),
      ∃ x : A, ‖x‖ ≤ C ∧ ∀ j, g j k x < ε) :
    ∃ x : lp (fun _ : ℕ => A) ∞, (∀ k, ‖x k‖ ≤ C) ∧
      ∀ j, Tendsto (fun k => g j k (x k)) (U : Filter ℕ) (𝓝 0) := by
  obtain ⟨e, he⟩ := exists_surjective_nat J
  obtain ⟨x, hxn, hx⟩ := bounded_epsilon_test U hfree C hC (fun j => g (e j))
    (fun j => hg (e j)) (fun _ ε hε => by
      filter_upwards [hsupply ε hε] with k ⟨x, hxn, hx⟩
      exact ⟨x, hxn, fun j _ => hx (e j)⟩)
  refine ⟨x, hxn, ?_⟩
  intro j
  obtain ⟨i, rfl⟩ := he j
  exact hx i

variable [NonUnitalCStarAlgebra A]

omit [NormedAddCommGroup A] in
theorem norm_mk_le_one_of_defect_tendsto (U : Ultrafilter ℕ)
    (x : BoundedFamilies (fun _ : ℕ => A))
    (h : Tendsto (fun k => max (‖x k‖ - 1) 0) (U : Filter ℕ) (𝓝 0)) :
    ‖QuotientAlgebra.mk U x‖ ≤ 1 := by
  rw [QuotientAlgebra.norm_mk_eq_limsup]
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le (BoundedFamilies.norm_cobounded U x)
  have he := h.eventually (gt_mem_nhds hε)
  filter_upwards [he] with k hk
  have hh := le_max_left (‖x k‖ - 1) 0
  linarith

end NormUltra

end

end OAI
