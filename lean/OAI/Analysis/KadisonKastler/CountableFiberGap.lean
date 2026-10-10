import OAI.Analysis.KadisonKastler.SequentialConjugacyTests
import OAI.Analysis.KadisonKastler.DenseUnitBallGap

namespace OAI

/-! # A common conull set for the fiber gap estimate

Countably many fiber approximants, with vanishing numerical slack,
bound the full fiber gap. Strong unit-ball density and weak compactness
supply the passage from test fields to arbitrary contractions.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem StrongUnitBallTestSequence.weakUnitBallDense {M : VonNeumannAlgebra H}
    (A : StrongUnitBallTestSequence M) : WeakUnitBallDense A.op M := by
  refine ⟨A.mem, ?_⟩
  intro T hT
  obtain ⟨S, hS, hlim⟩ := A.dense T hT
  choose j hj using hS
  refine ⟨Filter.map j atTop, inferInstance, ?_⟩
  intro x y
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).inner
    (𝕜 := ℂ) (hlim x)
  rw [tendsto_map'_iff]
  convert ht using 1
  funext n
  rw [Function.comp_apply, hj n]

theorem kkDistance_le_of_countable_approximants
    (M N : VonNeumannAlgebra H)
    (A : StrongUnitBallTestSequence M) (B : StrongUnitBallTestSequence N)
    {d : ℝ} (hd : 0 ≤ d)
    (y z : ℕ → ℕ → H →L[ℂ] H)
    (hy : ∀ j k, y j k ∈ unitBall N ∧ ‖A.op j - y j k‖ ≤ d + 1 / (k + 1 : ℝ))
    (hz : ∀ j k, z j k ∈ unitBall M ∧ ‖B.op j - z j k‖ ≤ d + 1 / (k + 1 : ℝ)) :
    kkDistance M N ≤ d := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hk' : 1 / (k + 1 : ℝ) ≤ ε := hk.le
  apply kkDistance_le_of_weakly_dense_tests M N A.op B.op
    A.weakUnitBallDense B.weakUnitBallDense (by positivity)
  · intro j
    exact ⟨y j k, (hy j k).1, (hy j k).2.trans (add_le_add le_rfl hk')⟩
  · intro j
    exact ⟨z j k, (hz j k).1, (hz j k).2.trans (add_le_add le_rfl hk')⟩

theorem ae_kkDistance_le_of_countable_approximants (μ : Measure X)
    (M N : X → VonNeumannAlgebra H)
    (A : ∀ t, StrongUnitBallTestSequence (M t)) (B : ∀ t, StrongUnitBallTestSequence (N t))
    {d : ℝ} (hd : 0 ≤ d)
    (y z : ℕ → ℕ → X → H →L[ℂ] H)
    (hy : ∀ j k, ∀ᵐ t ∂μ, y j k t ∈ unitBall (N t) ∧
      ‖(A t).op j - y j k t‖ ≤ d + 1 / (k + 1 : ℝ))
    (hz : ∀ j k, ∀ᵐ t ∂μ, z j k t ∈ unitBall (M t) ∧
      ‖(B t).op j - z j k t‖ ≤ d + 1 / (k + 1 : ℝ)) :
    ∀ᵐ t ∂μ, kkDistance (M t) (N t) ≤ d := by
  have hyall := ae_all_iff.mpr (fun j => ae_all_iff.mpr (hy j))
  have hzall := ae_all_iff.mpr (fun j => ae_all_iff.mpr (hz j))
  filter_upwards [hyall, hzall] with t ht hs
  exact kkDistance_le_of_countable_approximants (M t) (N t) (A t) (B t) hd
    (fun j k => y j k t) (fun j k => z j k t) ht hs

end

end KadisonKastler

end OAI
