import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormTraceKernelSigma

namespace OAI

section

noncomputable section
namespace NormUltra
open Filter Topology
open scoped ENNReal

variable {A : Type*} [NormedAddCommGroup A]

theorem bounded_epsilon_test (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
    (C : ℝ) (hC : 0 ≤ C) (g : ℕ → ℕ → A → ℝ)
    (hg : ∀ j k x,0 ≤ g j k x)
    (hsupply : ∀ m : ℕ,∀ ε : ℝ,0<ε → ∀ᶠ k in (U : Filter ℕ),
      ∃ x : A, ‖x‖ ≤ C ∧ ∀ j ≤ m,g j k x<ε) :
    ∃ x : lp (fun _ : ℕ => A) ∞,(∀ k,‖x k‖ ≤ C) ∧
      ∀ j,Tendsto (fun k => g j k (x k)) (U : Filter ℕ) (𝓝 0) := by
  classical
  let ε : ℕ → ℝ := fun m => 1/((m:ℝ)+1)
  have hε (m : ℕ) : 0<ε m := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P : ℕ → ℕ → Prop := fun m k => ∃ x : A,‖x‖ ≤ C ∧ ∀ j ≤ m,g j k x<ε m
  have hP (m : ℕ) : ∀ᶠ k in (U : Filter ℕ),P m k := hsupply m (ε m) (hε m)
  obtain ⟨j,hj,hjP⟩ := NonunitalGamma.kernel_diagonal_choice U hfree P hP
  let y : ℕ → A := fun k => if h : P (j k) k then h.choose else 0
  have hyn (k : ℕ) : ‖y k‖ ≤ C := by
    dsimp [y]
    split_ifs with h
    · exact h.choose_spec.1
    · simpa only [norm_zero] using hC
  let x : lp (fun _ : ℕ => A) ∞ := ⟨y,memℓp_infty ⟨C,by rintro _ ⟨k,rfl⟩; exact hyn k⟩⟩
  refine ⟨x,hyn,?_⟩
  intro i
  apply squeeze_zero' (Eventually.of_forall fun k => hg i k (x k)) _ (hε0.comp hj)
  filter_upwards [hjP,hj (eventually_ge_atTop i)] with k hk hki
  change g i k (y k) ≤ ε (j k)
  dsimp [y]
  rw [dite_eq_left hk]
  exact (hk.choose_spec.2 i hki).le

end NormUltra

end
end

end OAI
