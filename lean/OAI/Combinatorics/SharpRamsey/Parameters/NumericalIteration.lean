import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.IterationScales

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

def iterationBudgets (d : ℕ) (σ η : ℝ) (k : ℕ) : ℕ→ℝ×ℝ
  | 0 => (0,((d-1:ℕ):ℝ)*σ)
  | n+1 => let b:=iterationBudgets d σ η k n
           let D:=stageD σ η k b.1 b.2
           (D*σ^(-η/3)*k,16*scaleKstar σ η D)

def iterationD (d : ℕ) (σ η : ℝ) (k n : ℕ) : ℝ:=
  stageD σ η k (iterationBudgets d σ η k n).1 (iterationBudgets d σ η k n).2

lemma iterationD_succ (d : ℕ) (σ η : ℝ) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    iterationD d σ η k (n+1)=nextD σ η (iterationD d σ η k n) := by
  exact stage_next hk

lemma iteration_data {d k : ℕ} {σ η : ℝ} (hk : 0 < k) (hσ : 1 ≤ σ)
    (hinit : Admissible σ η (iterationD d σ η k 0) (evenScale σ η))
    (hiter : ∀ D : ℝ,0 ≤ D→nextD σ η D ≤ σ^(2*beta η)+D*σ^(-η/4) ∧
      (D ≤ σ^(1-η/2)→nextD σ η D ≤ σ^(1-η/2))) :
    ∀ n, 0 ≤ (iterationBudgets d σ η k n).1 ∧ 0 ≤ (iterationBudgets d σ η k n).2 ∧
      Admissible σ η (iterationD d σ η k n) (evenScale σ η) := by
  have hσ0 : 0 ≤ σ:=by linarith
  intro n
  induction n with
  | zero => exact ⟨le_refl 0,mul_nonneg (Nat.cast_nonneg _) hσ0,hinit⟩
  | succ n ih =>
    have hD : 0 ≤ iterationD d σ η k n:=(rpow_nonneg hσ0 _).trans ih.2.2.1
    obtain ⟨hlo,hup,hev⟩:=evenScale_bounds (η:=η) hσ0
    refine ⟨?_,?_,?_⟩
    · change 0 ≤ iterationD d σ η k n*σ^(-η/3)*(k:ℝ)
      positivity
    · change 0 ≤ 16*scaleKstar σ η (iterationD d σ η k n)
      unfold scaleKstar;positivity
    · rw [iterationD_succ d σ η hk]
      exact ⟨nextD_lower hσ0 hD,(hiter _ hD).2 ih.2.2.D_upper,hlo,hup,hev⟩

theorem eventually_iteration_budgets (d : ℕ) (η : ℝ) (hη : 0 < η) (hηu : η ≤ 1) :
    ∀ᶠ σ : ℝ in atTop, ∀ k : ℕ,0 < k→
      (∀ n,0 ≤ (iterationBudgets d σ η k n).1 ∧ 0 ≤ (iterationBudgets d σ η k n).2 ∧
        Admissible σ η (iterationD d σ η k n) (evenScale σ η)) ∧
      (iterationBudgets d σ η k (⌈8/η⌉₊+1)).1 ≤ k ∧
      (iterationBudgets d σ η k (⌈8/η⌉₊+1)).2 ≤ 48*σ^(8*beta η) := by
  have hg : 2*beta η-η/3 < 0:=by unfold beta;linarith
  filter_upwards [eventually_initial_stage d η hη hηu,eventually_iteration_scales η hη hηu,
    ParameterIteration.eventual_half hη,
    eventually_monomial_le_power 3 (2*beta η-η/3) 0 1 hg (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ hinit hiter hhalf hsmall hσ k hk
  have hσ0 : 0 < σ:=by linarith
  have hdata:=iteration_data hk hσ (hinit k).1 hiter
  let T:=⌈8/η⌉₊
  have hD : iterationD d σ η k T ≤ 3*σ^(2*beta η):=by
    apply ParameterIteration.source_contraction hσ (beta_pos hη).le hhalf _ T
      (ParameterIteration.prescribed_count hη) (hinit k).2
    intro n _
    rw [iterationD_succ d σ η hk]
    exact (hiter _ ((rpow_nonneg hσ0.le _).trans (hdata n).2.2.1)).1
  refine ⟨hdata,?_,?_⟩
  · change iterationD d σ η k T*σ^(-η/3)*(k:ℝ) ≤ k
    have hh : iterationD d σ η k T*σ^(-η/3) ≤ 1:=by
      calc
        _ ≤ 3*σ^(2*beta η)*σ^(-η/3):=mul_le_mul_of_nonneg_right hD (rpow_nonneg hσ0.le _)
        _ = 3*σ^(2*beta η-η/3):=by rw [mul_assoc,←rpow_add hσ0];congr 2;ring
        _ ≤ 1:=by simpa using hsmall
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg k)
  · change 16*scaleKstar σ η (iterationD d σ η k T) ≤ _
    unfold scaleKstar
    calc
      _ ≤ 16*(3*σ^(2*beta η))*σ^(6*beta η):=by
        have hh:=mul_le_mul_of_nonneg_right hD (rpow_nonneg hσ0.le (6*beta η))
        have hh':=mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 16)
        simpa only [mul_assoc] using hh'
      _ = _:=by rw [show 16*(3*σ^(2*beta η))*σ^(6*beta η)=48*(σ^(2*beta η)*σ^(6*beta η)) by ring,←rpow_add hσ0];congr 2;ring
end
end SharpLogRamsey.SourceScales

end

end OAI
