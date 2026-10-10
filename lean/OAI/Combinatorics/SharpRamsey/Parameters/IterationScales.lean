import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.CostContraction
import OAI.Combinatorics.SharpRamsey.Marking.StageBudget
import OAI.Combinatorics.SharpRamsey.Parameters.ParameterIteration

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

def evenScale (σ η : ℝ) : ℕ:=2*⌈σ^beta η/2⌉₊

lemma evenScale_bounds {σ η : ℝ} (hσ : 0 ≤ σ) :
    σ^beta η ≤ (evenScale σ η:ℝ) ∧
    (evenScale σ η:ℝ) ≤ 2*σ^beta η+2 ∧ Even (evenScale σ η) := by
  have hp : 0 ≤ σ^beta η:=rpow_nonneg hσ _
  have hlo:=Nat.le_ceil (σ^beta η/2)
  have hup:=Nat.ceil_lt_add_one (show 0 ≤ σ^beta η/2 by positivity)
  refine ⟨?_,?_,?_⟩
  · dsimp only [evenScale];push_cast;linarith
  · dsimp only [evenScale];push_cast;linarith
  · exact even_two_mul _

def nextD (σ η D : ℝ) : ℝ:=σ^beta η*(1+D*σ^(-η/3)+16*D*σ^(6*beta η)*σ^(-η))

lemma stage_next {σ η D : ℝ} {k : ℕ} (hk : 0 < k) :
    stageD σ η k (D*σ^(-η/3)*k) (16*scaleKstar σ η D)=nextD σ η D := by
  have hk0 : (k:ℝ)≠0:=by exact_mod_cast hk.ne'
  dsimp only [stageD,nextD,scaleKstar]
  rw [mul_div_cancel_right₀ _ hk0]
  ring

lemma nextD_lower {σ η D : ℝ} (hσ : 0 ≤ σ) (hD : 0 ≤ D) :
    σ^beta η ≤ nextD σ η D := by
  unfold nextD
  have hp : 0 ≤ σ^beta η:=rpow_nonneg hσ _
  have h1 : 0 ≤ D*σ^(-η/3):=by positivity
  have h2 : 0 ≤ 16*D*σ^(6*beta η)*σ^(-η):=by positivity
  nlinarith

theorem eventually_iteration_scales (η : ℝ) (hη : 0 < η) (hηu : η ≤ 1) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, 0 ≤ D →
      nextD σ η D ≤ σ^(2*beta η)+D*σ^(-η/4) ∧
      (D ≤ σ^(1-η/2) → nextD σ η D ≤ σ^(1-η/2)) := by
  have hg1 : beta η-η/3 < -η/4:=by unfold beta;linarith
  have hg2 : 7*beta η-η < -η/4:=by unfold beta;linarith
  have hg3 : 2*beta η < 1-η/2:=by unfold beta;linarith
  filter_upwards [eventually_monomial_le_power 1 (beta η-η/3) (-η/4) (1/2) hg1 (by norm_num),
    eventually_monomial_le_power 16 (7*beta η-η) (-η/4) (1/2) hg2 (by norm_num),
    eventually_monomial_le_power 1 (2*beta η) (1-η/2) (1/2) hg3 (by norm_num),
    eventually_monomial_le_power 1 (1-3*η/4) (1-η/2) (1/2) (by linarith) (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ h1 h2 h3 h4 hσ D hD
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hp : σ^beta η ≤ σ^(2*beta η):=rpow_le_rpow_of_exponent_le hσ (by have:=beta_pos hη;linarith)
  have heq : nextD σ η D=σ^beta η+D*σ^(beta η-η/3)+16*D*σ^(7*beta η-η) := by
    unfold nextD
    rw [mul_add,mul_add]
    simp only [mul_one]
    have hP1 : σ^beta η*σ^(-η/3)=σ^(beta η-η/3):=by rw [←rpow_add hσ0];congr 1;ring
    have hP2 : σ^beta η*σ^(6*beta η)*σ^(-η)=σ^(7*beta η-η):=by
      rw [←rpow_add hσ0,←rpow_add hσ0];congr 1;ring
    calc
      _ = σ^beta η+D*(σ^beta η*σ^(-η/3))+16*D*(σ^beta η*σ^(6*beta η)*σ^(-η)):=by ring
      _ = _:=by rw [hP1,hP2]
  have hrec : nextD σ η D ≤ σ^(2*beta η)+D*σ^(-η/4):=by
    rw [heq]
    have hh1:=mul_le_mul_of_nonneg_left h1 hD
    have hh2:=mul_le_mul_of_nonneg_left h2 hD
    nlinarith only [hp,hh1,hh2]
  refine ⟨hrec,?_⟩
  intro hDu
  have hu : D*σ^(-η/4) ≤ σ^(1-3*η/4):=by
    calc
      _ ≤ σ^(1-η/2)*σ^(-η/4):=mul_le_mul_of_nonneg_right hDu (rpow_nonneg hσ0.le _)
      _ = _:=by rw [←rpow_add hσ0];congr 1;ring
  linarith

theorem eventually_initial_stage (d : ℕ) (η : ℝ) (hη : 0 < η) (hηu : η ≤ 1) :
    ∀ᶠ σ : ℝ in atTop, ∀ k : ℕ,
      Admissible σ η (stageD σ η k 0 (((d-1:ℕ):ℝ)*σ)) (evenScale σ η) ∧
      stageD σ η k 0 (((d-1:ℕ):ℝ)*σ) ≤ σ := by
  have hg1 : beta η < 1-η/2:=by unfold beta;linarith
  have hg2 : 1-η+beta η < 1-η/2:=by unfold beta;linarith
  filter_upwards [eventually_monomial_le_power 1 (beta η) (1-η/2) (1/2) hg1 (by norm_num),
    eventually_monomial_le_power ((d-1:ℕ):ℝ) (1-η+beta η) (1-η/2) (1/2) hg2 (by norm_num),
    eventually_ge_atTop (1:ℝ)] with σ h1 h2 hσ k
  have hσ0 : 0 < σ:=lt_of_lt_of_le zero_lt_one hσ
  have hh : stageD σ η k 0 (((d-1:ℕ):ℝ)*σ)=σ^beta η+((d-1:ℕ):ℝ)*σ^(1-η+beta η):=by
    unfold stageD
    simp only [zero_div,add_zero]
    rw [mul_add,mul_one]
    congr 1
    calc
      _ = ((d-1:ℕ):ℝ)*(σ^beta η*σ^(1:ℝ)*σ^(-η)):=by rw [rpow_one];ring
      _ = _:=by rw [←rpow_add hσ0,←rpow_add hσ0];congr 2;ring
  have hu : stageD σ η k 0 (((d-1:ℕ):ℝ)*σ) ≤ σ^(1-η/2):=by rw [hh];linarith
  obtain ⟨hRl,hRu,hRe⟩:=evenScale_bounds (η:=η) hσ0.le
  refine ⟨⟨?_,hu,hRl,hRu,hRe⟩,hu.trans ?_⟩
  · rw [hh];have : 0 ≤ ((d-1:ℕ):ℝ)*σ^(1-η+beta η):=by positivity
    linarith
  · calc
      _ ≤ σ^(1:ℝ):=rpow_le_rpow_of_exponent_le hσ (by linarith)
      _ = _:=rpow_one _
end
end SharpLogRamsey.SourceScales

end

end OAI
