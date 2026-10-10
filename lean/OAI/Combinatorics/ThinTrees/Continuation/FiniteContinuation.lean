import Mathlib
import OAI.Combinatorics.ThinTrees.Flow.Interior

namespace OAI

/-! Finite continuation. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions Orientations
open scoped Classical MatrixOrder Matrix.Norms.Elementwise
variable {n m : ℕ}

def finiteStep (H : MultiGraph n m) (s κ t qbar ε : ℝ) (u : Fin m → ℝ)
    (x : StepFree n m) (F : FlowPoint n m) : Prop :=
  x ∈ stepCore H s κ t u ∧ F.Feasible H (x.capacities κ u) qbar ε

lemma finiteStep_sound (H : MultiGraph n m) (hn : 0 < n)
    {s κ t qbar ε : ℝ} {u : Fin m → ℝ} {x : StepFree n m} {F : FlowPoint n m}
    (hε : 0 ≤ ε) (h : finiteStep H s κ t qbar ε u x F) :
    x ∈ stepFeasible H s κ t (qbar-4*ε) u := by
  refine ⟨h.1,?_⟩
  apply relaxed_flow_implies_partitions H hn (x.capacities κ u) hε
  simpa only [sub_add_cancel] using h.2

lemma interior_capacities_lower (H : MultiGraph n m) {s κ t ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρκ : ρ ≤ κ) (u : Fin m → ℝ) (c : StepFree n m)
    (h : ∀x : StepFree n m, x.Close c ρ → x ∈ stepCore H s κ t u) :
    ∀e, ρ ≤ c.capacities κ u e := by
  let w : StepFree n m := (c.1,c.multiplier,c.y,fun e => c.z e-ρ)
  have hw : w.Close c ρ := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i j
      simpa only [w,sub_self,abs_zero] using hρ
    · intro ijk
      simpa only [w,StepFree.multiplier,sub_self,abs_zero] using hρ
    · intro e
      simpa only [w,StepFree.y,sub_self,abs_zero] using hρ
    · intro e
      change |c.z e-ρ-c.z e| ≤ ρ
      rw [show c.z e-ρ-c.z e = -ρ by ring,abs_neg,abs_of_nonneg hρ]
  have hwc := h w hw
  intro e
  unfold StepFree.capacities
  split_ifs
  · have he := (hwc.2.2.2.2.1 e).1
    change 0 ≤ c.z e-ρ at he
    linarith only [he]
  · exact hρκ

lemma finite_interior_numbers {P β : ℝ} (hP : 5 ≤ P)
    (hn : (n:ℝ) ≤ P) (hm : (m:ℝ) ≤ P) (hβ : P⁻¹/32 ≤ β) :
    let ε := P^(-10:ℤ)
    let α := P^(-12:ℤ)
    let γ := P^(-45:ℤ)
    let ρ := P^(-30:ℤ)
    let δ := P^(-50:ℤ)
    0 < β ∧ α ≤ ε ∧ α*((n:ℝ)-1) ≤ ε ∧
      4*m*γ ≤ α ∧ 4*m*γ ≤ β ∧ 2*γ ≤ ρ ∧
      δ ≤ ρ ∧ δ ≤ γ/4 ∧ γ ≤ 1 ∧ ρ ≤ P⁻¹ := by
  dsimp only
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hP2 : 25 ≤ P^2 := by nlinarith only [hP,sq_nonneg (P-5)]
  have hpw {a b : ℕ} (hab : a ≤ b) : P^a ≤ P^b := pow_le_pow_right₀ hP1 hab
  have h4 : (4:ℝ) ≤ P^5 := (by linarith : (4:ℝ) ≤ P).trans (by simpa using hpw (by norm_num : 1 ≤ 5))
  have h32 : (32:ℝ) ≤ P^11 := by
    have hh : 32 ≤ P^4 := by nlinarith only [hP2,sq_nonneg (P^2-25)]
    exact hh.trans (hpw (by norm_num))
  have hnm : (n:ℝ)-1 ≤ P^2 := calc
    _ ≤ P := by linarith only [hn]
    _ ≤ P^2 := by simpa using hpw (by norm_num : 1 ≤ 2)
  have hnα := scaled_inverse_power hP0 10 2 hnm
  have hm4 : 4*(m:ℝ) ≤ P^33 := calc
    _ ≤ 4*P := by linarith only [hm]
    _ ≤ P^2 := by nlinarith only [hP]
    _ ≤ P^33 := hpw (by norm_num)
  have hmγ := scaled_inverse_power hP0 12 33 hm4
  have hαβ : P^(-12:ℤ) ≤ β := by
    have hh := scaled_inverse_power hP0 1 11 h32
    norm_num only [Nat.cast_ofNat,Nat.reduceAdd,_root_.zpow_neg_one] at hh
    linarith only [hh,hβ]
  have hgρ := scaled_inverse_power hP0 30 15
    (show (2:ℝ) ≤ P^15 from (by linarith : (2:ℝ) ≤ P).trans (by simpa using hpw (by norm_num : 1 ≤ 15)))
  have hdg := scaled_inverse_power hP0 45 5 h4
  norm_num only [Nat.cast_ofNat,Nat.reduceAdd] at hnα hmγ hgρ hdg
  have hβ0 : 0 < β := (by positivity : (0:ℝ) < P⁻¹/32).trans_le hβ
  refine ⟨hβ0,inverse_power_mono hP1 (by norm_num : 10 ≤ 12),?_,?_,?_,?_,
    inverse_power_mono hP1 (by norm_num : 30 ≤ 50),?_,?_,?_⟩
  · simpa only [Nat.cast_ofNat,mul_comm] using hnα
  · simpa only [Nat.cast_ofNat,mul_assoc] using hmγ
  · exact hmγ.trans hαβ
  · simpa only [Nat.cast_ofNat] using hgρ
  · simpa only [Nat.cast_ofNat] using (show P^(-50:ℤ) ≤ P^(-45:ℤ)/4 by linarith only [hdg])
  · simpa using inverse_power_mono hP1 (by norm_num : 0 ≤ 45)
  · simpa using inverse_power_mono hP1 (by norm_num : 1 ≤ 30)

theorem finite_continuation_inner_cube (H : MultiGraph n m) (hn : 2 ≤ n)
    (hconn : H.Connected univ) {s qbar β : ℝ}
    (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (hq : (graphSize n m)^(-12:ℤ) ≤ qbar) (hqm : qbar+β ≤ m)
    (hβ : (graphSize n m)⁻¹/32 ≤ β)
    (u : Fin m → ℝ) (hu : ∀e, 0 ≤ u e) {z : StepFree n m}
    (hz : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) (qbar+β+β) u) :
    ∃(c : StepFree n m) (F : FlowPoint n m),
      c.Bounded (6*graphSize n m) ∧ F.Bounded (6*graphSize n m) ∧
      ∀(x : StepFree n m) (W : FlowPoint n m),
        x.Close c ((graphSize n m)^(-50:ℤ)) →
        W.Close F ((graphSize n m)^(-50:ℤ)) →
        finiteStep H s (continuationBaseline m) (continuationStep m) qbar
          ((graphSize n m)^(-10:ℤ)) u x W := by
  let P := graphSize n m
  have hP : 5 ≤ P := connected_size_five H hn hconn
  have hP0 : 0 < P := by linarith only [hP]
  have hnP : (n:ℝ) ≤ P := by unfold P graphSize; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hmP : (m:ℝ) ≤ P := by unfold P graphSize; linarith [Nat.cast_nonneg (α:=ℝ) n]
  obtain ⟨hβ0,hαε,hαn,hmγα,hmγβ,hgρ,hdρ,hdγ,hγ1,hρP⟩ :=
    finite_interior_numbers hP hnP hmP hβ
  have hγ0 : (0:ℝ) < P^(-45:ℤ) := zpow_pos hP0 _
  have hα0 : (0:ℝ) ≤ P^(-12:ℤ) := (zpow_pos hP0 _).le
  obtain ⟨c,hc,hball⟩ := bounded_step_inner_cube H hn hconn hs hsP hqm hβ u hu hz
  have hρ0 : (0:ℝ) ≤ P^(-30:ℤ) := (zpow_pos hP0 _).le
  have hcself := hball c (StepFree.Close.refl c hρ0)
  have hcap := interior_capacities_lower H hρ0 (hρP.trans baseline_lower) u c
    (fun x hx => (hball x hx).1)
  have hcR : ∀e, c.capacities (continuationBaseline m) u e ≤ 2 := by
    intro e
    unfold StepFree.capacities
    split_ifs
    · exact (hcself.1.2.2.2.2.1 e).2.trans (by linarith only [baseline_le_one (m:=m)])
    · exact baseline_le_one.trans (by norm_num)
  obtain ⟨F,hF,hFball⟩ := flow_inner_cube_vary H (by omega) (c.capacities (continuationBaseline m) u)
    hγ0 hα0 hq hαε hαn hβ0 hmγα hmγβ (fun e => hgρ.trans (hcap e)) hcR
    (fun p => by have hh := hcself.2 p; unfold slack at hh; linarith only [hh])
  refine ⟨c,F,hc,hF.mono ?_,?_⟩
  · linarith only [hγ1,hP]
  · intro x W hx hW
    refine ⟨(hball x (hx.mono hdρ)).1,hFball (x.capacities (continuationBaseline m) u) W ?_ (hW.mono hdγ)⟩
    intro e
    unfold StepFree.capacities
    split_ifs
    · have hh := (abs_le.mp (hx.2.2.2 e)).1
      change -(P^(-50:ℤ)) ≤ x.z e-c.z e at hh
      linarith only [hh,hdγ,hγ0]
    · linarith only [hγ0]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
