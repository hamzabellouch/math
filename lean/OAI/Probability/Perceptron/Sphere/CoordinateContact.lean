import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SphericalPerceptronFreeEnergy

lemma box_comparison_continuous {I : Type*} [Fintype I]
    {F : (I → ℝ) → ℝ} {L : I → ℝ} (hL : ∀ i, 0 ≤ L i) {a b : ℝ}
    (hcomp : ∀ u ∈ Icc (fun _ : I => a) (fun _ => b),
      ∀ v ∈ Icc (fun _ : I => a) (fun _ => b),
      |F v-F u| ≤ ∑ i, L i*|v i-u i|) :
    ContinuousOn F (Icc (fun _ : I => a) (fun _ => b)) := by
  have hsum : 0 ≤ ∑ i, L i := Finset.sum_nonneg fun i _ => hL i
  apply (LipschitzOnWith.of_dist_le_mul (K := ⟨∑ i, L i,hsum⟩) ?_).continuousOn
  intro u hu v hv
  change |F u-F v| ≤ (∑ i, L i)*‖u-v‖
  apply (hcomp v hv u hu).trans
  calc
    _ ≤ ∑ i, L i*‖u-v‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hL i)
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (u-v) i
    _ = _ := by rw [Finset.sum_mul]

def quadraticBoxPenalty {I : Type*} [Fintype I] (c u : I → ℝ) : ℝ :=
  ∑ i, c i*(u i-3/2)^2

lemma quadraticBoxPenalty_continuous {I : Type*} [Fintype I] (c : I → ℝ) :
    Continuous (quadraticBoxPenalty c) := by
  unfold quadraticBoxPenalty
  fun_prop

lemma exists_quadratic_box_min {I : Type*} [Fintype I] (F : (I → ℝ) → ℝ) (c : I → ℝ)
    (hF : ContinuousOn F (Icc (fun _ : I => 1) (fun _ => 2))) :
    ∃ u ∈ Icc (fun _ : I => 1) (fun _ => 2),
      IsMinOn (fun v => quadraticBoxPenalty c v-F v)
        (Icc (fun _ : I => 1) (fun _ => 2)) u := by
  refine isCompact_Icc.exists_isMinOn ?_ ((quadraticBoxPenalty_continuous c).continuousOn.sub hF)
  exact ⟨fun _ => 3/2,by constructor <;> intro i <;> norm_num⟩

lemma quadratic_box_min_penalty {I : Type*} [Fintype I]
    {F : (I → ℝ) → ℝ} {c u : I → ℝ} {ε : ℝ}
    (hmin : IsMinOn (fun v => quadraticBoxPenalty c v-F v)
      (Icc (fun _ : I => 1) (fun _ => 2)) u)
    (hcomp : |F u-F (fun _ => 3/2)| ≤ ε) :
    quadraticBoxPenalty c u ≤ ε := by
  have hm : quadraticBoxPenalty c u-F u ≤ quadraticBoxPenalty c (fun _ => 3/2)-F (fun _ => 3/2) :=
    hmin (show (fun _ : I => (3/2:ℝ)) ∈ Icc (fun _ => 1) (fun _ => 2) from
      by constructor <;> intro i <;> norm_num)
  have hc : quadraticBoxPenalty c (fun _ : I => 3/2)=0 := by simp [quadraticBoxPenalty]
  rw [hc] at hm
  linarith [le_abs_self (F u-F (fun _ => 3/2))]

lemma quadratic_box_min_coord {I : Type*} [Fintype I]
    {F : (I → ℝ) → ℝ} {c u : I → ℝ} {ε : ℝ} (hc : ∀ i, 0 ≤ c i)
    (hmin : IsMinOn (fun v => quadraticBoxPenalty c v-F v)
      (Icc (fun _ : I => 1) (fun _ => 2)) u)
    (hcomp : |F u-F (fun _ => 3/2)| ≤ ε) (j : I) :
    c j*(u j-3/2)^2 ≤ ε := by
  have hj : c j*(u j-3/2)^2 ≤ quadraticBoxPenalty c u :=
    Finset.single_le_sum (s := Finset.univ) (f := fun i => c i*(u i-3/2)^2)
      (fun i _ => mul_nonneg (hc i) (sq_nonneg _)) (Finset.mem_univ j)
  exact hj.trans (quadratic_box_min_penalty hmin hcomp)

lemma quadraticBoxPenalty_single {I : Type*} [Fintype I] [DecidableEq I]
    (c u : I → ℝ) (j : I) (r : ℝ) :
    quadraticBoxPenalty c (u+Pi.single j r) = quadraticBoxPenalty c u+
      c j*(r^2+2*(u j-3/2)*r) := by
  unfold quadraticBoxPenalty
  calc
    _ = ∑ i, (c i*(u i-3/2)^2+if i=j then c j*(r^2+2*(u j-3/2)*r) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : i=j
      · subst i; simp; ring
      · simp [hij]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

lemma quadratic_box_min_direction {I : Type*} [Fintype I] [DecidableEq I]
    {F : (I → ℝ) → ℝ} {c u : I → ℝ}
    (hmin : IsMinOn (fun v => quadraticBoxPenalty c v-F v)
      (Icc (fun _ : I => 1) (fun _ => 2)) u)
    (j : I) (r : ℝ) (hr : u+Pi.single j r ∈ Icc (fun _ : I => 1) (fun _ => 2)) :
    c j*(0-(3/2-u j))^2-F u ≤
      c j*(r-(3/2-u j))^2-F (u+Pi.single j r) := by
  have hm : quadraticBoxPenalty c u-F u ≤ quadraticBoxPenalty c (u+Pi.single j r)-F (u+Pi.single j r) := hmin hr
  rw [quadraticBoxPenalty_single] at hm
  nlinarith

lemma quadratic_box_min_local_direction {I : Type*} [Fintype I] [DecidableEq I]
    {F : (I → ℝ) → ℝ} {c u : I → ℝ}
    (hu : u ∈ Icc (fun _ : I => 1) (fun _ => 2))
    (hmin : IsMinOn (fun v => quadraticBoxPenalty c v-F v)
      (Icc (fun _ : I => 1) (fun _ => 2)) u)
    (j : I) (hj : u j ∈ Ioo 1 2) :
    IsLocalMin (fun r => c j*(r-(3/2-u j))^2-F (u+Pi.single j r)) 0 := by
  have hnb : Icc (1-u j) (2-u j) ∈ 𝓝 (0:ℝ) := Icc_mem_nhds (by linarith [hj.1]) (by linarith [hj.2])
  apply Filter.Eventually.mono hnb
  intro r hr
  have hub : u+Pi.single j r ∈ Icc (fun _ : I => 1) (fun _ => 2) := by
    constructor <;> intro i
    · by_cases hi : i=j
      · subst i; simp only [Pi.add_apply,Pi.single_eq_same]; linarith [hr.1]
      · simpa [Pi.single_eq_of_ne hi] using hu.1 i
    · by_cases hi : i=j
      · subst i; simp only [Pi.add_apply,Pi.single_eq_same]; linarith [hr.2]
      · simpa [Pi.single_eq_of_ne hi] using hu.2 i
  simpa using quadratic_box_min_direction hmin j r hub

end SphericalPerceptronFreeEnergy
end

end OAI
