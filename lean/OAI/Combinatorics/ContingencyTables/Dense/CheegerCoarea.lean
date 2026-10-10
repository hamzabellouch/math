import OAI.Combinatorics.ContingencyTables.Dense.PublishedCheeger
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # Weighted finite coarea for the published Cheeger input -/
namespace ContingencyTables.CheegerProof
open MeasureTheory CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

def level (a t : ℝ) : ℝ := if 0 ≤ t ∧ t < a then 1 else 0

lemma level_eq (a : ℝ) :
    level a = Set.indicator (Set.Ico 0 a) (fun _ => (1:ℝ)) := by
  funext t
  simp [level,Set.indicator_apply,Set.mem_Ico]

lemma level_integrable (a : ℝ) : Integrable (level a) := by
  rw [level_eq]
  exact (integrableOn_const (isCompact_Icc.measure_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc 0 a)).mono_set
      Set.Ico_subset_Icc_self |>.integrable_indicator measurableSet_Ico

lemma level_integral {a : ℝ} (ha : 0 ≤ a) : ∫ t, level a t = a := by
  rw [level_eq,integral_indicator measurableSet_Ico]
  simp [ha]

lemma level_abs_sub (a b t : ℝ) :
    |level a t-level b t| = level a t+level b t-2*level (min a b) t := by
  simp only [level,lt_min_iff]
  by_cases h₀ : 0 ≤ t <;> by_cases ha : t < a <;> by_cases hb : t < b <;>
    norm_num [h₀,ha,hb]

lemma level_abs_integrable (a b : ℝ) : Integrable (fun t => |level a t-level b t|) :=
  ((level_integrable a).sub (level_integrable b)).abs

lemma level_abs_integral {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ t, |level a t-level b t| = |a-b| := by
  simp_rw [level_abs_sub]
  rw [integral_sub (f := fun t => level a t+level b t)
      ((level_integrable a).add (level_integrable b))
      ((level_integrable (min a b)).const_mul 2),
    integral_add (level_integrable a) (level_integrable b),integral_const_mul,
    level_integral ha,level_integral hb,level_integral (le_min ha hb)]
  rcases le_total a b with h | h
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring

variable {X : Type*} [Fintype X] (C : FiniteChain X)

def mass (S : Finset X) : ℝ := ∑ x ∈ S, C.π x
def cut (S : Finset X) : ℝ := ∑ x ∈ S, ∑ y ∈ Sᶜ, C.π x*C.P x y

lemma mass_nonneg (S : Finset X) : 0 ≤ mass C S :=
  Finset.sum_nonneg fun x _ => (C.positive x).le

lemma mass_mono {S T : Finset X} (h : S ⊆ T) : mass C S ≤ mass C T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => (C.positive x).le)

lemma mass_compl (S : Finset X) : mass C Sᶜ = 1-mass C S := by
  have h := Finset.sum_compl_add_sum S C.π
  rw [C.normalized] at h
  dsimp [mass]
  linarith

lemma cut_indicator (S : Finset X) :
    (∑ x, ∑ y, C.π x*C.P x y*
      |(if x ∈ S then (1:ℝ) else 0)-(if y ∈ S then (1:ℝ) else 0)|) = 2*cut C S := by
  have hs (x y : X) : C.π x*C.P x y*
      |(if x ∈ S then (1:ℝ) else 0)-(if y ∈ S then (1:ℝ) else 0)| =
      (if x ∈ S ∧ y ∉ S then C.π x*C.P x y else 0)+
      (if y ∈ S ∧ x ∉ S then C.π x*C.P x y else 0) := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx,hy]
  simp_rw [hs,Finset.sum_add_distrib]
  have hforward : (∑ x, ∑ y, if x ∈ S ∧ y ∉ S then C.π x*C.P x y else 0) = cut C S := by
    simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_filter]
    congr 1
    ext y
    simp
  have hback : (∑ x, ∑ y, if y ∈ S ∧ x ∉ S then C.π x*C.P x y else 0) = cut C S := by
    rw [Finset.sum_comm]
    simpa only [C.reversible] using hforward
  rw [hforward,hback]
  ring

/-- Coarea on a function supported on a set of stationary mass at most one half. -/
theorem coarea (κ : ℝ)
    (hcut : ∀ S : Finset X, κ*min (mass C S) (mass C Sᶜ) ≤ cut C S)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hsmall : mass C (Finset.univ.filter fun x => 0 < g x) ≤ 1/2) :
    2*κ*(∑ x, C.π x*g x) ≤ ∑ x, ∑ y, C.π x*C.P x y*|g x-g y| := by
  let F : ℝ → ℝ := fun t => 2*κ*∑ x, C.π x*level (g x) t
  let J : ℝ → ℝ := fun t => ∑ x, ∑ y, C.π x*C.P x y*|level (g x) t-level (g y) t|
  have hF : Integrable F :=
    (integrable_finsetSum _ (fun x _ => (level_integrable (g x)).const_mul (C.π x))).const_mul _
  have hJ : Integrable J := integrable_finsetSum _ fun x _ =>
    integrable_finsetSum _ fun y _ => (level_abs_integrable (g x) (g y)).const_mul _
  have hle (t : ℝ) : F t ≤ J t := by
    let S := Finset.univ.filter fun x => 0 ≤ t ∧ t < g x
    have hi (x : X) : level (g x) t = if x ∈ S then 1 else 0 := by simp [level,S]
    have hm : mass C S ≤ 1/2 := (mass_mono C (by
      intro x hx
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx.1.trans_lt hx.2⟩)).trans hsmall
    have hc := hcut S
    rw [mass_compl,min_eq_left (by linarith : mass C S ≤ 1-mass C S)] at hc
    have hl : (∑ x, C.π x*level (g x) t) = mass C S := by
      simp only [hi,mul_ite,mul_one,mul_zero,mass]
      rw [← Finset.sum_filter]
      simp
    dsimp [F,J]
    rw [hl]
    simp only [hi,cut_indicator]
    linarith
  have H := integral_mono hF hJ hle
  dsimp [F,J] at H
  rw [integral_const_mul,integral_finsetSum _ (fun x _ => (level_integrable (g x)).const_mul _)] at H
  simp_rw [integral_const_mul,level_integral (hg _)] at H
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _
    (fun y _ => (level_abs_integrable (g x) (g y)).const_mul _))] at H
  simp_rw [integral_finsetSum _ (fun y _ => (level_abs_integrable _ _).const_mul _),
    integral_const_mul,level_abs_integral (hg _) (hg _)] at H
  exact H

end
end ContingencyTables.CheegerProof

end OAI
