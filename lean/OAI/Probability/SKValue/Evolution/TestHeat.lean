import Mathlib
import OAI.Probability.SKValue.Evolution.HeatDuality

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma linear_derivative_tower_bounded {ι : Type*} (S : ℕ → ι → ℝ → ℝ)
    (b : ι → ℝ → ℝ) (hs : ∀ j a,ContDiff ℝ ∞ (S j a))
    (hbs : ∀ a,ContDiff ℝ ∞ (b a))
    (hd : ∀ j a,deriv (S j a)=fun x ↦ S (j+1) a x-S j a x*b a x)
    (hb : ∀ j,∃ C:ℝ,0≤C ∧ ∀ a x,|S j a x|≤C)
    (hbb : ∀ n,∃ C:ℝ,0≤C ∧ ∀ a x,|iteratedDeriv n (b a) x|≤C) :
    ∀ n j:ℕ,∃ C:ℝ,0≤C ∧ ∀ a x,|iteratedDeriv n (S j a) x|≤C := by
  classical
  choose B hB hbB using hbb
  intro n
  induction n using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => intro j;simpa only [iteratedDeriv_zero] using hb j
    | succ n =>
      have hlo : ∀ k j:ℕ,∃ C:ℝ,0≤C ∧
          (k≤n → ∀ a x,|iteratedDeriv k (S j a) x|≤C) := by
        intro k j
        by_cases hk:k≤n
        · obtain ⟨C,hC,hbC⟩ := ih k (Nat.lt_succ_of_le hk) j
          exact ⟨C,hC,fun _ ↦ hbC⟩
        · exact ⟨0,le_rfl,fun h ↦ (hk h).elim⟩
      choose C hC hbound using hlo
      intro j
      refine ⟨C n (j+1)+∑ k∈Finset.range (n+1),(n.choose k:ℝ)*C k j*B (n-k),?_,?_⟩
      · exact add_nonneg (hC _ _) (Finset.sum_nonneg (fun k _ ↦
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC _ _)) (hB _)))
      · intro a x
        rw [iteratedDeriv_succ',hd,
          iteratedDeriv_fun_sub
            ((hs (j+1) a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            (((hs j a).mul (hbs a)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
          iteratedDeriv_fun_mul
            ((hs j a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            ((hbs a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
        apply (abs_sub _ _).trans
        apply add_le_add (hbound n (j+1) le_rfl a x)
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk':k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose k))]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hbound k j hk' a x) (Nat.cast_nonneg _))
          (hbB (n-k) a x) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC _ _))

lemma responseJet_uniform_jets {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0≤c) :
    ∀ n j:ℕ,∃ C:ℝ,0≤C ∧ ∀ t x,|iteratedDeriv n (responseJet c ψ f j t) x|≤C := by
  have hs := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
  have hp (t x:ℝ) : heat t (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
    (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hb := exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc
  apply linear_derivative_tower_bounded (responseJet c ψ f) (baseJet c ψ 1)
    (responseJet_smooth hψ hf hc)
    (normalizedJet_smooth hs hp 1)
    (fun j t ↦ funext (fun x ↦ (responseJet_space hψ hf hc j t x).deriv))
    (responseJet_bound hψ hf hc)
  intro n
  exact normalizedJet_uniform_bounded hs hp hb n 1

lemma responseJet_boundedSmooth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0≤c) (n:ℕ) (t:ℝ) :
    BoundedSmooth (responseJet c ψ f n t) := by
  refine ⟨responseJet_smooth hψ hf hc n t,?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := responseJet_uniform_jets hψ hf hc k n
  exact ⟨C,hC,hb t⟩

lemma baseJet_space {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0≤c) (n:ℕ) (t x:ℝ) :
    HasDerivAt (baseJet c ψ n t)
      (baseJet c ψ (n+1) t x-baseJet c ψ n t x*baseJet c ψ 1 t x) x := by
  have hs := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
  have hp (t x:ℝ) : heat t (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
    (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  exact ((normalizedJet_smooth hs hp n t).differentiable
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne' x).hasDerivAt.congr_deriv
      (congrFun (normalizedJet_deriv hs hp n t) x)

lemma responseJet_second {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0≤c) (n:ℕ) (t x:ℝ) :
    deriv (deriv (responseJet c ψ f n t)) x=
      responseJet c ψ f (n+2) t x-2*responseJet c ψ f (n+1) t x*baseJet c ψ 1 t x-
        responseJet c ψ f n t x*baseJet c ψ 2 t x+
          2*responseJet c ψ f n t x*(baseJet c ψ 1 t x)^2 := by
  have hd : deriv (responseJet c ψ f n t)=fun y ↦ responseJet c ψ f (n+1) t y-
      responseJet c ψ f n t y*baseJet c ψ 1 t y :=
    funext (fun y ↦ (responseJet_space hψ hf hc n t y).deriv)
  rw [hd]
  convert! ((responseJet_space hψ hf hc (n+1) t x).sub
    ((responseJet_space hψ hf hc n t x).mul (baseJet_space hψ hc 1 t x))).deriv using 1
  simp only [show n+1+1=n+2 by omega]
  ring

lemma responseJet_heat_drift {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c t : ℝ} (hc : 0≤c) (ht : 0<t) (n:ℕ) (x:ℝ) :
    HasDerivAt (responseJet c ψ f n · x)
      ((1/2:ℝ)*deriv (deriv (responseJet c ψ f n t)) x+
        baseJet c ψ 1 t x*deriv (responseJet c ψ f n t) x) t := by
  convert! responseJet_time hψ hf hc ht n x using 1
  rw [responseJet_second hψ hf hc,(responseJet_space hψ hf hc n t x).deriv]
  ring
end SKValue

end

end OAI
