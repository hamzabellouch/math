import Mathlib

namespace OAI

noncomputable section
namespace VelocityDetection.UniformDerivatives
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
variable {I E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def Bounded (f : I → E → F) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ n (f a) x‖ ≤ C

def Positive (f : I → E → F) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ n (f a) x‖ ≤ C

theorem Bounded.upTo {f : I → E → F} (hf : Bounded f) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i ≤ n, ∀ a x, ‖iteratedFDeriv ℝ i (f a) x‖ ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, _, hC⟩ := hf 0
    exact ⟨max 1 C, le_max_left _ _, fun i hi a x =>
      (by
        have : i = 0 := by omega
        subst i
        exact (hC a x).trans (le_max_right _ _))⟩
  | succ n ih =>
    obtain ⟨C, hC, hc⟩ := ih
    obtain ⟨D, _, hd⟩ := hf (n + 1)
    refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
    intro i hi a x
    by_cases h : i ≤ n
    · exact (hc i h a x).trans (le_max_left _ _)
    · have : i = n + 1 := by omega
      subst i
      exact (hd a x).trans (le_max_right _ _)

theorem Positive.upTo {f : I → E → F} (hf : Positive f) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i, 1 ≤ i → i ≤ n → ∀ a x,
      ‖iteratedFDeriv ℝ i (f a) x‖ ≤ C := by
  induction n with
  | zero => exact ⟨1, le_rfl, fun i hi hn => by omega⟩
  | succ n ih =>
    obtain ⟨C, hC, hc⟩ := ih
    obtain ⟨D, _, hd⟩ := hf (n + 1) (by omega)
    refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
    intro i hi hn a x
    by_cases h : i ≤ n
    · exact (hc i hi h a x).trans (le_max_left _ _)
    · have : i = n + 1 := by omega
      subst i
      exact (hd a x).trans (le_max_right _ _)

theorem Bounded.positive {f : I → E → F} (hf : Bounded f) : Positive f :=
  fun n _ => hf n

theorem Bounded.comp {g : I → F → G} {f : I → E → F}
    (hg : ∀ a, ContDiff ℝ ∞ (g a)) (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hgb : Bounded g) (hfb : Positive f) : Bounded (fun a x => g a (f a x)) := by
  intro n
  obtain ⟨C, hC, hc⟩ := hgb.upTo n
  obtain ⟨D, hD, hd⟩ := hfb.upTo n
  refine ⟨n.factorial * C * D ^ n, by positivity, ?_⟩
  intro a x
  exact norm_iteratedFDeriv_comp_le (hg a) (hf a) (by exact_mod_cast le_top) x
    (fun i hi => hc i hi a (f a x))
    (fun i hi hn => (hd i hi hn a x).trans (by simpa using pow_le_pow_right₀ hD hi))

theorem Bounded.add {f g : I → E → F} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hg : ∀ a, ContDiff ℝ ∞ (g a)) (hfb : Bounded f) (hgb : Bounded g) :
    Bounded (fun a x => f a x + g a x) := by
  intro n
  obtain ⟨C, hC, hc⟩ := hfb n
  obtain ⟨D, hD, hd⟩ := hgb n
  refine ⟨C + D, by positivity, fun a x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply ((hf a).of_le (show (n : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)).contDiffAt
    ((hg a).of_le (show (n : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hc a x) (hd a x))

theorem Bounded.sub {f g : I → E → F} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hg : ∀ a, ContDiff ℝ ∞ (g a)) (hfb : Bounded f) (hgb : Bounded g) :
    Bounded (fun a x => f a x - g a x) := by
  intro n
  obtain ⟨C, hC, hc⟩ := hfb n
  obtain ⟨D, hD, hd⟩ := hgb n
  refine ⟨C + D, by positivity, fun a x => ?_⟩
  rw [fun_iteratedFDeriv_sub_apply ((hf a).of_le (show (n : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)).contDiffAt
    ((hg a).of_le (show (n : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hc a x) (hd a x))

theorem Bounded.mul {f g : I → E → ℝ} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hg : ∀ a, ContDiff ℝ ∞ (g a)) (hfb : Bounded f) (hgb : Bounded g) :
    Bounded (fun a x => f a x * g a x) := by
  intro n
  obtain ⟨C, hC, hc⟩ := hfb.upTo n
  obtain ⟨D, hD, hd⟩ := hgb.upTo n
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C * D, by positivity, ?_⟩
  intro a x
  apply (norm_iteratedFDeriv_mul_le (hf a) (hg a) x (show (n : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)).trans
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  gcongr
  · exact hc i hin a x
  · exact hd (n - i) (Nat.sub_le _ _) a x

theorem compact {f : E → F} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Bounded (fun _ : I => f) := by
  intro n
  have h := ((hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).bddAbove_range_of_hasCompactSupport
    (hfc.iteratedFDeriv n).norm
  obtain ⟨C, hC⟩ := h
  refine ⟨max 0 C, le_max_left _ _, fun _ x => ?_⟩
  exact (hC (mem_range_self x)).trans (le_max_right _ _)

theorem norm_precomp_le (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) {f : F → G}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)

theorem Bounded.precomp {f : I → F → G} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hfb : Bounded f) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    Bounded (fun a x => f a (L x)) := by
  intro n
  obtain ⟨C, hC, hc⟩ := hfb n
  exact ⟨C, hC, fun a x => (norm_precomp_le L hL (hf a) n x).trans (hc a (L x))⟩

theorem Positive.precomp {f : I → F → G} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hfb : Positive f) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    Positive (fun a x => f a (L x)) := by
  intro n hn
  obtain ⟨C, hC, hc⟩ := hfb n hn
  exact ⟨C, hC, fun a x => (norm_precomp_le L hL (hf a) n x).trans (hc a (L x))⟩

theorem Positive.linear (L : E →L[ℝ] F) : Positive (fun _ : I => L) := by
  intro n hn
  refine ⟨‖L‖, norm_nonneg _, fun _ x => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  change ‖iteratedFDeriv ℝ (n + 1) (L : E → F) x‖ ≤ ‖L‖
  rw [← norm_iteratedFDeriv_fderiv]
  have hd : fderiv ℝ (L : E → F) = fun _ => L := funext fun _ => L.fderiv
  rw [hd]
  cases n with
  | zero => simp
  | succ n => simp [iteratedFDeriv_succ_const]

theorem Positive.sub {f g : I → E → F} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hg : ∀ a, ContDiff ℝ ∞ (g a)) (hfb : Positive f) (hgb : Positive g) :
    Positive (fun a x => f a x - g a x) := by
  intro n hn
  obtain ⟨C, hC, hc⟩ := hfb n hn
  obtain ⟨D, hD, hd⟩ := hgb n hn
  refine ⟨C + D, by positivity, fun a x => ?_⟩
  rw [fun_iteratedFDeriv_sub_apply (contDiff_infty.mp (hf a) n).contDiffAt
    (contDiff_infty.mp (hg a) n).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hc a x) (hd a x))

theorem Positive.div {f : I → E → ℝ} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hfb : Positive f) (R : I → ℝ) (hR : ∀ a, 1 ≤ R a) :
    Positive (fun a x => f a x / R a) := by
  intro n hn
  obtain ⟨C, hC, hc⟩ := hfb n hn
  refine ⟨C, hC, fun a x => ?_⟩
  have hRa : 0 < R a := lt_of_lt_of_le zero_lt_one (hR a)
  have heq : (fun x => f a x / R a) = fun x => (R a)⁻¹ • f a x := by
    ext x; simp [div_eq_mul_inv, mul_comm]
  change ‖iteratedFDeriv ℝ n (fun x => f a x / R a) x‖ ≤ C
  rw [heq, iteratedFDeriv_const_smul_apply' (contDiff_infty.mp (hf a) n).contDiffAt, norm_smul]
  apply (mul_le_mul_of_nonneg_left (hc a x) (norm_nonneg _)).trans
  exact mul_le_of_le_one_left hC (by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRa)]
    exact inv_le_one_of_one_le₀ (hR a))

theorem Positive.deriv {f : I → ℝ → F} (hfb : Positive f) :
    Bounded (fun a => deriv (f a)) := by
  intro n
  obtain ⟨C, hC, hc⟩ := hfb (n + 1) (by omega)
  refine ⟨C, hC, fun a x => ?_⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ'] using hc a x

end VelocityDetection.UniformDerivatives
end

end OAI
