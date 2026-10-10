import OAI.NumberTheory.JointDickman.Probability.CandidateSiteKernel
import Mathlib.Data.Nat.Dist

namespace OAI

/-! # Uniform means in either orientation of the latent site kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem candidateSiteKernel_conditional_mean
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, χ e ≤ 1) →
      ∀ i k : Fin M, i ≠ k → ∀ a ⊆ auxiliaryPrimes B,
      finiteExpectation (independentPrimeSetMass B)
        (fun R => candidateSiteKernel B L T H M τ C χ i k a R.val) ≤
          K/(T : ℝ)*singularFactor 24 (Nat.dist i.val k.val) := by
  obtain ⟨K₁,hK₁,hf⟩ := latentCandidateKernel_forward_conditional_mean hFord hM
  obtain ⟨K₂,hK₂,hr⟩ := latentCandidateKernel_reverse_conditional_mean hFord hM
  refine ⟨K₁+K₂,add_pos hK₁ hK₂,?_⟩
  filter_upwards [hf,hr] with B hf hr
  intro L T H M τ C hT hTs χ hχ i k hik a ha
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 ≤ singularFactor 24 (Nat.dist i.val k.val) :=
    zero_le_one.trans (singularFactor_one_le (by norm_num) _)
  rcases lt_or_gt_of_ne hik with hik | hki
  · have hh := hf L T H M τ C hT hTs (fun _ => a) χ hχ i k hik ha
    change finiteExpectation (independentPrimeSetMass B)
      (fun R => candidateSiteKernel B L T H M τ C χ i k a R.val) ≤ _ at hh
    rw [Nat.dist_eq_sub_of_le hik.le]
    refine hh.trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · apply div_le_div_of_nonneg_right _ hTr.le
      linarith
    · simpa only [Nat.dist_eq_sub_of_le hik.le] using hs
  · have hh := hr L T H M τ C hT hTs (fun _ => a) χ hχ k i hki ha
    have he : (fun R : (auxiliaryPrimes B).powerset =>
        candidateSiteKernel B L T H M τ C χ i k a R.val) =
        (fun R => latentCandidateKernel B L T H M τ C
          (Function.update (fun _ => a) k R.val) χ k i) := by
      funext R
      exact latentCandidateKernel_symm _ _ _ _ _ _ _ _ _ _ _
    rw [he,Nat.dist_eq_sub_of_le_right hki.le]
    refine hh.trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · apply div_le_div_of_nonneg_right _ hTr.le
      linarith
    · simpa only [Nat.dist_eq_sub_of_le_right hki.le] using hs

theorem candidateSiteKernel_zero_of_far {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (a b : Finset ℕ)
    (hfar : T ≤ Nat.dist i.val k.val) :
    candidateSiteKernel B L T H M τ C χ i k a b = 0 := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · rw [Nat.dist_eq_sub_of_le hik.le] at hfar
    exact latentCandidateKernel_forward_zero _ _ _ _ hik hfar
  · exact candidateSiteKernel_diag _ _ _ _ _ _ _ _ _ _ _
  · rw [candidateSiteKernel_symm]
    rw [Nat.dist_eq_sub_of_le_right hki.le] at hfar
    exact latentCandidateKernel_forward_zero _ _ _ _ hki hfar

theorem backward_lag_singular_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if k < i ∧ i.val-k.val < T then singularFactor 24 (i.val-k.val) else 0) ≤
      Real.exp 24*(T : ℝ) := by
  let I : Finset (Fin M) := univ.filter (fun k => k < i ∧ i.val-k.val < T)
  have hinj : Set.InjOn (fun k : Fin M => i.val-k.val) I := by
    intro k hk l hl he
    have hk' : k.val < i.val := (mem_filter.mp hk).2.1
    have hl' : l.val < i.val := (mem_filter.mp hl).2.1
    apply Fin.ext
    dsimp only at he
    omega
  have hsub : I.image (fun k => i.val-k.val) ⊆ Ioc 0 T := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    have hk := (mem_filter.mp hk).2
    have hik : k.val < i.val := hk.1
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ I, singularFactor 24 (i.val-k.val) := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => i.val-k.val), singularFactor 24 j := (sum_image hinj).symm
    _ ≤ ∑ j ∈ Ioc 0 T, singularFactor 24 j := sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => zero_le_one.trans (singularFactor_one_le (by norm_num) j))
    _ ≤ _ := by
      simpa only [pow_one,Nat.cast_one,Nat.sub_self,pow_zero,one_mul,mul_one] using
        singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 1 T

theorem distance_lag_singular_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
      singularFactor 24 (Nat.dist i.val k.val) else 0) ≤ 2*Real.exp 24*(T : ℝ) := by
  have he (k : Fin M) :
      (if i ≠ k ∧ Nat.dist i.val k.val < T then singularFactor 24 (Nat.dist i.val k.val) else 0) =
      (if i < k ∧ k.val-i.val < T then singularFactor 24 (k.val-i.val) else 0) +
      (if k < i ∧ i.val-k.val < T then singularFactor 24 (i.val-k.val) else 0) := by
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le,Nat.dist_eq_sub_of_le h.le]
    · simp
    · simp [h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le,Nat.dist_eq_sub_of_le_right h.le]
  simp_rw [he]
  rw [sum_add_distrib]
  have hf := forward_lag_singular_sum i T
  have hb := backward_lag_singular_sum i T
  linarith

end JointDickman

end OAI
