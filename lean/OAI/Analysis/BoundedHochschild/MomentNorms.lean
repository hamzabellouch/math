import Mathlib

namespace OAI

/-! Recovery of operator norms from moments and free-word boundary decompositions. -/

noncomputable section


open scoped ComplexOrder
open Filter Topology
namespace HochschildMoments
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_le_of_positive_moment_bound (τ : A →ₚ[ℂ] ℂ)
    (hfaithful : ∀ x : A, τ (star x * x) = 0 → x = 0)
    (a : A) (ha : 0 ≤ a) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n : ℕ, (τ (a^n)).re ≤ R^n) : ‖a‖ ≤ R := by
  by_contra! hnot
  have : Nontrivial A := nontrivial_of_ne a 0 (by
    intro h; rw [h, norm_zero] at hnot; linarith)
  obtain ⟨c, hRc, hca⟩ := exists_between hnot
  have hc : 0 < c := hR.trans_lt hRc
  let f : ℝ → ℝ := fun t => max 0 (t-c)
  have hf : Continuous f := by fun_prop
  let x : A := cfc f a
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  have hsx : IsSelfAdjoint x := cfc_predicate f a
  have hineq (n : ℕ) : c^n • (star x*x) ≤ ‖a‖^2 • a^n := by
    have hleft : cfc (fun t => c^n * (f t * f t)) a = c^n • (star x*x) := by
      rw [cfc_const_mul (c^n) (fun t => f t * f t) a (hf.mul hf).continuousOn,
        cfc_mul f f a hf.continuousOn hf.continuousOn, hsx.star_eq]
    have hright : cfc (fun t : ℝ => ‖a‖^2 * t^n) a = ‖a‖^2 • a^n := by
      rw [cfc_const_mul (‖a‖^2) (fun t : ℝ => t^n) a (continuous_id.pow n).continuousOn,
        cfc_pow_id a n hsa]
    rw [← hleft, ← hright]
    apply (cfc_le_iff _ _ a ((hf.mul hf).const_mul _).continuousOn
      ((continuous_id.pow n).const_mul _).continuousOn hsa).mpr
    intro t ht
    change c^n * (f t * f t) ≤ ‖a‖^2 * t^n
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha ht
    have htA : t ≤ ‖a‖ := (le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)
    by_cases htc : t ≤ c
    · simp only [f, max_eq_left (sub_nonpos.mpr htc), mul_zero]
      positivity
    · have hct : c ≤ t := le_of_lt (lt_of_not_ge htc)
      simp only [f, max_eq_right (sub_nonneg.mpr hct)]
      have hfA : (t-c)*(t-c) ≤ ‖a‖^2 := by nlinarith [norm_nonneg a]
      calc
        _ ≤ t^n * ‖a‖^2 := mul_le_mul (pow_le_pow_left₀ hc.le hct n) hfA
          (mul_self_nonneg _) (pow_nonneg ht0 _)
        _ = _ := by ring
  have hxtrace : 0 ≤ (τ (star x*x)).re := by
    exact (τ.map_nonneg (star_mul_self_nonneg x)).1
  have htrace (n : ℕ) : (τ (star x*x)).re ≤ ‖a‖^2 * (R/c)^n := by
    have hh := τ.monotone (hineq n)
    change τ (c^n • (star x*x)) ≤ τ (‖a‖^2 • a^n) at hh
    rw [τ.map_smul_of_tower, τ.map_smul_of_tower] at hh
    have hre : c^n * (τ (star x*x)).re ≤ ‖a‖^2 * (τ (a^n)).re := by simpa only [Complex.smul_re, smul_eq_mul] using hh.1
    apply (mul_le_mul_iff_right₀ (pow_pos hc n)).mp
    calc
      _ = c^n * (τ (star x*x)).re := by ring
      _ ≤ ‖a‖^2 * (τ (a^n)).re := hre
      _ ≤ ‖a‖^2 * R^n := mul_le_mul_of_nonneg_left (hbound n) (sq_nonneg _)
      _ = (‖a‖^2 * (R/c)^n) * c^n := by
        rw [div_pow, mul_assoc, div_mul_cancel₀ _ (ne_of_gt (pow_pos hc n))]
      _ = c^n * (‖a‖^2 * (R/c)^n) := by ring
  have hlim : Tendsto (fun n : ℕ => ‖a‖^2 * (R/c)^n) atTop (𝓝 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR hc.le)
      ((div_lt_one hc).mpr hRc)).const_mul (‖a‖^2) using 1; simp
  have hzre : (τ (star x*x)).re = 0 := le_antisymm (ge_of_tendsto' hlim htrace) hxtrace
  have hz : τ (star x*x) = 0 := by
    have hp := τ.map_nonneg (star_mul_self_nonneg x)
    exact Complex.ext hzre hp.2.symm
  have hx : x = 0 := hfaithful x hz
  have heq : cfc f a = cfc (fun _ : ℝ => 0) a := by simpa only [cfc_const_zero] using hx
  have hxnorm := eqOn_of_cfc_eq_cfc heq hf.continuousOn continuousOn_const hsa
    (CStarAlgebra.norm_mem_spectrum_of_nonneg a ha)
  dsimp [f] at hxnorm
  have : 0 < max 0 (‖a‖-c) := lt_max_of_lt_right (sub_pos.mpr hca)
  linarith

lemma positive_moment_le_norm_pow (τ : A →ₚ[ℂ] ℂ) (hτ : τ 1 = 1)
    (a : A) (ha : 0 ≤ a) (n : ℕ) : (τ (a^n)).re ≤ ‖a‖^n := by
  have : Nontrivial A := nontrivial_of_ne (1 : A) 0 (by
    intro h; have := hτ; rw [h, map_zero] at this; exact zero_ne_one this)
  calc
    _ ≤ ‖τ (a^n)‖ := Complex.re_le_norm _
    _ ≤ ‖τ 1‖ * ‖a^n‖ := τ.norm_apply_le_of_nonneg _ (CStarAlgebra.pow_nonneg a n ha)
    _ ≤ ‖a‖^n := by simpa [hτ] using norm_pow_le a n

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
 

theorem norm_eq_of_positive_moments
    (τ : A →ₚ[ℂ] ℂ) (ρ : B →ₚ[ℂ] ℂ) (hτ : τ 1 = 1) (hρ : ρ 1 = 1)
    (hτf : ∀ x : A, τ (star x*x)=0 → x=0)
    (hρf : ∀ x : B, ρ (star x*x)=0 → x=0)
    (a : A) (ha : 0 ≤ a) (b : B) (hb : 0 ≤ b)
    (hm : ∀ n : ℕ, τ (a^n) = ρ (b^n)) : ‖a‖ = ‖b‖ := by
  apply le_antisymm
  · apply norm_le_of_positive_moment_bound τ hτf a ha ‖b‖ (norm_nonneg _)
    intro n
    rw [hm]
    exact positive_moment_le_norm_pow ρ hρ b hb n
  · apply norm_le_of_positive_moment_bound ρ hρf b hb ‖a‖ (norm_nonneg _)
    intro n
    rw [← hm]
    exact positive_moment_le_norm_pow τ hτ a ha n

 
theorem norm_eq_of_star_mul_moments
    (τ : A →ₚ[ℂ] ℂ) (ρ : B →ₚ[ℂ] ℂ) (hτ : τ 1 = 1) (hρ : ρ 1 = 1)
    (hτf : ∀ x : A, τ (star x*x)=0 → x=0)
    (hρf : ∀ x : B, ρ (star x*x)=0 → x=0)
    (a : A) (b : B)
    (hm : ∀ n : ℕ, τ ((star a*a)^n) = ρ ((star b*b)^n)) : ‖a‖ = ‖b‖ := by
  have h := norm_eq_of_positive_moments τ ρ hτ hρ hτf hρf
    (star a*a) (star_mul_self_nonneg _) (star b*b) (star_mul_self_nonneg _) hm
  rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg a, norm_nonneg b]
end HochschildMoments
namespace HochschildFreeWords
open FreeGroup
variable {α : Type*}
 

theorem boundary_decomposition (v w : List (α × Bool))
    (hv : IsReduced v) (hw : IsReduced w) :
    ∃ u c h, v = u ++ c ∧ w = invRev c ++ h ∧ IsReduced (u ++ h) := by
  induction v using List.reverseRecOn generalizing w with
  | nil => exact ⟨[], [], w, rfl, rfl, hw⟩
  | @append_singleton v a ih =>
    cases w with
    | nil => exact ⟨v ++ [a], [], [], by simp, rfl, by simpa using hv⟩
    | cons b w =>
      by_cases hab : a.1 = b.1 ∧ a.2 = !b.2
      · have hv' : IsReduced v := hv.left_of_append
        have hw' : IsReduced w := hw.tail
        obtain ⟨u,c,h,hu,hc,hr⟩ := ih w hv' hw'
        refine ⟨u, c ++ [a], h, ?_, ?_, hr⟩
        · simp only [hu, List.append_assoc]
        · have hba : (a.1, !a.2) = b := by
            apply Prod.ext
            · exact hab.1
            · simp [hab.2]
          have hinv : invRev [a] = [b] := by
            simp [invRev, hba]
          rw [invRev_append, hinv]
          simpa using congrArg (fun l => b :: l) hc
      · refine ⟨v ++ [a], [], b::w, by simp, rfl, ?_⟩
        change List.IsChain _ _
        rw [List.append_assoc, List.singleton_append, List.isChain_append_cons_cons]
        refine ⟨hv, ?_, hw⟩
        intro hfst
        have hh : a.2 ≠ !b.2 := fun h => hab ⟨hfst,h⟩
        cases ha : a.2 <;> cases hb : b.2 <;> simp_all

variable [DecidableEq α]
 
theorem boundary_reduction (v w : List (α × Bool))
    (hv : IsReduced v) (hw : IsReduced w) :
    ∃ u c h, v = u ++ c ∧ w = invRev c ++ h ∧
      reduce (v ++ w) = u ++ h ∧ IsReduced (u ++ h) := by
  obtain ⟨u,c,h,hu,hw,hr⟩ := boundary_decomposition v w hv hw
  refine ⟨u,c,h,hu,hw,?_,hr⟩
  have heq : FreeGroup.mk (v ++ w) = FreeGroup.mk (u ++ h) := by
    rw [hu,hw]
    simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    group
  have heq' := congr_arg FreeGroup.toWord heq
  simpa only [FreeGroup.toWord_mk, hr.reduce_eq] using heq'
end HochschildFreeWords

 

namespace HochschildLength
open Finset
noncomputable section

abbrev Vector (ι : Type*) := lp (fun _ : ι => ℂ) 2

lemma norm_sum_single_sq {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (out : ι → κ)
    (c : ι → ℂ) (hinj : Set.InjOn out s) :
    ‖∑ i ∈ s, (lp.single 2 (out i) (c i) : Vector κ)‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 := by
  classical
  have hi : inner ℂ (∑ i ∈ s, (lp.single 2 (out i) (c i) : Vector κ))
      (∑ i ∈ s, (lp.single 2 (out i) (c i) : Vector κ)) =
      ∑ i ∈ s, (‖c i‖ : ℂ) ^ 2 := by
    rw [sum_inner]
    apply sum_congr rfl
    intro i hi
    rw [inner_sum]
    rw [sum_eq_single i]
    · simp [inner_self_eq_norm_sq_to_K]
    · intro j hj hji
      rw [lp.inner_single_left, lp.single_apply_ne]
      · exact inner_zero_right _
      · exact fun h => hji (hinj hj hi h.symm)
    · exact fun h => (h hi).elim
  apply Complex.ofReal_injective
  simpa [inner_self_eq_norm_sq_to_K, Complex.ofReal_sum, Complex.ofReal_pow] using hi

lemma norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have h := norm_sum_le s (fun i => a i * b i)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖))

 

lemma block_matrix_bound {U V H : Type*} (su : Finset U) (sv : Finset V)
    (sh : Finset H) (a : U → V → ℂ) (b : V → H → ℂ) :
    ∑ h ∈ sh, ∑ u ∈ su, ‖∑ v ∈ sv, a u v * b v h‖ ^ 2 ≤
      (∑ u ∈ su, ∑ v ∈ sv, ‖a u v‖ ^ 2) *
        (∑ h ∈ sh, ∑ v ∈ sv, ‖b v h‖ ^ 2) := by
  calc
    _ ≤ ∑ h ∈ sh, ∑ u ∈ su,
        (∑ v ∈ sv, ‖a u v‖ ^ 2) * (∑ v ∈ sv, ‖b v h‖ ^ 2) := by
      gcongr with h hh u hu
      exact norm_sum_mul_sq_le sv _ _
    _ = _ := by simp_rw [← sum_mul, ← mul_sum]

 

lemma masked_block_matrix_bound {U V H W : Type*} [DecidableEq W]
    (su : Finset U) (sv : Finset V) (sh : Finset H)
    (a : U → V → ℂ) (b : V → H → ℂ) (P : U → H → Prop) [∀ u h, Decidable (P u h)]
    (out : U → H → W)
    (hinj : Set.InjOn (fun p : H × U => out p.2 p.1)
      {p | p.1 ∈ sh ∧ p.2 ∈ su ∧ P p.2 p.1}) :
    ‖∑ p ∈ (sh ×ˢ su).filter (fun p => P p.2 p.1),
        (lp.single 2 (out p.2 p.1) (∑ v ∈ sv, a p.2 v * b v p.1) : Vector W)‖ ^ 2 ≤
      (∑ u ∈ su, ∑ v ∈ sv, ‖a u v‖ ^ 2) *
        (∑ h ∈ sh, ∑ v ∈ sv, ‖b v h‖ ^ 2) := by
  classical
  rw [norm_sum_single_sq _ _ _ (by
    intro p hp q hq hpq
    apply hinj (by simpa only [mem_coe, mem_filter, mem_product, Set.mem_ofPred_eq, and_assoc] using hp)
      (by simpa only [mem_coe, mem_filter, mem_product, Set.mem_ofPred_eq, and_assoc] using hq) hpq)]
  calc
    _ ≤ ∑ p ∈ sh ×ˢ su, ‖∑ v ∈ sv, a p.2 v * b v p.1‖ ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intros; positivity
    _ = ∑ h ∈ sh, ∑ u ∈ su, ‖∑ v ∈ sv, a u v * b v h‖ ^ 2 := sum_product ..
    _ ≤ _ := block_matrix_bound su sv sh a b

end
end HochschildLength
end

end OAI
