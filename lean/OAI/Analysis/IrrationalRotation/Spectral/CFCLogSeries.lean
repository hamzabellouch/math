import OAI.Analysis.IrrationalRotation.Model.Spectral

namespace OAI

noncomputable section
open scoped CStarAlgebra
namespace Invariant233
namespace CFCLogSeries

section Normed
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def term (a : A) (n : ℕ) : A := ((n + 1 : ℝ)⁻¹) • a ^ (n + 1)

omit [CompleteSpace A] in
lemma norm_term_le (a : A) (n : ℕ) : ‖term a n‖ ≤ ‖a‖ ^ (n + 1) := by
  have hn : (1 : ℝ) ≤ n + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hi : (n + 1 : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hn
  rw [term, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (norm_pow_le' _ (by omega)) (by positivity)).trans
    (mul_le_of_le_one_left (by positivity) hi)

lemma summable_term {a : A} (ha : ‖a‖ < 1) : Summable (term a) := by
  apply ((summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one (norm_nonneg a) ha)).of_norm_bounded
  exact norm_term_le a

end Normed

section CStar
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

private lemma spectrum_abs_lt_one {a : A} (ha : ‖a‖ < 1)
    {x : ℝ} (hx : x ∈ spectrum ℝ a) : |x| < 1 :=
  (spectrum.norm_le_norm_of_mem hx).trans_lt ha

theorem hasSum_neg_log_one_sub {a : A} (hsa : IsSelfAdjoint a) (ha : ‖a‖ < 1) :
    HasSum (term a) (-CFC.log (1 - a)) := by
  let f : C(spectrum ℝ a, ℝ) := (ContinuousMap.id ℝ).restrict (spectrum ℝ a)
  have hf : ‖f‖ ≤ ‖a‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg a)).mpr
    intro x
    exact spectrum.norm_le_norm_of_mem x.property
  have hsum : Summable (term f) := summable_term (hf.trans_lt ha)
  have hc : ContinuousOn (fun x : ℝ => -Real.log (1 - x)) (spectrum ℝ a) := by
    apply ContinuousOn.neg
    apply Real.continuousOn_log.comp (continuous_const.sub continuous_id).continuousOn
    intro x hx
    exact ne_of_gt (sub_pos.mpr ((le_abs_self x).trans_lt (spectrum_abs_lt_one ha hx)))
  let g : C(spectrum ℝ a, ℝ) := ⟨_, hc.domRestrict⟩
  have heq : (∑' n, term f n) = g := by
    ext x
    rw [← ContinuousMap.tsum_apply hsum x]
    simpa [term, f, g, div_eq_mul_inv, mul_comm] using
      (Real.hasSum_pow_div_log_of_abs_lt_one
        (spectrum_abs_lt_one ha x.property)).tsum_eq
  have hmap := (cfcL hsa).hasSum (heq ▸ hsum.hasSum)
  have hid : cfcHom hsa f = a := cfcHom_id hsa
  have hterm : ∀ n, cfcL hsa (term f n) = term a n := by
    intro n
    simp only [term, cfcL_apply, map_smul, map_pow, hid]
  have hg : cfcL hsa g = -CFC.log (1 - a) := by
    change cfcHom hsa g = _
    rw [← cfc_apply (fun x : ℝ => -Real.log (1-x)) a hsa hc]
    rw [cfc_neg]
    change -cfc (fun x : ℝ => Real.log (1-x)) a = _
    have hlog : ContinuousOn Real.log ((fun x : ℝ => 1-x) '' spectrum ℝ a) := by
      apply Real.continuousOn_log.mono
      rintro y ⟨x, hx, rfl⟩
      exact ne_of_gt (sub_pos.mpr ((le_abs_self x).trans_lt (spectrum_abs_lt_one ha hx)))
    rw [cfc_comp' Real.log (fun x : ℝ => 1-x) a hlog]
    have hsub : cfc (fun x : ℝ => 1-x) a = 1-a := by
      rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) a,
        cfc_const_one ℝ a hsa, cfc_id' ℝ a hsa]
    rw [hsub]
    rfl
  simpa only [hterm, hg] using hmap

theorem norm_log_remainder_le {a : A} (hsa : IsSelfAdjoint a) (ha : ‖a‖ < 1)
    (n : ℕ) :
    ‖(∑ i ∈ Finset.range n, term a i) + CFC.log (1-a)‖ ≤
      ‖a‖ ^ (n+1) / (1-‖a‖) := by
  have ht : HasSum (fun i => term a (i+n))
      (-CFC.log (1-a) - ∑ i ∈ Finset.range n, term a i) := by
    apply (hasSum_nat_add_iff n).mpr
    simpa using hasSum_neg_log_one_sub hsa ha
  have hg : HasSum (fun i : ℕ => ‖a‖ ^ (i+n+1))
      (‖a‖ ^ (n+1) / (1-‖a‖)) := by
    simpa only [pow_add, pow_one, div_eq_mul_inv, mul_one, mul_assoc,
      mul_comm, mul_left_comm] using
      (hasSum_geometric_of_lt_one (norm_nonneg a) ha).mul_left (‖a‖ ^ (n+1))
  have hb := ht.norm_le_of_bounded hg (fun i => norm_term_le a (i+n))
  have heq : -CFC.log (1-a) - (∑ i ∈ Finset.range n, term a i) =
      -((∑ i ∈ Finset.range n, term a i) + CFC.log (1-a)) := by abel
  rwa [heq, norm_neg] at hb

theorem norm_log_one_sub_add_le {a : A} (hsa : IsSelfAdjoint a) (ha : ‖a‖ < 1) :
    ‖CFC.log (1-a) + a‖ ≤ ‖a‖ ^ 2 / (1-‖a‖) := by
  simpa [term, add_comm] using norm_log_remainder_le hsa ha 1

theorem norm_log_one_add_sub_le {a : A} (hsa : IsSelfAdjoint a) (ha : ‖a‖ < 1) :
    ‖CFC.log (1+a) - a‖ ≤ ‖a‖ ^ 2 / (1-‖a‖) := by
  simpa only [sub_neg_eq_add, norm_neg, sub_eq_add_neg, neg_neg] using
    norm_log_one_sub_add_le hsa.neg (by simpa only [norm_neg] using ha)

theorem TracialState_hasSum_log (τ : TracialState A) {a : A}
    (hsa : IsSelfAdjoint a) (ha : ‖a‖ < 1) :
    HasSum (fun n => τ (term a n)) (-τ (CFC.log (1-a))) := by
  simpa only [map_neg] using τ.toContinuousLinearMap.hasSum
    (hasSum_neg_log_one_sub hsa ha)

theorem norm_trace_log_one_add_sub_le (τ : TracialState A) {a : A}
    (hsa : IsSelfAdjoint a) (ha : ‖a‖ < 1) :
    ‖τ (CFC.log (1+a)) - τ a‖ ≤
      ‖τ.toContinuousLinearMap‖ * (‖a‖ ^ 2 / (1-‖a‖)) := by
  rw [← map_sub]
  exact (τ.toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_log_one_add_sub_le hsa ha) (norm_nonneg _))

end CStar
end CFCLogSeries
end Invariant233

end

end OAI
