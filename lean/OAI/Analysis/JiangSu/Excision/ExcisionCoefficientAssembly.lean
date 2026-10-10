import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Traces.SmallTracePeakIsometry
import OAI.Analysis.JiangSu.Excision.ExcisionUpperCut
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzControlledSupport

namespace OAI

noncomputable section


namespace CStarExcision
open scoped BigOperators

variable {A : Type*} [NonUnitalCStarAlgebra A]
variable {I : Type*} [Fintype I]

 def assembled (d : I → A) (r : A) (c : I → A) : A := ∑ i,d i*r*c i
 def coefficientValue (ω : A → ℂ) (d c : I → A) (a : A) : A :=
  ∑ i,∑ j,ω (star (d i)*a*d j) • (star (c i)*c j)

 lemma assembled_square (d c : I → A) (r a : A) :
    star (assembled d r c)*a*assembled d r c=
      ∑ i,∑ j,star (c i)*(star r*(star (d i)*a*d j)*r)*c j := by
  simp only [assembled,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_assoc]

 lemma coefficient_mul (ω : A → ℂ) (d c : I → A) (a e : A)
    (he : ∀ i,e*c i=c i*e) :
    coefficientValue ω d c a*e=
      ∑ i,∑ j,star (c i)*(ω (star (d i)*a*d j) • e)*c j := by
  simp only [coefficientValue,Finset.sum_mul,smul_mul_assoc,mul_smul_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  calc
    star (c i)*c j*e=star (c i)*(c j*e) := mul_assoc _ _ _
    _=star (c i)*(e*c j) := by rw [he j]
    _=star (c i)*e*c j := (mul_assoc _ _ _).symm

 lemma assembly_error_identity (ω : A → ℂ) (d c : I → A) (r a e : A)
    (he : ∀ i,e*c i=c i*e) :
    star (assembled d r c)*a*assembled d r c-coefficientValue ω d c a*e=
      ∑ i,∑ j,star (c i)*(star r*(star (d i)*a*d j)*r-
        ω (star (d i)*a*d j) • e)*c j := by
  rw [assembled_square,coefficient_mul ω d c a e he,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  noncomm_ring

 theorem assembly_error_le (ω : A → ℂ) (d c : I → A) (r a e : A)
    (he : ∀ i,e*c i=c i*e) {δ : ℝ}
    (hδ : ∀ i j,‖star r*(star (d i)*a*d j)*r-ω (star (d i)*a*d j) • e‖≤δ) :
    ‖star (assembled d r c)*a*assembled d r c-coefficientValue ω d c a*e‖≤
      δ*(∑ i,‖c i‖)^2 := by
  rw [assembly_error_identity ω d c r a e he]
  calc
    ‖∑ i,∑ j,star (c i)*(star r*(star (d i)*a*d j)*r-
        ω (star (d i)*a*d j) • e)*c j‖
      ≤∑ i,∑ j,‖c i‖*δ*‖c j‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j _
        calc
          _≤(‖star (c i)‖*‖star r*(star (d i)*a*d j)*r-
            ω (star (d i)*a*d j) • e‖)*‖c j‖ :=
              (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
                (norm_mul_le _ _) (norm_nonneg _))
          _≤_ := by
            rw [norm_star]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hδ i j) (norm_nonneg _)) (norm_nonneg _)
    _=δ*(∑ i,‖c i‖)^2 := by
      simp only [←Finset.mul_sum,←Finset.sum_mul]
      ring

 theorem compression_error_le (b r a e : A) (zeta : ℂ)
    (hb : star b=b) (hbr : b*r=r) {δ ε : ℝ}
    (hδ : ‖b*a*b-zeta • (b*b)‖≤δ) (hε : ‖star r*r-e‖≤ε) :
    ‖star r*a*r-zeta • e‖≤‖r‖^2*δ+‖zeta‖*ε := by
  have hrb : star r*b=star r := by
    have h := congrArg star hbr
    simpa only [star_mul,hb] using h
  have hid : star r*a*r-zeta • e=
      star r*(b*a*b-zeta • (b*b))*r+zeta • (star r*r-e) := by
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,smul_sub]
    rw [show star r*(b*a*b)*r=star r*a*r by
      calc
        star r*(b*a*b)*r=(star r*b)*a*(b*r) := by noncomm_ring
        _=star r*a*r := by rw [hrb,hbr]]
    rw [show star r*(b*b)*r=star r*r by
      calc
        star r*(b*b)*r=(star r*b)*(b*r) := by noncomm_ring
        _=star r*r := by rw [hrb,hbr]]
    abel
  rw [hid]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      ‖star r*(b*a*b-zeta • (b*b))*r‖≤
          (‖star r‖*‖b*a*b-zeta • (b*b)‖)*‖r‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤(‖r‖*δ)*‖r‖ := by
        rw [norm_star]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hδ (norm_nonneg _)) (norm_nonneg _)
      _=‖r‖^2*δ := by ring
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hε (norm_nonneg _)

end CStarExcision


namespace DirectComparison
open Pureness CurrentMain
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma cut_rank_lower_from_trace (τ : TracialState A) (w : A)
    (hw : 0 ≤ w) (hwn : ‖w‖ ≤ 1) {β : ℝ} (hβ : 0 ≤ β) :
    (τ.functional w).re-β ≤ (normalizedRootRank τ (directPositiveCut β w)).toReal := by
  let b := directPositiveCut β w
  have hb := directPositiveCut_nonneg β w
  have hb1 : b ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg b hb).mp
    (norm_directPositiveCut_le_one w hw hwn β hβ)
  have hr := trace_le_rank_of_mem_hereditary τ b b hb (self_mem_hereditary b hb) hb1
  have hrs := ENNReal.toReal_mono (directRank_ne_top τ b hb) hr
  rw [ENNReal.toReal_ofReal (τ.functional.map_nonneg hb).1] at hrs
  have he := (trace_sub_real_le_norm τ w b).trans (norm_sub_directPositiveCut_le w hw β hβ)
  linarith

theorem small_trace_supported_isometry [Nonempty (TracialState A)]
    (hcmp : StrictComparison A) (e w h f : A)
    (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) (hw : 0 ≤ w) (hwn : ‖w‖ ≤ 1) (hhw : h*w=w)
    {α β ε : ℝ} (hα : 0<α) (hβ : 0<β) (hε : 0<ε) (hε1 : ε ≤ 1)
    (hsmall : ∀ τ : TracialState A, (τ.functional e).re<α*β)
    (hlarge : ∀ τ : TracialState A, 2*β ≤ (τ.functional w).re) :
    ∃ s : A, ‖s‖ ≤ 2 ∧ ‖star s*s-e‖<ε+α ∧ h*s=s ∧
      ‖f*s-s‖ ≤ 2*β⁻¹*‖f*w-w‖ := by
  let a := directPositiveCut α e
  let b := directPositiveCut β w
  have ha := directPositiveCut_nonneg α e
  have hb := directPositiveCut_nonneg β w
  have hgap (τ : TracialState A) : normalizedRootRank τ a<normalizedRootRank τ b := by
    apply (ENNReal.toReal_lt_toReal (directRank_ne_top τ a ha) (directRank_ne_top τ b hb)).mp
    have hs := directPositiveCut_rank_le_trace_div τ e he α hα
    have hl := cut_rank_lower_from_trace τ w hw hwn hβ.le
    have hd : (τ.functional e).re/α<β := (div_lt_iff₀ hα).mpr (by nlinarith [hsmall τ])
    change (normalizedRootRank τ a).toReal ≤ _ at hs
    change _ ≤ (normalizedRootRank τ b).toReal at hl
    linarith [hlarge τ]
  have hb0 : b≠0 := by
    intro hz
    let τ : TracialState A := Classical.choice inferInstance
    have hn := hgap τ
    rw [hz,normalizedRootRank_zero] at hn
    exact not_lt_of_ge zero_le hn
  have hab := hcmp.scalar a b ha hb hb0 hgap
  obtain ⟨s,hsn,hse,hhs,hfs⟩ := approximate_controlled_isometry a w h f
    (norm_directPositiveCut_le_one e he hen α hα.le) hw hhw hβ hε hε1 hab
  refine ⟨s,hsn,?_,hhs,hfs⟩
  have hn := norm_sub_le_norm_sub_add_norm_sub (star s*s) a e
  have hc := norm_sub_directPositiveCut_le e he α hα.le
  rw [norm_sub_rev e a] at hc
  linarith

theorem supported_state_excision [Nonempty (TracialState A)]
    (hcmp : StrictComparison A) (e w h f a : A) (z : ℂ)
    (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) (hw : 0 ≤ w) (hwn : ‖w‖ ≤ 1)
    (hh : IsSelfAdjoint h) (hhw : h*w=w)
    {α β ε δ : ℝ} (hα : 0<α) (hβ : 0<β) (hε : 0<ε) (hε1 : ε ≤ 1)
    (hδ : 0 ≤ δ) (hex : ‖h*a*h-z • (h*h)‖ ≤ δ)
    (hsmall : ∀ τ : TracialState A, (τ.functional e).re<α*β)
    (hlarge : ∀ τ : TracialState A, 2*β ≤ (τ.functional w).re) :
    ∃ s : A, ‖s‖ ≤ 2 ∧ ‖star s*s-e‖<ε+α ∧
      ‖f*s-s‖ ≤ 2*β⁻¹*‖f*w-w‖ ∧
      ‖star s*a*s-z • e‖ ≤ 4*δ+‖z‖*(ε+α) := by
  obtain ⟨s,hsn,hse,hhs,hfs⟩ := small_trace_supported_isometry hcmp e w h f
    he hen hw hwn hhw hα hβ hε hε1 hsmall hlarge
  refine ⟨s,hsn,hse,hfs,?_⟩
  have hx := CStarExcision.compression_error_le h s a e z hh.star_eq hhs hex hse.le
  have hn : ‖s‖^2 ≤ 4 := by nlinarith [norm_nonneg s]
  exact hx.trans (add_le_add (mul_le_mul_of_nonneg_right hn hδ) le_rfl)

end DirectComparison

end

end OAI
