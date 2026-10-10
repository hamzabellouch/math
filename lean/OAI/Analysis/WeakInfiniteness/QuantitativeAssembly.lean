import Mathlib
import OAI.Analysis.WeakInfiniteness.BoundedImplementation
import OAI.Analysis.WeakInfiniteness.FinalAssembly
import OAI.Analysis.WeakInfiniteness.IndividualInfiniteness

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def QuantitativeSeparatingPositives (A : Type u) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (σ : ℝ) : Prop :=
  ∀ (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
    ∀ r l : ℝ,0 < r → r < 1 → 0 < l → l < 1/10 →
    ∃ Q R : A,0 ≤ Q ∧ 0 ≤ R ∧
      Q ∈ hereditarySubalgebra a ha.isSelfAdjoint ∧
      R ∈ hereditarySubalgebra b hb.isSelfAdjoint ∧
      (∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        NonUnitalRepresentationIrreducible π →
        (r ≤ ‖π a‖ → r*σ^2/1024 ≤ ‖π Q‖) ∧
        (r ≤ ‖π b‖ → r*σ^2/1024 ≤ ‖π R‖)) ∧
      ‖Q*R‖ ≤ 20*Real.sqrt l

lemma separation_parameter_choices {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ r l δ : ℝ,0 < r ∧ r < 1 ∧ 0 < l ∧ l < 1/10 ∧ 0 < δ ∧ δ < 1 ∧
      r^2 ≤ ε/16 ∧ δ+(4+δ)*δ ≤ ε/6 ∧
      320*Real.sqrt l/(r*σ^2/1024)^2 ≤ ε/4 := by
  let r := min (1/2) (Real.sqrt ε/4)
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hr1 : r < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hrε : r^2 ≤ ε/16 := by
    have h := min_le_right (1/2 : ℝ) (Real.sqrt ε/4)
    change r ≤ _ at h
    nlinarith [Real.sq_sqrt hε.le,Real.sqrt_nonneg ε]
  let m := r*σ^2/1024
  have hm : 0 < m := by dsimp [m]; positivity
  let z := ε*m^2/1280
  have hz : 0 < z := by dsimp [z]; positivity
  let l := min (1/20) (z^2)
  have hl : 0 < l := lt_min (by norm_num) (sq_pos_of_pos hz)
  have hl1 : l < 1/10 := (min_le_left _ _).trans_lt (by norm_num)
  have hls : Real.sqrt l ≤ z := by
    have := min_le_right (1/20 : ℝ) (z^2)
    change l ≤ z^2 at this
    nlinarith [Real.sq_sqrt hl.le,Real.sqrt_nonneg l]
  let δ := min (1/2) (ε/36)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδh : δ ≤ 1/2 := min_le_left _ _
  have hδε : δ ≤ ε/36 := min_le_right _ _
  refine ⟨r,l,δ,hr,hr1,hl,hl1,hδ,by linarith,hrε,?_,?_⟩
  · nlinarith
  · change 320*Real.sqrt l/m^2 ≤ ε/4
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    dsimp only [z] at hls
    nlinarith

theorem contractive_spi_of_quantitative_separation
    (hpi : ∀ x : A,0 ≤ x → ProperlyInfinite (diagonalCopies 1 x))
    {σ : ℝ} (hσ : 0 < σ) (hsep : QuantitativeSeparatingPositives A σ)
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) (han : ‖a‖ ≤ 1) (hbn : ‖b‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s t : A, ‖star s*(a*a)*s-a*a‖ < ε ∧
      ‖star t*(b*b)*t-b*b‖ < ε ∧ ‖star s*a*b*t‖ < ε := by
  obtain ⟨r,l,δ,hr,hr1,hl,hl1,hδ,hδ1,hrε,hδε,hlε⟩ := separation_parameter_choices hε hσ
  let m := r*σ^2/1024
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨Q,R,hQ,hR,hQa,hRb,hcover,hQR⟩ := hsep a b ha hb han hbn r l hr hr1 hl hl1
  have hca := cut_square_cuntz_of_norm_coverage hpi ha hQ hr hm (fun H π hπ => (hcover H π hπ).1)
  have hcb := cut_square_cuntz_of_norm_coverage hpi hb hR hr hm (fun H π hπ => (hcover H π hπ).2)
  have haa : 0 ≤ a*a := by simpa only [ha.star_eq] using star_mul_self_nonneg a
  have hbb : 0 ≤ b*b := by simpa only [hb.star_eq] using star_mul_self_nonneg b
  have hcan : ‖positiveCut (r^2) (a*a)‖ ≤ 1 := by
    calc
      _≤‖a*a‖ := norm_positiveCut_le haa (sq_nonneg r)
      _≤‖a‖*‖a‖ := norm_mul_le _ _
      _≤1*1 := by gcongr
      _=1 := by norm_num
  have hcbn : ‖positiveCut (r^2) (b*b)‖ ≤ 1 := by
    calc
      _≤‖b*b‖ := norm_positiveCut_le hbb (sq_nonneg r)
      _≤‖b‖*‖b‖ := norm_mul_le _ _
      _≤1*1 := by gcongr
      _=1 := by norm_num
  obtain ⟨x,hxe,hxn,hx⟩ := exists_bounded_cut_implementation hQ (positiveCut_nonneg _ _) hcan hm hca hδ hδ1
  obtain ⟨y,hye,hyn,hy⟩ := exists_bounded_cut_implementation hR (positiveCut_nonneg _ _) hcbn hm hcb hδ hδ1
  obtain ⟨s,hs⟩ := exists_left_approx_of_hereditary ha hQa x hδ
  obtain ⟨t,ht⟩ := exists_left_approx_of_hereditary hb hRb y hδ
  have hcross : ‖star (Q*x)*(R*y)‖ ≤ ε/4 := by
    calc
      _=‖star x*(Q*R)*y‖ := by congr 1; rw [star_mul,hQ.star_eq]; simp only [mul_assoc]
      _≤‖star x‖*‖Q*R‖*‖y‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤(4/m)*(20*Real.sqrt l)*(4/m) := by rw [norm_star]; gcongr
      _=320*Real.sqrt l/m^2 := by ring
      _≤ε/4 := hlε
  have hsa := norm_star_mul_approx_le (a*s) (a*s) (Q*x) (Q*x) hδ.le hxn hxn hs.le hs.le
  have htb := norm_star_mul_approx_le (b*t) (b*t) (R*y) (R*y) hδ.le hyn hyn ht.le ht.le
  have hst := norm_star_mul_approx_le (a*s) (b*t) (Q*x) (R*y) hδ.le hxn hyn hs.le ht.le
  have haerr : ‖star (a*s)*(a*s)-a*a‖ < ε := by
    have hcut := norm_sub_positiveCut_le haa (sq_nonneg r)
    calc
      _=‖(star (a*s)*(a*s)-star (Q*x)*(Q*x))+
        (star (Q*x)*(Q*x)-positiveCut (r^2) (a*a))+(positiveCut (r^2) (a*a)-a*a)‖ := by congr 1; abel
      _≤‖star (a*s)*(a*s)-star (Q*x)*(Q*x)‖+
        ‖star (Q*x)*(Q*x)-positiveCut (r^2) (a*a)‖+‖positiveCut (r^2) (a*a)-a*a‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _< (4+δ)*δ+δ+r^2 := by rw [norm_sub_rev (positiveCut _ (a*a)) (a*a)]; linarith
      _< ε := by linarith
  have hberr : ‖star (b*t)*(b*t)-b*b‖ < ε := by
    have hcut := norm_sub_positiveCut_le hbb (sq_nonneg r)
    calc
      _=‖(star (b*t)*(b*t)-star (R*y)*(R*y))+
        (star (R*y)*(R*y)-positiveCut (r^2) (b*b))+(positiveCut (r^2) (b*b)-b*b)‖ := by congr 1; abel
      _≤‖star (b*t)*(b*t)-star (R*y)*(R*y)‖+
        ‖star (R*y)*(R*y)-positiveCut (r^2) (b*b)‖+‖positiveCut (r^2) (b*b)-b*b‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _< (4+δ)*δ+δ+r^2 := by rw [norm_sub_rev (positiveCut _ (b*b)) (b*b)]; linarith
      _< ε := by linarith
  refine ⟨s,t,?_,?_,?_⟩
  · simpa only [star_mul,ha.star_eq,mul_assoc] using haerr
  · simpa only [star_mul,hb.star_eq,mul_assoc] using hberr
  · have hn : ‖star (a*s)*(b*t)‖ ≤ (4+δ)*δ+ε/4 := by
      calc
        _=‖(star (a*s)*(b*t)-star (Q*x)*(R*y))+star (Q*x)*(R*y)‖ := by rw [sub_add_cancel]
        _≤‖star (a*s)*(b*t)-star (Q*x)*(R*y)‖+‖star (Q*x)*(R*y)‖ := norm_add_le _ _
        _≤_ := add_le_add hst hcross
    have : ‖star (a*s)*(b*t)‖ < ε := by linarith
    simpa only [star_mul,ha.star_eq,mul_assoc] using this

end

end WeakPureInfiniteness
end

end OAI
