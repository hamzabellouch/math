import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import OAI.Analysis.FactorGeneration.Bicommutant

namespace OAI

noncomputable section

namespace Generator

/-! A separated idempotent is recovered from commutation with a norm-small
perturbation. This is an elementary substitute for the spectral-cut step. -/
section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem offDiagonal_eq_zero_of_gap (p t x : A) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a)
    (hx : Commute (a • p+t) x) : p*x*(1-p)=0 := by
  let y := p*x*(1-p)
  have hleft : p*(a • p+t) = a • p+p*t := by
    rw [mul_add,mul_smul_comm,hp]
  have hright : (a • p+t)*(1-p)=t*(1-p) := by
    rw [add_mul,smul_mul_assoc,mul_sub,mul_one,hp,sub_self,smul_zero,zero_add]
  have he := congrArg (fun z : A => p*z*(1-p)) hx.eq
  have hy : a • y = y*t-t*y := by
    have ht : t*(1-p)=(1-p)*t := by
      rw [mul_sub,sub_mul,mul_one,one_mul,hpt.eq]
    have h : a • y+t*y=y*t := by
      calc a • y+t*y = (p*(a • p+t))*x*(1-p) := by
             rw [hleft,add_mul,add_mul,smul_mul_assoc,smul_mul_assoc]
             dsimp [y]
             rw [hpt.eq]
             simp only [mul_assoc]
        _ = p*((a • p+t)*x)*(1-p) := by simp only [mul_assoc]
        _ = p*(x*(a • p+t))*(1-p) := he
        _ = y*t := by
          simp only [mul_assoc]
          rw [hright,ht]
          simp only [y,mul_assoc]
    exact eq_sub_of_add_eq' (by simpa only [add_comm] using h)
  have han : 0 ≤ a := (mul_nonneg (by norm_num) (norm_nonneg t)).trans ha.le
  have hn : a*‖y‖ ≤ 2*‖t‖*‖y‖ := by
    calc a*‖y‖ = ‖a • y‖ := by rw [norm_smul,Real.norm_of_nonneg han]
      _ = ‖y*t-t*y‖ := congrArg norm hy
      _ ≤ ‖y*t‖+‖t*y‖ := norm_sub_le _ _
      _ ≤ ‖y‖*‖t‖+‖t‖*‖y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2*‖t‖*‖y‖ := by ring
  have hz : ‖y‖=0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp hz

theorem commute_projection_of_gap (p t x : A) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a)
    (hx : Commute (a • p+t) x) : Commute p x := by
  have h₁ := offDiagonal_eq_zero_of_gap p t x hp hpt a ha hx
  have hcp : (1-p)*(1-p)=1-p := by noncomm_ring [hp]
  have hcpt : Commute (1-p) (-t) := ((Commute.one_left t).sub_left hpt).neg_right
  have hcx : Commute (a • (1-p)+ -t) x := by
    have he : a • (1-p)+ -t = a • (1 : A)-(a • p+t) := by
      rw [smul_sub]; abel
    rw [he]
    exact ((Commute.one_left x).smul_left a).sub_left hx
  have h₂ := offDiagonal_eq_zero_of_gap (1-p) (-t) x hcp hcpt a
    (by simpa only [norm_neg] using ha) hcx
  simp only [sub_sub_cancel] at h₂
  show p*x=x*p
  have h₁' : p*x=p*x*p := by simpa only [mul_sub,mul_one,sub_eq_zero] using h₁
  have h₂' : x*p=p*x*p := by simpa only [sub_mul,one_mul,sub_eq_zero] using h₂
  exact h₁'.trans h₂'.symm

end

/-! Countably many commuting projections have one self-adjoint generator.
We use coefficients 3*4^(-(n+1)), whose strict gap admits direct norm recovery
through the double commutant. No trace, tensor model, or uniqueness is used. -/
namespace CommutingProjectionEncoding
open scoped BigOperators Topology
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def weight (n : ℕ) : ℝ := (3/4)*(1/4)^n

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

theorem weight_hasSum (n : ℕ) :
    HasSum (fun k => weight (n+k)) ((1/4 : ℝ)^n) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) < 1)).mul_left ((3/4:ℝ)*(1/4)^n)
  convert! h using 1
  · ext k; simp only [weight,pow_add]; ring
  · ring

def tail (e : ℕ → (H →L[ℂ] H)) (n : ℕ) : (H →L[ℂ] H) := ∑' k, weight (n+k) • e (n+k)

variable (e : ℕ → (H →L[ℂ] H)) (hp : ∀ n, IsStarProjection (e n))
include hp

theorem term_norm_le (n k : ℕ) : ‖(weight (n+k) • e (n+k) : (H →L[ℂ] H))‖ ≤ weight (n+k) := by
  rw [norm_smul,Real.norm_of_nonneg (weight_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (hp (n+k)).norm_le (weight_nonneg _)).trans_eq (mul_one _)

theorem tail_summable (n : ℕ) : Summable (fun k => (weight (n+k) • e (n+k) : (H →L[ℂ] H))) := by
  exact (weight_hasSum n).summable.of_norm_bounded (term_norm_le e hp n)

theorem tail_norm_le (n : ℕ) : ‖tail e n‖ ≤ (1/4 : ℝ)^n :=
  tsum_of_norm_bounded (weight_hasSum n) (term_norm_le e hp n)

theorem tail_step (n : ℕ) : tail e n = weight n • e n + tail e (n+1) := by
  have h := (tail_summable e hp n).tsum_eq_zero_add
  simpa only [tail,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem tail_selfAdjoint (n : ℕ) : IsSelfAdjoint (tail e n) := by
  have h := (tail_summable e hp n).hasSum.star
  simp only [star_smul,star_trivial,(hp _).isSelfAdjoint.star_eq] at h
  exact h.unique (tail_summable e hp n).hasSum

theorem tail_mem (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
    (he : ∀ n, e n ∈ S) (n : ℕ) : tail e n ∈ S := by
  apply (wotClosed_normClosed S hS).mem_of_tendsto (tail_summable e hp n).hasSum
  exact Eventually.of_forall fun s => S.sum_mem fun k _ => by
    rw [← Complex.coe_smul]
    exact S.smul_mem (he (n+k)) _

variable (hc : ∀ i j, Commute (e i) (e j))
include hc

omit hp [CompleteSpace H] in
theorem projection_commutes_tail (i n : ℕ) : Commute (e i) (tail e n) :=
  Commute.tsum_right _ fun k => (hc i (n+k)).smul_right _

theorem projection_mem_of_tail_mem (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
    (n : ℕ) (ht : tail e n ∈ S) : e n ∈ S := by
  change e n ∈ (S : Set (H →L[ℂ] H))
  rw [← wotClosed_bicommutant S hS]
  intro x hx
  have hxt : Commute (weight n • e n+tail e (n+1)) x := by
    rw [← tail_step e hp n]
    exact hx _ ht
  have hgap : 2*‖tail e (n+1)‖ < weight n := by
    have h := tail_norm_le e hp (n+1)
    have hn : 0 < (1/4:ℝ)^n := by positivity
    dsimp [weight]
    rw [pow_succ] at h
    nlinarith
  exact (commute_projection_of_gap (e n) (tail e (n+1)) x
    (hp n).isIdempotentElem.eq (projection_commutes_tail e hc n (n+1))
    (weight n) hgap hxt).eq.symm

theorem projection_mem_wstar (n : ℕ) : e n ∈ wstar {tail e 0} := by
  let S := wstar {tail e 0}
  have hS : WOTClosed S := wstar_closed _
  have ht : ∀ k, tail e k ∈ S := by
    intro k
    induction k with
    | zero => exact subset_wstar _ (Set.mem_singleton _)
    | succ k ih =>
      have he := projection_mem_of_tail_mem e hp hc S hS k ih
      have hs : weight k • e k ∈ S := by
        rw [← Complex.coe_smul]
        exact S.smul_mem he _
      have h := S.sub_mem ih hs
      rw [tail_step e hp k,add_sub_cancel_left] at h
      exact h
  exact projection_mem_of_tail_mem e hp hc S hS n (ht n)

theorem wstar_encoding : wstar {tail e 0} = wstar (Set.range e) := by
  apply le_antisymm
  · apply wstar_le (wstar_closed _)
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact tail_mem e hp (wstar (Set.range e)) (wstar_closed _)
      (fun n => subset_wstar (Set.range e) (Set.mem_range_self n)) 0
  · apply wstar_le (wstar_closed _)
    rintro x ⟨n,rfl⟩
    exact projection_mem_wstar e hp hc n

/-- Countable commuting-projection encoding without additional structural hypotheses. -/
theorem exists_selfAdjoint_generator :
    ∃ b : (H →L[ℂ] H), IsSelfAdjoint b ∧ ‖b‖ ≤ 1 ∧ wstar {b}=wstar (Set.range e) :=
  ⟨tail e 0,tail_selfAdjoint e hp 0,by simpa using tail_norm_le e hp 0,
    wstar_encoding e hp hc⟩

end CommutingProjectionEncoding

/-! The spectral separation step as an exact membership theorem for literal W*. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem idempotent_mem_wstar_of_gap (p t : H →L[ℂ] H) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a) : p ∈ wstar {a • p+t} := by
  let S := wstar {a • p+t}
  change p ∈ (S : Set (H →L[ℂ] H))
  rw [← wotClosed_bicommutant S (wstar_closed _)]
  intro x hx
  exact (commute_projection_of_gap p t x hp hpt a ha
    (hx _ (subset_wstar _ rfl))).eq.symm

end Generator

end

end OAI
