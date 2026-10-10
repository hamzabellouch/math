import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ProjectiveHighCapturedMoment

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.DyadicMoments
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α]

theorem moment_cutoff_polynomial_tail (x : α → ℝ) (a : ι → ℝ) (T : Finset ι)
    (θ M A : ℝ) (K R : ℕ) (hK : K≠0) (hKR : K≤R)
    (hθ : 0≤θ) (hM : 0≤M) (hA : 0≤A)
    (hx : ∀ v,0≤x v) (hmax : ∀ v,x v≤M) (ha : ∀ i∈T,0<a i)
    (hcover : ∀ v,0<x v → ∃ i∈T,a i≤x v ∧ x v≤2*a i)
    (htail : ∀ i∈T,θ≤2*a i →
      ((Finset.univ.filter fun v => a i≤x v).card:ℝ)*a i^K≤A) :
    (∑ v,x v^R) ≤ (Fintype.card α:ℝ)*θ^R + M^(R-K)*(2^K*T.card*A) := by
  let y (v : α) : ℝ := if θ≤x v then x v else 0
  let U := T.filter fun i => θ≤2*a i
  have hy (v : α) : 0≤y v := by dsimp [y]; split_ifs; exact hx v; rfl
  have hym (v : α) : y v≤M := by dsimp [y]; split_ifs; exact hmax v; exact hM
  have hbase : (∑ v,y v^K) ≤ 2^K*U.card*A := by
    apply moment_polynomial_tail y a U K hK A hy
      (fun i hi => (ha i (Finset.mem_filter.mp hi).1).le)
    · intro v hv
      have hv' : θ≤x v := by by_contra hn; simp [y,hn] at hv
      have hpos : 0<x v := by simpa [y,hv'] using hv
      obtain ⟨i,hi,hlo,hhi⟩ := hcover v hpos
      exact ⟨i,Finset.mem_filter.mpr ⟨hi,hv'.trans hhi⟩,by simpa [y,hv'] using hlo,
        by simpa [y,hv'] using hhi⟩
    · intro i hi
      have hiT := (Finset.mem_filter.mp hi).1
      have hc : (Finset.univ.filter fun v => a i≤y v).card ≤
          (Finset.univ.filter fun v => a i≤x v).card := by
        apply Finset.card_le_card
        intro v hv
        have hv' := (Finset.mem_filter.mp hv).2
        have hyx : y v≤x v := by dsimp [y]; split_ifs; rfl; exact hx v
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv'.trans hyx⟩
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc)
        (pow_nonneg (ha i hiT).le K)).trans (htail i hiT (Finset.mem_filter.mp hi).2)
  have hbase' : (∑ v,y v^K) ≤ 2^K*T.card*A := by
    apply hbase.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (Finset.card_filter_le T _)) (by positivity)) hA
  have hhi := pow_sum_from_lower y M _ K R hM hKR hy hym hbase'
  have hpoint (v : α) : x v^R ≤ θ^R+y v^R := by
    by_cases hv : θ≤x v
    · simpa [y,hv] using (le_add_of_nonneg_left (a := x v^R) (pow_nonneg hθ R))
    · have hp := pow_le_pow_left₀ (hx v) (le_of_not_ge hv) R
      exact hp.trans (le_add_of_nonneg_right (pow_nonneg (hy v) R))
  calc
    _ ≤ ∑ v,(θ^R+y v^R) := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = (Fintype.card α:ℝ)*θ^R+∑ v,y v^R := by simp [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add_right hhi _

end SharpRamseyFive.DyadicMoments

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore DyadicMoments
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma radial_tail_le_localLines (x : ℙ K V) [Fintype (RadialLine x)]
    (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (Lines : Finset (Submodule K V))
    (hLines : ∀ l : RadialLine x,l.val∈Lines) :
    (Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)).card ≤
      (localLines S O δ a Lines x).card := by
  let A := Finset.univ.filter fun l : RadialLine x =>
      a ≤ (radialWeight x (outsideAt x S (O x)) δ l:ℝ)
  let E := localLines S O δ a Lines x
  let f (l : A) : E := ⟨l.val.val,by
    refine Finset.mem_filter.mpr ⟨hLines l.val,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_flatPoints _ _).mpr l.val.property.2
    · have hr := (Finset.mem_filter.mp l.property).2
      change a ≤ (δ:ℝ)*(((outsideAt x S (O x)).filter fun y => y.val.submodule ≤ l.val.val).card:ℝ) at hr
      rwa [outsideAt_filter_card] at hr⟩
  have hi : Function.Injective f := by
    intro l m he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : E => z.val) he))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

variable [∀ x : ℙ K V,Fintype (RadialLine x)]

lemma global_radial_tail (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (a : ℝ) (Lines : Finset (Submodule K V))
    (Q : Finset (ℙ K V)) (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines) :
    (Finset.univ.filter fun z : Σ x : Q,RadialLine x.val =>
      a ≤ (radialWeight z.1.val (outsideAt z.1.val S (O z.1.val)) δ z.2:ℝ)).card ≤
      ∑ A∈Lines,(richCenters S O δ a A).card := by
  have he : (Finset.univ.filter fun z : Σ x : Q,RadialLine x.val =>
      a ≤ (radialWeight z.1.val (outsideAt z.1.val S (O z.1.val)) δ z.2:ℝ)).card =
      ∑ x : Q,(Finset.univ.filter fun l : RadialLine x.val =>
        a ≤ (radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)).card := by
    simp only [Finset.card_filter,Fintype.sum_sigma]
  rw [he]
  calc
    _ ≤ ∑ x : Q,(localLines S O δ a Lines x.val).card :=
      Finset.sum_le_sum fun x _ => radial_tail_le_localLines x.val S O δ a Lines (hLines x.val x.property)
    _ = ∑ x∈Q,(localLines S O δ a Lines x).card := Finset.sum_coe_sort Q (fun x => (localLines S O δ a Lines x).card)
    _ ≤ _ := sum_localLines_le S O δ a Lines Q

theorem global_radial_moment (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (hδ : 0<δ) (θ A : ℝ) (hθ : 0≤θ) (hA : 0≤A)
    (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V))
    (hLines : ∀ x∈Q,∀ l : RadialLine x,l.val∈Lines)
    (htail : ∀ i∈Finset.range (Nat.clog 2 S.card+1),θ≤2*((δ:ℝ)*2^i) →
      (δ:ℝ)*2^i≤(δ:ℝ)*((Nat.card K:ℝ)+1) →
      (∑ l∈Lines,((richCenters S O δ ((δ:ℝ)*2^i) l).card:ℝ))*((δ:ℝ)*2^i)^2≤A)
    (J : ℕ) (hJ : 2≤J) :
    (∑ x : Q,∑ l : RadialLine x.val,(radialWeight x.val (outsideAt x.val S (O x.val)) δ l:ℝ)^J) ≤
      (∑ x : Q,(Fintype.card (RadialLine x.val):ℝ))*θ^J+
        ((δ:ℝ)*((Nat.card K:ℝ)+1))^(J-2)*(4*(Nat.clog 2 S.card+1)*A) := by
  let w (z : Σ x : Q,RadialLine x.val) : ℝ :=
    radialWeight z.1.val (outsideAt z.1.val S (O z.1.val)) δ z.2
  have hw (z : Σ x : Q,RadialLine x.val) : 0≤w z := NNReal.coe_nonneg _
  have hmax (z : Σ x : Q,RadialLine x.val) : w z≤(δ:ℝ)*((Nat.card K:ℝ)+1) := by
    have hc := training_line_card z.1.val (outsideAt z.1.val S (O z.1.val)) z.2
    change (δ:ℝ)*((RadialLine.trainingOnLine _ _).card:ℝ) ≤ _
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) δ.coe_nonneg
  have hcS (x : ℙ K V) : (outsideAt x S (O x)).card≤S.card := outsideAt_card_le x S (O x)
  have hcover (z : Σ x : Q,RadialLine x.val) (hp : 0<w z) :
      ∃ i∈Finset.range (Nat.clog 2 S.card+1),(δ:ℝ)*2^i≤w z ∧ w z≤2*((δ:ℝ)*2^i) := by
    obtain ⟨i,hi,hlo,hhi⟩ := radial_bounded_cover z.1.val (outsideAt z.1.val S (O z.1.val)) δ
      ((δ:ℝ)*((Nat.card K:ℝ)+1)) (fun l => hmax ⟨z.1,l⟩) z.2 hp
    refine ⟨i,?_,hlo,hhi⟩
    have hir := (Finset.mem_filter.mp hi).1
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp hir
    exact lt_of_lt_of_le this (Nat.add_le_add_right (Nat.clog_mono_right 2 (hcS z.1.val)) 1)
  have hh := moment_cutoff_polynomial_tail w (fun i : ℕ => (δ:ℝ)*2^i)
    (Finset.range (Nat.clog 2 S.card+1)) θ ((δ:ℝ)*((Nat.card K:ℝ)+1)) A 2 J
    (by norm_num) hJ hθ (by positivity) hA hw hmax
    (by intro i _; positivity) hcover (by
      intro i hi hcut
      by_cases hcap : (δ:ℝ)*2^i≤(δ:ℝ)*((Nat.card K:ℝ)+1)
      · have ht := global_radial_tail S O δ ((δ:ℝ)*2^i) Lines Q hLines
        have htr : ((Finset.univ.filter fun z : Σ x : Q,RadialLine x.val =>
            (δ:ℝ)*2^i≤w z).card:ℝ) ≤
            ∑ l∈Lines,((richCenters S O δ ((δ:ℝ)*2^i) l).card:ℝ) := by
          exact_mod_cast ht
        exact (mul_le_mul_of_nonneg_right htr (sq_nonneg _)).trans (htail i hi hcut hcap)
      · have he : (Finset.univ.filter fun z : Σ x : Q,RadialLine x.val => (δ:ℝ)*2^i≤w z)=∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro z hz
          exact hcap ((Finset.mem_filter.mp hz).2.trans (hmax z))
        simpa only [he,Finset.card_empty,Nat.cast_zero,zero_mul] using hA)
  simpa only [Fintype.sum_sigma,Finset.card_range,Nat.cast_add,Nat.cast_one,
    Fintype.card_sigma,Nat.cast_sum,show (2:ℝ)^2=4 by norm_num] using hh

end SharpRamseyFive.ScoreGeometry

end OAI
