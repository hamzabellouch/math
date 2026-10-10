import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.FiniteCoefficients

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter
open scoped Topology ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
variable (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
variable (hcmp : StrictComparison A) (hnuc : IsNuclear A)
local notation "τ" => (fun t : TracialState A => t)
local notation "D" => FamilyUltrapower τ U
local notation "Λ" => familyLimitTrace τ U
include hfree hsimple hinf hcmp hnuc in
theorem comparison_dyadic_approximation (S : Set D) (hS : S.Countable) (n : ℕ)
    {r : D} (hr : IsStarProjection r) (hrc : ∀ a ∈ S, Commute r a)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∃ p : D, ∃ α : ℝ, IsStarProjection p ∧ p ≤ r ∧ α ∈ Set.Icc 0 1 ∧
      |α-t| ≤ (1/2:ℝ)^n ∧ ∀ a ∈ S, Commute p a ∧ ∀ s : ℕ → TracialState A,
      (Λ s).functional (p*a)=(α:ℂ)*(Λ s).functional (r*a) := by
  induction n generalizing r t with
  | zero =>
    refine ⟨0,0,IsStarProjection.zero _,hr.nonneg,⟨le_rfl,zero_le_one⟩,?_,?_⟩
    · simpa only [zero_sub,abs_neg,abs_of_nonneg ht.1,pow_zero] using ht.2
    · intro a ha
      exact ⟨Commute.zero_left a,by intro s; simp⟩
  | succ n ih =>
    obtain ⟨h,hh,hhr,hht⟩ := comparison_corner_halving U hfree hsimple hinf hcmp hnuc S hS hr hrc
    have hhc : ∀ a ∈ S, Commute h a := fun a ha => (hht a ha).1
    by_cases ht2 : t ≤ 1/2
    · have h2t : 2*t ∈ Set.Icc 0 1 := ⟨by linarith [ht.1],by linarith⟩
      obtain ⟨p,α,hp,hph,hα,herr,hpt⟩ := ih hh hhc h2t
      refine ⟨p,α/2,hp,hph.trans hhr,⟨by linarith [hα.1],by linarith [hα.2]⟩,?_,?_⟩
      · rw [abs_sub_le_iff] at herr ⊢
        rw [pow_succ]
        constructor <;> nlinarith [herr.1,herr.2]
      · intro a ha
        refine ⟨(hpt a ha).1,?_⟩
        intro s
        rw [(hpt a ha).2 s,(hht a ha).2 s]
        push_cast
        ring
    · have ht2' : 1/2 ≤ t := (lt_of_not_ge ht2).le
      have h2t : 2*t-1 ∈ Set.Icc 0 1 := ⟨by linarith,by linarith [ht.2]⟩
      have hhr' : h*r=h := (hh.le_iff_mul_eq_left hr).mp hhr
      have hrem : IsStarProjection (r-h) := hh.sub_of_mul_eq_left hr hhr'
      have hremc : ∀ a ∈ S, Commute (r-h) a := fun a ha => (hrc a ha).sub_left (hhc a ha)
      obtain ⟨p,α,hp,hprem,hα,herr,hpt⟩ := ih hrem hremc h2t
      have hremp : (r-h)*p=p := (hp.le_iff_mul_eq_right hrem).mp hprem
      have horth : h*p=0 := by
        calc
          h*p=h*((r-h)*p) := by rw [hremp]
          _=(h*(r-h))*p := (mul_assoc _ _ _).symm
          _=0 := by rw [mul_sub,hhr',hh.isIdempotentElem.eq,sub_self,zero_mul]
      have hsum : h+p ≤ r := by
        have hhadd := add_le_add_left hprem h
        simpa only [sub_add_cancel,add_comm p h] using hhadd
      refine ⟨h+p,(1+α)/2,hh.add hp horth,hsum,
        ⟨by linarith [hα.1],by linarith [hα.2]⟩,?_,?_⟩
      · rw [abs_sub_le_iff] at herr ⊢
        rw [pow_succ]
        constructor <;> nlinarith [herr.1,herr.2]
      · intro a ha
        refine ⟨(hhc a ha).add_left (hpt a ha).1,?_⟩
        intro s
        rw [add_mul,map_add,(hpt a ha).2 s,sub_mul,map_sub,(hht a ha).2 s]
        push_cast
        ring

end DirectComparison
end
end

end OAI
