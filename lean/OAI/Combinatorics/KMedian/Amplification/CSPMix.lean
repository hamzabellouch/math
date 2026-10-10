import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringObjects
import OAI.Combinatorics.KMedian.Expanders.GraphMix
import OAI.Combinatorics.KMedian.PCP.AlphabetReduction

namespace OAI

section Inline_PCPCSPMix

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V D S A : Type} [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} {H : PortGraph V S}
variable (C : PortCSP G A) (K : PortCSP H A)

noncomputable def blend : PortCSP (G.blend H) A where
  allowed p := if p.2.1=0 then C.allowed (p.1,p.2.2.1) else K.allowed (p.1,p.2.2.2)
  symmetric := by
    rintro ⟨v,i,d,s⟩ a b
    change (a,b) ∈ (if (PortGraph.blendRotate G H (v,i,d,s)).2.1=0 then
      C.allowed ((PortGraph.blendRotate G H (v,i,d,s)).1,(PortGraph.blendRotate G H (v,i,d,s)).2.2.1)
      else K.allowed ((PortGraph.blendRotate G H (v,i,d,s)).1,(PortGraph.blendRotate G H (v,i,d,s)).2.2.2)) ↔ _
    by_cases hi : i=0
    · simpa only [PortGraph.blendRotate,hi,ite_true,PortGraph.step,PortGraph.back,Prod.eta] using C.symmetric (v,d) a b
    · simpa only [PortGraph.blendRotate,hi,ite_false,PortGraph.step,PortGraph.back,Prod.eta] using K.symmetric (v,s) a b

omit [Fintype A] [DecidableEq A] in
@[simp] lemma blend_bad (a : V → A) (v : V) (i : Fin 3) (d : D) (s : S) :
    (C.blend K).Bad a (v,i,d,s) ↔ if i=0 then C.Bad a (v,d) else K.Bad a (v,s) := by
  unfold Bad
  rw [PortGraph.blend_step]
  change _ ∉ (if i=0 then _ else _) ↔ _
  by_cases hi : i=0 <;> simp only [hi,ite_true,ite_false]

omit [Fintype A] [DecidableEq A] in
lemma blend_complete (a : V → A) (hc : C.Satisfies a) (hk : K.Satisfies a) :
    (C.blend K).Satisfies a := by
  rintro v ⟨i,d,s⟩
  have hh : ¬ (C.blend K).Bad a (v,i,d,s) := by
    rw [blend_bad]
    by_cases hi : i=0
    · simpa only [hi,ite_true,Bad,not_not] using hc v d
    · simpa only [hi,ite_false,Bad,not_not] using hk v s
  exact not_not.mp hh

variable [Fintype V] [Fintype D] [Nonempty D] [Fintype S] [Nonempty S]

omit [Fintype A] [DecidableEq A] in
lemma blend_failure (a : V → A) : testRate ((C.blend K).Bad a) =
    (testRate (C.Bad a)+2*testRate (K.Bad a))/3 := by
  have hp := testRate_congr (fun p : V × PortGraph.BlendPort (D := D) (S := S) =>
    C.blend_bad K a p.1 p.2.1 p.2.2.1 p.2.2.2)
  rw [hp]
  unfold testRate
  rw [expect_prod]
  simp_rw [expect_prod]
  have hv (v : V) :
      (𝔼 i : Fin 3, 𝔼 d : D, 𝔼 s : S,
        if (if i=0 then C.Bad a (v,d) else K.Bad a (v,s)) then (1:ℝ) else 0) =
      ((𝔼 d : D, if C.Bad a (v,d) then (1:ℝ) else 0)+
        2*(𝔼 s : S, if K.Bad a (v,s) then (1:ℝ) else 0))/3 := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [Fintype.card_fin,Nat.cast_ofNat,Fin.sum_univ_succ,Fin.isValue,ite_true,
      Fin.succ_ne_zero,ite_false,Fintype.expect_const,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    ring
  simp_rw [hv]
  rw [← expect_div,expect_add_distrib,← mul_expect]
  congr 2
  · apply expect_congr rfl
    intro v _
    apply expect_congr rfl
    intro d _
    split_ifs <;> rfl
  · congr 1
    apply expect_congr rfl
    intro v _
    apply expect_congr rfl
    intro d _
    split_ifs <;> rfl

end PortCSP

namespace PortCSP
variable {V D A : Type} [Fintype A] [DecidableEq A] (G : PortGraph V D)
def always : PortCSP G A where
  allowed _ := univ
  symmetric _ _ _ := by simp

omit [DecidableEq A] in
@[simp] lemma always_complete (a : V → A) : (always (A := A) G).Satisfies a := by
  intro v d
  exact mem_univ _

omit [DecidableEq A] in
@[simp] lemma always_bad (a : V → A) (p : V × D) : ¬(always (A := A) G).Bad a p := by
  simp [Bad,always]

omit [DecidableEq A] in
@[simp] lemma always_failure [Fintype V] [Fintype D] (a : V → A) :
    testRate ((always (A := A) G).Bad a)=0 := by
  exact (testRate_eq_zero_iff _).mpr (always_bad G a)

end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPMix

end OAI
