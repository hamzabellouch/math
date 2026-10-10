import Mathlib
import OAI.Probability.SKGap.Stability.Ordinary

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D : Type*}

def Paired.consDiag (a : D) (F : List (Letter D)) (d : Paired F) : Paired (.diag a::F) :=
  ⟨.diag a d.val,by simp [word,d.property]⟩
lemma Paired.consDiag_bijective (a : D) (F : List (Letter D)) :
    Function.Bijective (Paired.consDiag a F) := by
  constructor
  · intro d e h
    apply Subtype.ext
    exact (Diagram.diag.inj (congrArg Subtype.val h)).2
  · intro ⟨d,hd⟩
    cases d with
    | nil => simp [word] at hd
    | arch u v => simp [word] at hd
    | diag b d =>
      change Letter.diag b::d.word=Letter.diag a::F at hd
      obtain ⟨hab,hword⟩ := List.cons.inj hd
      have hab := Letter.diag.inj hab
      subst b
      exact ⟨⟨d,hword⟩,rfl⟩
def Paired.consDiagEquiv (a : D) (F : List (Letter D)) : Paired F ≃ Paired (.diag a::F) :=
  Equiv.ofBijective _ (Paired.consDiag_bijective a F)
def Paired.appendDiag (a : D) (F : List (Letter D)) (d : Paired F) : Paired (F++[.diag a]) :=
  ⟨d.val.append (.diag a .nil),by simp [append_word,d.property,word]⟩
lemma Paired.appendDiag_bijective (a : D) (F : List (Letter D)) :
    Function.Bijective (Paired.appendDiag a F) := by
  constructor
  · intro d e h
    apply Subtype.ext
    exact append_last_diag_injective a (congrArg Subtype.val h)
  · intro ⟨d,hd⟩
    obtain ⟨e,he,hde⟩ := remove_last_diag d F a hd
    exact ⟨⟨e,he⟩,Subtype.ext hde.symm⟩
def Paired.appendDiagEquiv (a : D) (F : List (Letter D)) : Paired F ≃ Paired (F++[.diag a]) :=
  Equiv.ofBijective _ (Paired.appendDiag_bijective a F)
instance pairedNilUnique : Unique (Paired ([] : List (Letter D))) where
  default := ⟨.nil,rfl⟩
  uniq d := by
    apply Subtype.ext
    have h := d.property
    cases hd : d.val <;> simp_all [word]

variable {ι : Type*} [Fintype ι]
@[simp] lemma expect_nil (j : ℝ) (v : D→ι→ℝ) (i : ι) : expect j v [] i=1 := by
  rw [expect,Fintype.sum_unique]
  rfl
@[simp] lemma expect_cons_diag (j : ℝ) (v : D→ι→ℝ) (a : D) (F : List (Letter D)) (i : ι) :
    expect j v (.diag a::F) i=v a i*expect j v F i := by
  unfold expect
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Paired.consDiagEquiv a F)
  intro d
  rfl
@[simp] lemma expect_append_diag (j : ℝ) (v : D→ι→ℝ) (a : D) (F : List (Letter D)) (i : ι) :
    expect j v (F++[.diag a]) i=expect j v F i*v a i := by
  unfold expect
  rw [Finset.sum_mul]
  symm
  apply Fintype.sum_equiv (Paired.appendDiagEquiv a F)
  intro d
  simp [Paired.appendDiagEquiv,Paired.appendDiag,evaluate,map_append,map,value_append,value]
end Diagram
namespace WordSeries
open Diagram InverseDiagram
variable {ι : Type*} [Fintype ι]
@[simp] lemma ordinary_nil (j : ℝ) (i : ι) : ordinary j [] i=1 := expect_nil j id i
@[simp] lemma ordinary_cons_diag (j : ℝ) (d : ι→ℝ) (F : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (.diag d::F) i=d i*ordinary j F i := expect_cons_diag j id d F i
@[simp] lemma ordinary_append_diag (j : ℝ) (d : ι→ℝ) (F : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (F++[.diag d]) i=ordinary j F i*d i := expect_append_diag j id d F i

lemma ordinary_diag_prefix (j : ℝ) (D : List (ι→ℝ)) (F : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (D.map Letter.diag++F) i=(D.map (fun d=>d i)).prod*ordinary j F i := by
  induction D with
  | nil => simp
  | cons d D ih => simp [ih,mul_assoc]
lemma ordinary_diag_suffix (j : ℝ) (D : List (ι→ℝ)) (F : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (F++D.map Letter.diag) i=ordinary j F i*(D.map (fun d=>d i)).prod := by
  induction D using List.reverseRecOn with
  | nil => simp
  | append_singleton D d ih =>
    simp only [List.map_append,List.map_singleton,List.prod_append,List.prod_singleton]
    rw [← List.append_assoc,ordinary_append_diag,ih,mul_assoc]
lemma inverseCoefficient_diagonal (j : ℝ) (a : ι→ℝ) (P Q : List (ι→ℝ)) (n : ℕ) (i : ι) :
    inverseCoefficient j a (P.map Letter.diag) (Q.map Letter.diag) n i=
      if n=0 then (P.map (fun d=>d i)).prod*(Q.map (fun d=>d i)).prod else 0 := by
  have he : inverseCoefficient j a (P.map Letter.diag) (Q.map Letter.diag) n i=
      (P.map (fun d=>d i)).prod*inverseCoefficient j a [] [] n i*(Q.map (fun d=>d i)).prod := by
    simp only [inverseCoefficient,List.nil_append,List.append_nil,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro bs _
    rw [List.append_assoc,ordinary_diag_prefix,ordinary_diag_suffix]
    ring
  rw [he,inverseCoefficient_empty]
  split_ifs <;> ring
end WordSeries
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
