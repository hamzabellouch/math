import Mathlib
import OAI.Probability.SKGap.Matrix.WordBaseBias
import OAI.Probability.SKGap.Terminal.ConsDiag
import OAI.Probability.SKGap.Matrix.InverseSeries

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
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*} [Fintype ι]

@[simp] lemma literalSeries_lift_append (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++liftWord Q) i=C (ordinary j (P++Q) i) := by
  rw [← liftWord_append,literalSeries_lift]
@[simp] lemma literalSeries_two_prefix (j : ℝ) (a : ι→ℝ)
    (P R Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++(liftWord R++(.inverse::liftWord Q))) i=
      inverseSeries j a (P++R) Q i := by
  rw [← List.append_assoc,← liftWord_append,literalSeries_oneInverse]
@[simp] lemma literalSeries_two_suffix (j : ℝ) (a : ι→ℝ)
    (P Q R : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a ((liftWord P++(.inverse::liftWord Q))++liftWord R) i=
      inverseSeries j a P (Q++R) i := by
  rw [List.append_assoc,List.cons_append,← liftWord_append,literalSeries_oneInverse]
@[simp] lemma literalSeries_cons_inverse (j : ℝ) (a : ι→ℝ)
    (Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (.inverse::liftWord Q) i=inverseSeries j a [] Q i := by
  exact literalSeries_oneInverse j a [] Q i

@[simp] lemma literalSeries_lift_fun (j : ℝ) (a : ι→ℝ) (F : List (Letter (ι→ℝ))) :
    literalSeries j a (liftWord F)=(fun i=>C (ordinary j F i)) := by
  funext i; exact literalSeries_lift j a F i
@[simp] lemma literalSeries_oneInverse_fun (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) :
    literalSeries j a (liftWord P++(.inverse::liftWord Q))=inverseSeries j a P Q := by
  funext i; exact literalSeries_oneInverse j a P Q i
@[simp] lemma literalSeries_inverse_diag_fun (j : ℝ) (a : ι→ℝ)
    (P : List (Letter (ι→ℝ))) :
    literalSeries j a (liftWord P++[.inverse,.diag a])=inverseSeries j a P [.diag a] := by
  exact literalSeries_oneInverse_fun j a P [.diag a]
@[simp] lemma literalSeries_inverse_single_append (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) :
    literalSeries j a (liftWord P++([.inverse]++liftWord Q))=inverseSeries j a P Q := by
  exact literalSeries_oneInverse_fun j a P Q
@[simp] lemma literalSeries_cons_inverse_fun (j : ℝ) (a : ι→ℝ)
    (Q : List (Letter (ι→ℝ))) :
    literalSeries j a (.inverse::liftWord Q)=inverseSeries j a [] Q := by
  exact literalSeries_oneInverse_fun j a [] Q

@[simp] lemma literalSeries_inverse_diag_suffix (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) :
    literalSeries j a ((liftWord P++[.inverse,.diag a])++liftWord Q)=
      inverseSeries j a P (.diag a::Q) := by
  rw [List.append_assoc]
  exact literalSeries_oneInverse_fun j a P (.diag a::Q)

lemma literalSeries_at_noInverse (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++(.noise::liftWord Q)) i=
      ((wordRecursionAt a (liftWord P) (liftWord Q)).map (fun t=>
        (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
          literalSeries j a t.outer i)).sum := by
  rw [show liftWord P++(.noise::liftWord Q)=liftWord (P++(.noise::Q)) by
    simp [liftWord,Letter.toWord]]
  simp only [wordRecursionAt,List.map_append,List.sum_append,List.map_map,
    WordCut.asLeft,WordCut.asRight,Function.comp_def]
  rw [sum_wordPartners_lift,sum_wordPartners_lift]
  simp only [Bool.false_eq_true,↓reduceIte,one_mul,literalSeries_lift,literalSeries_lift_append,
    literalSeries_lift_fun,meanSeries_C]
  have hh := congrArg C (expect_at j (id : (ι→ℝ)→ι→ℝ) P Q i)
  simpa only [map_add,map_sum,map_mul,ordinary,mul_assoc] using hh

lemma literalSeries_at_rightInverse (j : ℝ) (a : ι→ℝ)
    (P R T : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++(.noise::(liftWord R++(.inverse::liftWord T)))) i=
      ((wordRecursionAt a (liftWord P) (liftWord R++(.inverse::liftWord T))).map (fun t=>
        (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
          literalSeries j a t.outer i)).sum := by
  rw [show liftWord P++(.noise::(liftWord R++(.inverse::liftWord T)))=
      liftWord (P++(.noise::R))++(.inverse::liftWord T) by
    simp [liftWord,Letter.toWord,List.append_assoc]]
  simp only [wordRecursionAt,List.map_append,List.sum_append,List.map_map,
    WordCut.asLeft,WordCut.asRight,Function.comp_def]
  rw [sum_wordPartners_lift,sum_wordPartners_oneInverse]
  simp only [Bool.false_eq_true,↓reduceIte,one_mul,literalSeries_lift_append,
    literalSeries_oneInverse,literalSeries_two_prefix,literalSeries_oneInverse_fun,
    literalSeries_inverse_diag_fun,literalSeries_inverse_single_append,literalSeries_lift_fun,meanSeries_C]
  simpa only [map_mul,mul_assoc,add_assoc] using inverseSeries_right j a P R T i

lemma literalSeries_at_leftInverse (j : ℝ) (a : ι→ℝ)
    (P R T : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a ((liftWord P++(.inverse::liftWord R))++(.noise::liftWord T)) i=
      ((wordRecursionAt a (liftWord P++(.inverse::liftWord R)) (liftWord T)).map (fun t=>
        (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
          literalSeries j a t.outer i)).sum := by
  rw [show (liftWord P++(.inverse::liftWord R))++(.noise::liftWord T)=
      liftWord P++(.inverse::liftWord (R++(.noise::T))) by
    simp [liftWord,Letter.toWord,List.append_assoc]]
  simp only [wordRecursionAt,List.map_append,List.sum_append,List.map_map,
    WordCut.asLeft,WordCut.asRight,Function.comp_def]
  rw [sum_wordPartners_oneInverse,sum_wordPartners_lift]
  simp only [Bool.false_eq_true,↓reduceIte,one_mul,literalSeries_lift_append,
    literalSeries_oneInverse,literalSeries_two_suffix,literalSeries_oneInverse_fun,
    literalSeries_inverse_diag_suffix,List.singleton_append,literalSeries_cons_inverse_fun,
    literalSeries_lift_fun,meanSeries_C]
  have hh := inverseSeries_left j a P R T i
  simp only [map_mul,mul_assoc,add_assoc] at hh ⊢
  exact hh

lemma literalSeries_at (j : ℝ) (a : ι→ℝ) (P Q : List (WordLetter ι))
    (hI : inverseCount (P++(.noise::Q))≤1) (i : ι) :
    literalSeries j a (P++(.noise::Q)) i=
      ((wordRecursionAt a P Q).map (fun t=>
        (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
          literalSeries j a t.outer i)).sum := by
  have hP : inverseCount P≤1 := by simp only [inverseCount_append,inverseCount_noise] at hI; omega
  have hQ : inverseCount Q≤1 := by simp only [inverseCount_append,inverseCount_noise] at hI; omega
  rcases one_inverse_cases P hP with ⟨P,rfl⟩ | ⟨P,R,rfl⟩
  · rcases one_inverse_cases Q hQ with ⟨Q,rfl⟩ | ⟨R,T,rfl⟩
    · exact literalSeries_at_noInverse j a P Q i
    · exact literalSeries_at_rightInverse j a P R T i
  · have hQ0 : inverseCount Q=0 := by
      simp only [inverseCount_append,inverseCount_inverse,inverseCount_noise,inverseCount_lift] at hI
      omega
    obtain ⟨T,rfl⟩ := exists_lift_of_no_inverse Q hQ0
    exact literalSeries_at_leftInverse j a P R T i

end SKGap.Noncrossing

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma exists_diagonals_of_count_zero (F : List (Letter (ι→ℝ)))
    (h : ordinaryCount (liftWord F)=0) : ∃ D : List (ι→ℝ), D.map Letter.diag=F := by
  induction F with
  | nil => exact ⟨[],rfl⟩
  | cons l F ih =>
    cases l with
    | noise => simp [liftWord,Letter.toWord,ordinaryCount] at h
    | diag d =>
      have ht : ordinaryCount (liftWord F)=0 := by simpa [liftWord,Letter.toWord,ordinaryCount] using h
      obtain ⟨D,rfl⟩ := ih ht
      exact ⟨d::D,rfl⟩

omit [Fintype ι] in
@[simp] lemma wordDiagonal_diags (D : List (ι→ℝ)) (i : ι) :
    wordDiagonal (liftWord (D.map Letter.diag)) i=(D.map (fun d=>d i)).prod := by
  simp [wordDiagonal,liftWord,Function.comp_def,Letter.toWord]
omit [Fintype ι] in
@[simp] lemma wordDiagonal_append (P Q : List (WordLetter ι)) (i : ι) :
    wordDiagonal (P++Q) i=wordDiagonal P i*wordDiagonal Q i := by simp [wordDiagonal]
omit [Fintype ι] in
@[simp] lemma wordDiagonal_inverse (Q : List (WordLetter ι)) (i : ι) :
    wordDiagonal (.inverse::Q) i=wordDiagonal Q i := by simp [wordDiagonal]

lemma literalSeries_base (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι))
    (hI : inverseCount F≤1) (ho : ordinaryCount F=0) (i : ι) :
    literalSeries j a F i=C (wordDiagonal F i) := by
  rcases one_inverse_cases F hI with ⟨P,rfl⟩ | ⟨P,Q,rfl⟩
  · obtain ⟨D,rfl⟩ := exists_diagonals_of_count_zero P ho
    rw [literalSeries_lift,wordDiagonal_diags]
    congr 1
    simpa using ordinary_diag_prefix j D [] i
  · have hc : ordinaryCount (liftWord P)+ordinaryCount (liftWord Q)=0 := by
      simpa [ordinaryCount,List.countP_append] using ho
    obtain ⟨D,rfl⟩ := exists_diagonals_of_count_zero P (by omega)
    obtain ⟨E,rfl⟩ := exists_diagonals_of_count_zero Q (by omega)
    rw [literalSeries_oneInverse,wordDiagonal_append,wordDiagonal_inverse,wordDiagonal_diags,wordDiagonal_diags]
    ext n
    rw [coeff_inverseSeries,inverseCoefficient_diagonal,coeff_C]

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
end
end
end
end

end OAI
