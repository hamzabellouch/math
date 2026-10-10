import Mathlib
import OAI.Probability.SKGap.Matrix.WordPartnerContraction
import OAI.Probability.SKGap.Stability.OrdinaryCutLeft

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
namespace SKGap.Noncrossing.WordSeries
open Diagram InverseDiagram PowerSeries
variable {ι : Type*} [Fintype ι]

instance noiseSplitNilIsEmpty {D : Type*} : IsEmpty (NoiseSplit ([] : List (Letter D))) :=
  ⟨fun s => by have h := congrArg List.length s.word_eq; simp at h⟩

def inverseSeries (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (i : ι) : ℝ⟦X⟧ :=
  PowerSeries.mk (fun n => inverseCoefficient j a P Q n i)
def meanSeries (f : ι→ℝ⟦X⟧) : ℝ⟦X⟧ := C ((Fintype.card ι:ℝ)⁻¹)*(∑ i,f i)
@[simp] lemma coeff_inverseSeries (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) :
    coeff n (inverseSeries j a P Q i)=inverseCoefficient j a P Q n i := coeff_mk _ _
@[simp] lemma coeff_meanSeries (f : ι→ℝ⟦X⟧) (n : ℕ) :
    coeff n (meanSeries f)=mean (fun i=>coeff n (f i)) := by
  simp [meanSeries,mean,div_eq_mul_inv,mul_comm]
@[simp] lemma meanSeries_C (f : ι→ℝ) : meanSeries (fun i=>C (f i))=C (mean f) := by
  ext n
  simp only [coeff_meanSeries,coeff_C]
  split_ifs with hn
  · rfl
  · simp [mean]

lemma coeff_mul_fin (p q : ℝ⟦X⟧) (n : ℕ) :
    coeff n (p*q)=∑ k : Fin (n+1), coeff k.val p*coeff (n-k.val) q := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => coeff k p*coeff l q) n]
  exact (Fin.sum_univ_eq_sum_range (fun k => coeff k p*coeff (n-k) q) (n+1)).symm

lemma inverseSeries_right (j : ℝ) (a : ι→ℝ) (P R T : List (Letter (ι→ℝ))) (i : ι) :
    inverseSeries j a (P++(.noise::R)) T i =
      (∑ s : NoiseSplit P, C (j*mean (ordinary j s.after))*inverseSeries j a (s.before++R) T i) +
      (∑ s : NoiseSplit R, C (j*mean (ordinary j s.before))*inverseSeries j a (P++s.after) T i) +
      X*(C j*meanSeries (inverseSeries j a R [.diag a])*inverseSeries j a P T i) +
      (∑ s : NoiseSplit T, C j*meanSeries (inverseSeries j a R s.before)*C (ordinary j (P++s.after) i)) := by
  ext n
  cases n with
  | zero =>
    simp only [map_add,map_sum,coeff_inverseSeries,coeff_C_mul,coeff_mul_C,coeff_meanSeries,
      inverseCoefficient_zero,coeff_zero_X_mul,add_zero]
    simpa only [ordinary,List.append_assoc,List.nil_append,List.append_nil,Finset.univ_eq_empty,
      Finset.sum_empty,add_zero] using
      ordinary_cut_right j P R ([] : List (Letter (ι→ℝ))) T i
  | succ n =>
    simp only [map_add,map_sum,coeff_inverseSeries,coeff_C_mul,coeff_mul_C,coeff_meanSeries,
      coeff_succ_X_mul,coeff_mul_fin]
    exact inverseCoefficient_right j a P R T n i

lemma inverseSeries_left (j : ℝ) (a : ι→ℝ) (P R T : List (Letter (ι→ℝ))) (i : ι) :
    inverseSeries j a P (R++(.noise::T)) i =
      (∑ s : NoiseSplit P, C j*meanSeries (inverseSeries j a s.after R)*C (ordinary j (s.before++T) i)) +
      X*(C j*meanSeries (inverseSeries j a [] R)*inverseSeries j a P (.diag a::T) i) +
      (∑ s : NoiseSplit R, C (j*mean (ordinary j s.after))*inverseSeries j a P (s.before++T) i) +
      (∑ s : NoiseSplit T, C (j*mean (ordinary j s.before))*inverseSeries j a P (R++s.after) i) := by
  ext n
  cases n with
  | zero =>
    simp only [map_add,map_sum,coeff_inverseSeries,coeff_C_mul,coeff_mul_C,coeff_meanSeries,
      inverseCoefficient_zero,coeff_zero_X_mul,add_zero]
    simpa only [ordinary,List.append_assoc,List.nil_append,List.append_nil,Finset.univ_eq_empty,
      Finset.sum_empty,add_zero] using
      ordinary_cut_left j P ([] : List (Letter (ι→ℝ))) R T i
  | succ n =>
    simp only [map_add,map_sum,coeff_inverseSeries,coeff_C_mul,coeff_mul_C,coeff_meanSeries,
      coeff_succ_X_mul,coeff_mul_fin]
    rw [inverseCoefficient_left]
    congr 2
    congr 1
    apply Fintype.sum_equiv (Fin.revPerm (n := n+1))
    intro k
    simp only [Fin.revPerm_apply,Fin.val_rev]
    rw [show n+1-(k.val+1)=n-k.val by omega, Nat.sub_sub_self (Nat.le_of_lt_succ k.isLt)]

end SKGap.Noncrossing.WordSeries

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*}

def Letter.toWord : Letter (ι→ℝ)→WordLetter ι
  | .diag d => .diag d
  | .noise => .noise
def liftWord (F : List (Letter (ι→ℝ))) : List (WordLetter ι) := F.map Letter.toWord
@[simp] lemma liftWord_nil : liftWord ([] : List (Letter (ι→ℝ)))=[] := rfl
@[simp] lemma liftWord_cons (l : Letter (ι→ℝ)) (F : List (Letter (ι→ℝ))) :
    liftWord (l::F)=l.toWord::liftWord F := rfl
@[simp] lemma liftWord_append (P Q : List (Letter (ι→ℝ))) : liftWord (P++Q)=liftWord P++liftWord Q := List.map_append
@[simp] lemma inverseCount_lift (F : List (Letter (ι→ℝ))) : inverseCount (liftWord F)=0 := by
  induction F with
  | nil => rfl
  | cons l F ih => cases l <;> simpa [liftWord,Letter.toWord,inverseCount] using ih

lemma exists_lift_of_no_inverse (F : List (WordLetter ι)) (h : inverseCount F=0) :
    ∃ P : List (Letter (ι→ℝ)), liftWord P=F := by
  induction F with
  | nil => exact ⟨[],rfl⟩
  | cons l F ih =>
    cases l with
    | inverse => simp [inverseCount] at h
    | diag d =>
      obtain ⟨P,rfl⟩ := ih (by simpa [inverseCount] using h)
      exact ⟨.diag d::P,rfl⟩
    | noise =>
      obtain ⟨P,rfl⟩ := ih (by simpa [inverseCount] using h)
      exact ⟨.noise::P,rfl⟩

@[simp] lemma inverseCount_inverse (F : List (WordLetter ι)) :
    inverseCount (.inverse::F)=inverseCount F+1 := by simp [inverseCount]

lemma one_inverse_cases (F : List (WordLetter ι)) (h : inverseCount F≤1) :
    (∃ P, F=liftWord P) ∨ (∃ P Q, F=liftWord P++(.inverse::liftWord Q)) := by
  induction F with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons l F ih =>
    cases l with
    | inverse =>
      have hz : inverseCount F=0 := by rw [inverseCount_inverse] at h; omega
      obtain ⟨P,rfl⟩ := exists_lift_of_no_inverse F hz
      exact Or.inr ⟨[],P,rfl⟩
    | diag d =>
      have ht : inverseCount F≤1 := by simpa [inverseCount] using h
      rcases ih ht with ⟨P,rfl⟩ | ⟨P,Q,rfl⟩
      · exact Or.inl ⟨.diag d::P,rfl⟩
      · exact Or.inr ⟨.diag d::P,Q,rfl⟩
    | noise =>
      have ht : inverseCount F≤1 := by simpa [inverseCount] using h
      rcases ih ht with ⟨P,rfl⟩ | ⟨P,Q,rfl⟩
      · exact Or.inl ⟨.noise::P,rfl⟩
      · exact Or.inr ⟨.noise::P,Q,rfl⟩

def expandWord [Fintype ι] (j : ℝ) (a : ι→ℝ) (bs : List Bool) (F : List (WordLetter ι)) :=
  F.flatMap (fun l=>match l with
    | .diag d => [Letter.diag d]
    | .noise => [.noise]
    | .inverse => chain j a bs)
@[simp] lemma expandWord_lift [Fintype ι] (j : ℝ) (a : ι→ℝ) (bs : List Bool) (F : List (Letter (ι→ℝ))) :
    expandWord j a bs (liftWord F)=F := by
  induction F with
  | nil => rfl
  | cons l F ih => cases l <;> simp [expandWord,liftWord,Letter.toWord] at * <;> exact ih
@[simp] lemma expandWord_oneInverse [Fintype ι] (j : ℝ) (a : ι→ℝ) (bs : List Bool)
    (P Q : List (Letter (ι→ℝ))) :
    expandWord j a bs (liftWord P++(.inverse::liftWord Q))=P++chain j a bs++Q := by
  simp only [expandWord,List.flatMap_append,List.flatMap_cons]
  change expandWord j a bs (liftWord P)++(chain j a bs++expandWord j a bs (liftWord Q))=_
  simp [List.append_assoc]

def literalSeries [Fintype ι] (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ⟦X⟧ :=
  if inverseCount F=0 then PowerSeries.C (ordinary j (expandWord j a [] F) i)
  else PowerSeries.mk (fun n=>∑ bs : Blocks n, ordinary j (expandWord j a bs.val F) i)
@[simp] lemma literalSeries_lift [Fintype ι] (j : ℝ) (a : ι→ℝ) (F : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord F) i=PowerSeries.C (ordinary j F i) := by
  simp [literalSeries]
@[simp] lemma literalSeries_oneInverse [Fintype ι] (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++(.inverse::liftWord Q)) i=inverseSeries j a P Q i := by
  have hc : inverseCount (liftWord P++(.inverse::liftWord Q))=1 := by simp only [inverseCount_append,inverseCount_inverse,inverseCount_lift,zero_add]
  simp [literalSeries,hc,inverseSeries,inverseCoefficient]

instance noiseSplitDiagIsEmpty {D : Type*} (d : D) : IsEmpty (NoiseSplit [Letter.diag d]) :=
  ⟨fun s => by
    have hle := s.length_bound
    have hp : s.before=[] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    have hh := s.word_eq
    simp [hp] at hh⟩
instance noiseSplitNoiseUnique {D : Type*} : Unique (NoiseSplit [Letter.noise (D := D)]) where
  default := ⟨[],[],rfl⟩
  uniq s := by
    have hle := s.length_bound
    have hp : s.before=[] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    have hq : s.after=[] := by have hh := s.word_eq; simpa [hp] using hh.symm
    apply NoiseSplit.ext <;> assumption

lemma sum_noiseSplit_cons_diag {D M : Type*} [AddCommMonoid M] (d : D) (F : List (Letter D))
    (f : List (Letter D)→List (Letter D)→M) :
    (∑ s : NoiseSplit (.diag d::F), f s.before s.after)=
      ∑ s : NoiseSplit F, f (.diag d::s.before) s.after := by
  have hh := NoiseSplit.sum_append [Letter.diag d] F f
  simpa using hh
lemma sum_noiseSplit_cons_noise {D M : Type*} [AddCommMonoid M] (F : List (Letter D))
    (f : List (Letter D)→List (Letter D)→M) :
    (∑ s : NoiseSplit (.noise::F), f s.before s.after)=
      f [] F+∑ s : NoiseSplit F, f (.noise::s.before) s.after := by
  have hh := NoiseSplit.sum_append [Letter.noise] F f
  have he : (default : NoiseSplit [Letter.noise (D := D)])=⟨[],[],rfl⟩ := Subsingleton.elim _ _
  simpa only [Fintype.sum_unique,he,List.nil_append,List.singleton_append] using hh

lemma sum_wordPartners_lift {M : Type*} [AddCommMonoid M] (a : ι→ℝ)
    (F : List (Letter (ι→ℝ))) (f : WordCut ι→M) :
    ((wordPartners a (liftWord F)).map f).sum=
      ∑ s : NoiseSplit F, f ⟨liftWord s.before,liftWord s.after,false⟩ := by
  induction F generalizing f with
  | nil => simp [wordPartners]
  | cons l F ih =>
    cases l with
    | diag d =>
      simp only [liftWord_cons,Letter.toWord,wordPartners,List.nil_append,List.map_map]
      rw [ih,sum_noiseSplit_cons_diag d F (fun U V=>f ⟨liftWord U,liftWord V,false⟩)]
      rfl
    | noise =>
      simp only [liftWord_cons,Letter.toWord,wordPartners,List.singleton_append,List.map_cons,
        List.sum_cons,List.map_map]
      rw [ih,sum_noiseSplit_cons_noise F (fun U V=>f ⟨liftWord U,liftWord V,false⟩)]
      rfl

lemma sum_wordPartners_append {M : Type*} [AddCommMonoid M] (a : ι→ℝ)
    (P Q : List (WordLetter ι)) (f : WordCut ι→M) :
    ((wordPartners a (P++Q)).map f).sum=
      ((wordPartners a P).map (fun c=>f ⟨c.left,c.right++Q,c.inversePartner⟩)).sum+
      ((wordPartners a Q).map (fun c=>f ⟨P++c.left,c.right,c.inversePartner⟩)).sum := by
  induction P generalizing f with
  | nil => simp [wordPartners]
  | cons l P ih =>
    cases l <;>
      simp only [List.cons_append,wordPartners,List.nil_append,
        List.map_cons,List.sum_cons,List.map_map,Function.comp_def,WordCut.prepend] <;>
      rw [ih] <;> simp only [add_assoc]

lemma sum_wordPartners_oneInverse {M : Type*} [AddCommMonoid M] (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (f : WordCut ι→M) :
    ((wordPartners a (liftWord P++(.inverse::liftWord Q))).map f).sum=
      (∑ s : NoiseSplit P, f ⟨liftWord s.before,liftWord s.after++(.inverse::liftWord Q),false⟩)+
      f ⟨liftWord P++[.inverse,.diag a],[.inverse]++liftWord Q,true⟩+
      (∑ s : NoiseSplit Q, f ⟨liftWord P++(.inverse::liftWord s.before),liftWord s.after,false⟩) := by
  rw [sum_wordPartners_append,sum_wordPartners_lift]
  simp only [wordPartners,List.singleton_append,List.map_cons,List.sum_cons,List.map_map,
    Function.comp_def,WordCut.prepend]
  rw [sum_wordPartners_lift]
  simp [add_assoc]

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

end OAI
