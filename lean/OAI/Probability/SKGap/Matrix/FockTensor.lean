import Mathlib
import OAI.Probability.SKGap.Localization.GraphPrediction

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor
open Diagram
variable {ι : Type*} [Fintype ι]
abbrev Space := ι→List ι→ℝ

def tensorValue : List (ι→ℝ)→List ι→ℝ
  | [],[] => 1
  | a::A,i::I => a i*tensorValue A I
  | _,_ => 0

def realize : Primary.Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s i I =>s.1 i*tensorValue s.2 I)
omit [Fintype ι] in
lemma realize_ket (s : Stack (ι:=ι)) (i : ι) (I : List ι) :
    realize (ket s) i I=s.1 i*tensorValue s.2 I := by simp [realize,ket]

def diagonal (a : ι→ℝ) : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) where
  toFun v i I := a i*v i I
  map_add' v w := by ext i I; simp [mul_add]
  map_smul' c v := by ext i I; simp [mul_left_comm]
def creation : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) where
  toFun v i I := match I with | [] => 0 | q::Q => v q Q
  map_add' v w := by ext i I; cases I <;> simp
  map_smul' c v := by ext i I; cases I <;> simp
def annihilation : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) where
  toFun v i I := Diagram.mean (fun q =>v q (i::I))
  map_add' v w := by ext i I; simp [Diagram.mean,Finset.sum_add_distrib,add_div]
  map_smul' c v := by ext i I; simp [Diagram.mean,←Finset.mul_sum,mul_div_assoc]
def noise (j : ℝ) : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) := creation+j • annihilation
def project : Space (ι:=ι)→ₗ[ℝ] (ι→ℝ) where
  toFun v i := v i []
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vacuum : Space (ι:=ι) := realize Primary.vacuum

def letter (j : ℝ) : Letter (ι→ℝ)→Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)
  | .diag a => diagonal a
  | .noise => noise j
def word (j : ℝ) : List (Letter (ι→ℝ))→Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)
  | [] => LinearMap.id
  | a::F => (letter j a).comp (word j F)

omit [Fintype ι] in
lemma realize_diagonal (a : ι→ℝ) (v : Primary.Space (ι:=ι)) :
    realize (Primary.diagonal a v)=diagonal a (realize v) := by
  have h : realize.comp (Primary.diagonal a)=(diagonal a).comp realize := by
    apply Finsupp.lhom_ext'
    intro s
    ext i I
    change realize (Primary.diagonal a (ket s)) i I = diagonal a (realize (ket s)) i I
    rw [Primary.diagonal_ket,realize_ket]
    change (a i*s.1 i)*tensorValue s.2 I=a i*realize (ket s) i I
    rw [realize_ket]; ring
  exact LinearMap.congr_fun h v
omit [Fintype ι] in
lemma realize_creation (v : Primary.Space (ι:=ι)) :
    realize (Primary.creation v)=creation (realize v) := by
  have h : (realize (ι:=ι)).comp Primary.creation=creation.comp realize := by
    apply Finsupp.lhom_ext'
    intro s
    ext i I
    change realize (Primary.creation (ket s)) i I = creation (realize (ket s)) i I
    rw [Primary.creation_ket,realize_ket]
    cases I <;> simp [creation,tensorValue,realize_ket]
  exact LinearMap.congr_fun h v
lemma realize_annihilation (v : Primary.Space (ι:=ι)) :
    realize (Primary.annihilation v)=annihilation (realize v) := by
  have h : (realize (ι:=ι)).comp Primary.annihilation=annihilation.comp realize := by
    apply Finsupp.lhom_ext'
    rintro ⟨a,L⟩
    ext i I
    change realize (Primary.annihilation (ket (a,L))) i I = annihilation (realize (ket (a,L))) i I
    cases L <;> simp [annihilation,realize_ket,tensorValue,Diagram.mean,←Finset.sum_mul,div_mul_eq_mul_div]
  exact LinearMap.congr_fun h v
lemma realize_noise (j : ℝ) (v : Primary.Space (ι:=ι)) :
    realize (Primary.noise j v)=noise j (realize v) := by
  simp [Primary.noise,noise,realize_annihilation,realize_creation]
omit [Fintype ι] in
lemma project_realize (v : Primary.Space (ι:=ι)) : project (realize v)=Primary.project v := by
  have h : (project (ι:=ι)).comp realize=Primary.project := by
    apply Finsupp.lhom_ext'
    rintro ⟨a,L⟩
    ext i
    change project (realize (ket (a,L))) i = Primary.project (ket (a,L)) i
    cases L <;> simp [project,realize_ket,tensorValue]
  exact LinearMap.congr_fun h v
lemma realize_word (j : ℝ) (F : List (Letter (ι→ℝ))) (v : Primary.Space (ι:=ι)) :
    realize (Primary.word j F v)=word j F (realize v) := by
  induction F generalizing v with
  | nil => rfl
  | cons a F ih =>
    cases a <;> simp [Primary.word,Primary.letter,word,letter,realize_noise,realize_diagonal,ih]
omit [Fintype ι] in
lemma diagram_map_id (d : Diagram (ι→ℝ)) : d.map id=d := by
  induction d <;> simp_all [Diagram.map]
lemma project_word (j : ℝ) (F : List (Letter (ι→ℝ))) (i : ι) :
    project (word j F vacuum) i=WordSeries.ordinary j F i := by
  rw [vacuum,←realize_word,project_realize,Primary.project_word]
  simp [WordSeries.ordinary,Diagram.expect,Diagram.evaluate,Diagram.prediction,diagram_map_id]
lemma word_append (j : ℝ) (F G : List (Letter (ι→ℝ))) :
    word j (F++G)=(word j F).comp (word j G) := by
  induction F with
  | nil => simp [word]
  | cons a F ih => simp [word,ih,LinearMap.comp_assoc]
omit [Fintype ι] in
lemma diagonal_scale (c : ℝ) (a : ι→ℝ) : diagonal (fun i=>c*a i)=c • diagonal a := by
  ext v i I
  change (c*a i)*v i I=c*(a i*v i I)
  ring
lemma annihilation_diagonal_creation (a : ι→ℝ) (v : Space (ι:=ι)) :
    annihilation (diagonal a (creation v))=Diagram.mean a • v := by
  ext i I
  simp [annihilation,diagonal,creation,Diagram.mean,←Finset.sum_mul,mul_div_right_comm]
omit [Fintype ι] in
lemma project_diagonal_creation (a : ι→ℝ) (v : Space (ι:=ι)) :
    project (diagonal a (creation v))=0 := by ext i; simp [project,diagonal,creation]
omit [Fintype ι] in
lemma project_creation (v : Space (ι:=ι)) : project (creation v)=0 := rfl
end SKGap.Noncrossing.Primary.Tensor

end
end

end OAI
