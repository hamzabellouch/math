import OAI.Computability.RationalHitting.MatrixComputation

namespace OAI

namespace RationalHitting.StackLanguage

lemma range_flatMap_to_finRange {A : Type} (n : ℕ) (f : ℕ → List A) :
    (List.range n).flatMap f=(List.finRange n).flatMap (fun i => f i.val) := by
  rw [←finRange_map_val,List.flatMap_map]

namespace Poly
variable {A B : Type} [Coding A] [Coding B]

theorem tabulateUp {n : A → ℕ} {f : A×Unary → B}
    (hn : Poly (fun a => Unary.mk (n a))) (hf : Poly f) :
    Poly (fun a => (List.range (n a)).map (fun i => f (a,⟨i⟩))) :=
  hf.tabulate.comp (hn.pair (show Poly (fun a : A => a) from id))

theorem flatMapUp {n : A → ℕ} {f : A×Unary → List B}
    (hn : Poly (fun a => Unary.mk (n a))) (hf : Poly f) :
    Poly (fun a => (List.range (n a)).flatMap (fun i => f (a,⟨i⟩))) :=
  (listFlatten.comp (tabulateUp hn hf)).of_eq (by intro a;rw [List.flatMap_def])

theorem wordRange {n : A → ℕ} {f : A×Unary → BitWord}
    (hn : Poly (fun a => Unary.mk (n a))) (hf : Poly f) :
    Poly (fun a => BitWord.mk ((List.range (n a)).flatMap (fun i => (f (a,⟨i⟩)).val))) :=
  (wordConcat.comp (tabulateUp hn hf)).of_eq (by intro a;simp [List.flatMap_map])
end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
namespace Runtime

abbrev MatrixWordArgs := (DenseSquare×DenseSquare)×ℤ

def matrixWord (A B : DenseSquare) (den : ℤ) : BitWord :=
  ⟨(List.range A.dim).flatMap fun i =>
    (List.range A.dim).flatMap fun j =>
      encodeRat (Rat.divInt (cramer A B i j).val.det den)⟩

@[fun_prop] theorem matrixWord_poly : Poly (fun a : MatrixWordArgs => matrixWord a.1.1 a.1.2 a.2) := by
  have hc : Poly (fun a : (MatrixWordArgs×Unary)×Unary =>
      cramer a.1.1.1.1 a.1.1.1.2 a.1.2.val a.2.val) :=
    cramer_poly.comp (show Poly (fun a : (MatrixWordArgs×Unary)×Unary =>
      (a.1.1.1,(a.1.2,a.2))) by fun_prop)
  have hv := Poly.rationalEncode.comp ((Poly.denseDet.comp hc).pair
    (show Poly (fun a : (MatrixWordArgs×Unary)×Unary => a.1.1.2) by fun_prop))
  have hr := Poly.wordRange (Poly.denseDim.comp (show Poly (fun a : MatrixWordArgs×Unary => a.1.1.1) by fun_prop)) hv
  exact Poly.wordRange (Poly.denseDim.comp (show Poly (fun a : MatrixWordArgs => a.1.1) by fun_prop)) hr

lemma matrixWord_of {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (den : ℤ) :
    (matrixWord (DenseSquare.of A) (DenseSquare.of B) den).val=
      (List.finRange d).flatMap (fun i => (List.finRange d).flatMap (fun j =>
        encodeRat (Rat.divInt (A.updateCol i (fun r => B r j)).det den))) := by
  unfold matrixWord
  change (List.range d).flatMap _ = _
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro i hi
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro j hj
  change Fin d at j
  exact cramer_encode_of A B den i j

abbrev TupleWordArgs := (Params×GridPoint)×DenseSquare×ℤ

def tupleWord (p : Params) (x : GridPoint) (A : DenseSquare) (den : ℤ) : BitWord :=
  ⟨(List.range p.n).flatMap fun i => (matrixWord A (matrix p x ⟨i+1⟩) den).val⟩

@[fun_prop] theorem tupleWord_poly : Poly (fun a : TupleWordArgs => tupleWord a.1.1 a.1.2 a.2.1 a.2.2) := by
  have hm : Poly (fun a : TupleWordArgs×Unary => matrix a.1.1.1 a.1.1.2 (a.2+1)) := by fun_prop
  have hv := matrixWord_poly.comp
    (((show Poly (fun a : TupleWordArgs×Unary => a.1.2.1) by fun_prop).pair hm).pair
      (show Poly (fun a : TupleWordArgs×Unary => a.1.2.2) by fun_prop))
  exact Poly.wordRange (show Poly (fun a : TupleWordArgs => a.1.1.1) by fun_prop) hv

lemma tupleWord_eq (n s : ℕ) (x : GridPoint) (den : ℤ) :
    (tupleWord (Params.of n s) x
      (matrix (Params.of n s) x 0) den).val =
      encodeTuple (ExecutableGenerator.tuple (ExecutableGenerator.normalized
        (ExecutableGenerator.inputTables n (Parameters.N n s) (Parameters.exponent n s) (gridFn x)) den)) := by
  unfold tupleWord encodeTuple
  change (List.range n).flatMap _ = _
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro a ha
  let U := Generator.U n (Parameters.N n s) (Parameters.exponent n s) (gridFn x)
  have hzero : matrix (Params.of n s) x 0=DenseSquare.of (U 0) := matrix_eq n s x 0
  have hsucc : matrix (Params.of n s) x ⟨a.val+1⟩=DenseSquare.of (U a.succ) := matrix_eq n s x a.succ
  trans (matrixWord (DenseSquare.of (U 0)) (DenseSquare.of (U a.succ)) den).val
  · exact congrArg₂ (fun A B => (matrixWord A B den).val) hzero hsucc
  rw [matrixWord_of]
  apply List.flatMap_congr
  intro i hi
  apply List.flatMap_congr
  intro j hj
  congr 1
  rw [ExecutableGenerator.tuple_normalized,ExecutableGenerator.normalizedEntry,
    DeterminantAlgorithm.determinant_eq,DeterminantAlgorithm.denote_tabulate,
    ExecutableGenerator.inputTables_denote,ExecutableGenerator.inputTables_denote]

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
namespace Runtime

def point (p : Params) (x : GridPoint) : List BitWord :=
  let A := matrix p x 0
  let den := A.val.det
  if den=0 then [] else [tupleWord p x A den]

@[fun_prop] theorem point_poly : Poly (fun a : Params×GridPoint => point a.1 a.2) := by
  have hf : Poly (fun a : TupleWordArgs =>
    if a.2.2=0 then ([] : List BitWord) else [tupleWord a.1.1 a.1.2 a.2.1 a.2.2]) := by
    apply Poly.ite
    · exact Poly.intZero.comp (show Poly (fun a : TupleWordArgs => a.2.2) by fun_prop)
    · exact Poly.const []
    · exact Poly.listSingleton.comp tupleWord_poly
  have hm : Poly (fun a : Params×GridPoint => matrix a.1 a.2 0) := by fun_prop
  exact hf.comp ((show Poly (fun a : Params×GridPoint => a) from Poly.id).pair
    (hm.pair (Poly.denseDet.comp hm)))

lemma matrix_det_eq (n s : ℕ) (x : GridPoint) (a : Fin (n+1)) :
    (matrix (Params.of n s) x ⟨a.val⟩).val.det=
      (Generator.U n (Parameters.N n s) (Parameters.exponent n s) (gridFn x) a).det := by
  apply congrArg Matrix.det
  funext i j
  exact entry_eq n _ _ (gridFn x) a i j

lemma point_eq (n s : ℕ) (x : GridPoint) :
    point (Params.of n s) x=
      ((ExecutableGenerator.atPoint n (Parameters.N n s) (Parameters.exponent n s) (gridFn x)).toList.map
        (fun X => BitWord.mk (encodeTuple X))) := by
  unfold point ExecutableGenerator.atPoint
  simp only [DeterminantAlgorithm.determinant_eq,ExecutableGenerator.inputTables_denote]
  have hd : (matrix (Params.of n s) x 0).val.det=
      (Generator.U n (Parameters.N n s) (Parameters.exponent n s) (gridFn x) 0).det :=
    matrix_det_eq n s x 0
  rw [hd]
  split_ifs with hz
  · rfl
  · simp only [Option.toList_some,List.map_cons,List.map_nil,List.cons.injEq, and_true]
    apply congrArg BitWord.mk
    exact tupleWord_eq n s x _

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

lemma map_filterMap_toList {A B C : Type} (l : List A) (f : A → Option B) (g : B → C) :
    (l.filterMap f).map g=l.flatMap (fun a => (f a).toList.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : f a <;> simp [h,ih]

namespace Runtime

def words (p : Params) : List BitWord :=
  (List.range p.H).flatMap fun t => (List.range p.H).flatMap fun q =>
    (List.range p.H).flatMap fun r => point p (⟨t+1⟩,⟨q+1⟩,⟨r+1⟩)

@[fun_prop] theorem words_poly : Poly words := by
  have hp : Poly (fun a : ((Params×Unary)×Unary)×Unary =>
      point a.1.1.1 (a.1.1.2+1,a.1.2+1,a.2+1)) := by fun_prop
  have h1 := Poly.flatMapUp (show Poly (fun a : (Params×Unary)×Unary => a.1.1.2.2.2.2) by fun_prop) hp
  have h2 := Poly.flatMapUp (show Poly (fun a : Params×Unary => a.1.2.2.2.2) by fun_prop) h1
  exact Poly.flatMapUp (show Poly (fun a : Params => a.2.2.2.2) by fun_prop) h2

lemma gridFn_fin {H : ℕ} (t p r : Fin H) :
    gridFn (⟨t.val+1⟩,⟨p.val+1⟩,⟨r.val+1⟩)=fun i => (![t,p,r] i).val+1 := by
  funext i;fin_cases i <;> rfl

lemma words_eq (n s : ℕ) : words (Params.of n s)=
    (ExecutableGenerator.list n s).tuples.map (fun X => BitWord.mk (encodeTuple X)) := by
  unfold words
  rw [show (Params.of n s).H=Parameters.H n s from rfl]
  simp only [ExecutableGenerator.list,ExecutableGenerator.output]
  rw [map_filterMap_toList]
  simp only [Generator.grid,List.flatMap_assoc,List.flatMap_map]
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro t ht
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro p hp
  rw [range_flatMap_to_finRange]
  apply List.flatMap_congr
  intro r hr
  rw [point_eq,gridFn_fin]

end Runtime
end RationalHitting.StackLanguage

end OAI
