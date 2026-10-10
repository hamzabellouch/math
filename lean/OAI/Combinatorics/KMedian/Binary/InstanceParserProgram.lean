import Mathlib
import OAI.Combinatorics.KMedian.Programs.InstanceDataProgram
import OAI.Combinatorics.KMedian.Binary.NumericParserProgram
import OAI.Combinatorics.KMedian.Binary.SequentialParserProgram

namespace OAI


                                             
section
namespace MetricKMedian.InputParser
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
@[fun_prop] theorem take_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).take (f x)) :=
  comp list_take (pair hg hf)
@[fun_prop] theorem drop_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).drop (f x)) :=
  comp list_drop (pair hg hf)
def squareUnits (xs : Row) : List Unit := xs.flatMap (fun _ => xs.map (fun _ => ()))
@[fun_prop] theorem squareUnits_poly : Poly squareUnits := by unfold squareUnits; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
 theorem squareUnits_length (xs : Row) : (squareUnits xs).length=xs.length*xs.length := by
  simp only [squareUnits,List.length_flatMap,List.length_map]
  rw [List.map_const',List.sum_replicate]
  simp only [smul_eq_mul]
def reshape (x : Row × List ℚ) : InstanceProgram.Matrix :=
  (indices x.1).map (fun i => (indices x.1).map (fun j => x.2[i*x.1.length+j]?.getD 0))
@[fun_prop] theorem reshape_poly : Poly reshape := by unfold reshape; apply list_map; apply list_map <;> fun_prop; fun_prop
 theorem flatten_ofFn {n : ℕ} (d : Fin n → Fin n → ℚ) :
    (List.ofFn (fun i => List.ofFn (d i))).flatten=
      List.ofFn (fun k : Fin (n*n) => d (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  symm
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij : i.val*n+j.val<n*n := by
    calc
      i.val*n+j.val < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by simp only [Nat.add_mul,Nat.one_mul]
      _ ≤ n*n := Nat.mul_le_mul_right n i.isLt
  have he : (⟨i.val*n+j.val, hij⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext; change _=j.val+n*i.val; ac_rfl
  rw [he]
  exact congrArg (fun p : Fin n × Fin n => d p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
 theorem reshape_flatten {n : ℕ} (S : Finset (Fin n)) (d : Fin n → Fin n → ℚ) :
    reshape (setView S,(List.ofFn (fun i => List.ofFn (d i))).flatten)=List.ofFn (fun i => List.ofFn (d i)) := by
  rw [flatten_ofFn]
  simp only [reshape,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij : i.val*n+j.val<n*n := by
    calc
      i.val*n+j.val < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by simp only [Nat.add_mul,Nat.one_mul]
      _ ≤ n*n := Nat.mul_le_mul_right n i.isLt
  simp only [List.getElem?_ofFn,dite_eq_left hij,Option.getD_some]
  have he : (⟨i.val*n+j.val, hij⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext; change _=j.val+n*i.val; ac_rfl
  rw [he]
  exact congrArg (fun p : Fin n × Fin n => d p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
def matrix (x : Row × List Bool) : InstanceProgram.Matrix :=
  reshape (x.1,(parse ratRead (squareUnits x.1,x.2)).1)
noncomputable def matrixProgram : PolyProgram enc enc matrix := by
  have hp : Poly (parse ratRead) := ⟨parseProgram ratRead ratRead_poly.program ratRead_rest_length⟩
  have h : Poly matrix := by unfold matrix; fun_prop
  exact h.program
 theorem matrix_encoded {n : ℕ} (S : Finset (Fin n)) (d : Fin n → Fin n → ℚ) (xs : List Bool) :
    matrix (setView S,((List.ofFn (fun i => List.ofFn (d i))).flatten.map encodeRat).flatten++xs)=
      List.ofFn (fun i => List.ofFn (d i)) := by
  unfold matrix
  have hu : squareUnits (setView S)=List.replicate (List.ofFn (fun i => List.ofFn (d i))).flatten.length () := by
    apply List.eq_replicate_iff.mpr
    refine ⟨?_,fun _ _ => rfl⟩
    rw [squareUnits_length,flatten_ofFn]
    simp only [setView,List.length_ofFn]
  rw [hu,parse_encoded ratRead encodeRat ratRead_append]
  exact reshape_flatten S d
abbrev Header := (Row × Row) × ℕ
def header (xs : List Bool) : Header × List Bool :=
  let a := natRead xs
  let b := natRead a.2
  (((b.2.take a.1,(b.2.drop a.1).take a.1),b.1),b.2.drop (a.1+a.1))
@[fun_prop] theorem header_poly : Poly header := by unfold header; fun_prop
 theorem header_encoded (I : Instance) : header (encodeInstance I)=
    (((setView I.clients,setView I.facilities),I.k),
      (List.ofFn (fun i => (List.ofFn (fun j => encodeRat (I.distance i j))).flatten)).flatten) := by
  unfold header encodeInstance
  simp only [List.append_assoc,natRead_append]
  have hc : (setView I.clients).length=I.n := by simp only [setView,List.length_ofFn]
  have hf : (setView I.facilities).length=I.n := by simp only [setView,List.length_ofFn]
  change (((((setView I.clients)++(setView I.facilities++_)).take I.n,
    (((setView I.clients)++(setView I.facilities++_)).drop I.n).take I.n),I.k),
    ((setView I.clients)++(setView I.facilities++_)).drop (I.n+I.n))=_
  have htC (xs : Row) : (setView I.clients++xs).take I.n=setView I.clients := by simpa only [hc] using List.take_left (l₁ := setView I.clients) (l₂ := xs)
  have hdC (xs : Row) : (setView I.clients++xs).drop I.n=xs := by simpa only [hc] using List.drop_left (l₁ := setView I.clients) (l₂ := xs)
  have htF (xs : Row) : (setView I.facilities++xs).take I.n=setView I.facilities := by simpa only [hf] using List.take_left (l₁ := setView I.facilities) (l₂ := xs)
  have hdF (xs : Row) : (setView I.facilities++xs).drop I.n=xs := by simpa only [hf] using List.drop_left (l₁ := setView I.facilities) (l₂ := xs)
  simp only [htC,hdC,htF,← List.drop_drop,hdF]

def raw (xs : List Bool) : Raw :=
  let h := header xs
  (h.1.1,(h.1.2,matrix (h.1.1.1,h.2)))
noncomputable def rawProgram : PolyProgram enc enc raw := by
  have hm : Poly matrix := ⟨matrixProgram⟩
  exact (by unfold raw; fun_prop : Poly raw).program
 theorem raw_encoded (I : Instance) : raw (encodeInstance I)=view I := by
  unfold raw
  rw [header_encoded]
  have he : (List.ofFn (fun i => (List.ofFn (fun j => encodeRat (I.distance i j))).flatten)).flatten=
      ((List.ofFn (fun i => List.ofFn (I.distance i))).flatten.map encodeRat).flatten := by
    simp only [List.map_flatten,List.map_ofFn,Function.comp_def]
    rw [List.flatten_flatten]
    simp only [List.map_ofFn,Function.comp_def]
  rw [he]
  dsimp only
  have hm := matrix_encoded I.clients I.distance []
  simp only [List.append_nil] at hm
  rw [hm]
  rfl
noncomputable def instanceProgram : PolyProgram encodeInstance InstanceProgram.encode (id : Instance → Instance) :=
  (BooleanLists.packProgram.comp rawProgram).recode encodeInstance (fun _ => rfl) (fun I => congrArg enc (raw_encoded I))
end MetricKMedian.InputParser
end

end OAI
