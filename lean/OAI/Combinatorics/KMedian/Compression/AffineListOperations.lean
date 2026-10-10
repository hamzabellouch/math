import Mathlib
import OAI.Combinatorics.KMedian.Compression.ComputedAffineKernel
import OAI.Combinatorics.KMedian.Geometry.SortedListEncoding
import OAI.Combinatorics.KMedian.Compression.IntegerKernelProgram

namespace OAI


                                            
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Gaussian
open Finset
abbrev Row := Binary.IntegerList.Row
abbrev Rows := Binary.IntegerList.Rows
abbrev er := Binary.IntegerList.er
abbrev em := Binary.IntegerList.em
abbrev es := Gaussian.ListOperation.eslots
abbrev Data := List Unit × (Row × Rows)
abbrev ed := encodePair es (encodePair er em)
abbrev Entry := ℕ × (ℤ × Row)
abbrev ee := encodePair Nat.bits (encodePair Signed.encode er)
abbrev ees := encodeList ee

def entries (x : Data) : List Entry :=
  let zs := x.2.1.zip x.2.2
  (List.range zs.length).zip zs

def active (x : Data) : List Entry := (entries x).filter (fun e => decide (e.2.1≠0))
def activeRows (x : Data) : Gaussian.IntegerProgram.Rows :=
  (active x).map (fun _ => 1) :: (List.range x.1.length).map (fun j => (active x).map (fun e => e.2.2[j]?.getD 0))
def activeData (x : Data) : List Unit × Rows :=
  ((active x).map (fun _ => ()),activeRows x)

def extend (zs : List (ℕ × ℤ)) (i : ℕ) : ℤ :=
  ((zs.filter (fun e => decide (e.1=i))).map Prod.snd).sum

def full (x : Data) (z : Row) : Row :=
  let zs := ((active x).map Prod.fst).zip z
  (List.range x.2.1.length).map (extend zs)

structure Input where
  n : ℕ
  d : ℕ
  μ : IntegerLaw (Fin n)
  v : Fin n → Fin d → ℤ
  large : d+1 < μ.support.card

def Input.raw (I : Input) : Data :=
  (List.replicate I.d (),(List.ofFn I.μ.numerator,List.ofFn (fun i => List.ofFn (I.v i))))
abbrev Input.encode (I : Input) := ed I.raw

def Input.kernel (I : Input) : Gaussian.IntegerProgram.Input :=
  ⟨I.d+1,I.μ.support.card,activeMatrix I.μ I.v,I.large⟩

theorem indices_ofFn (n : ℕ) : List.range n=List.ofFn (fun i : Fin n => i.val) := by
  apply List.ext_getElem
  · simp
  · intros; simp

theorem range_ofFn {n : ℕ} {α : Type} (f : Fin n → α) :
    (List.range n).zip (List.ofFn f)=List.ofFn (fun i => (i.val,f i)) := by
  rw [indices_ofFn,Gaussian.ListOperation.zip_ofFn]

theorem entries_raw (I : Input) : entries I.raw=List.ofFn (fun i : Fin I.n =>
    (i.val,(I.μ.numerator i,List.ofFn (I.v i)))) := by
  simp only [entries,Input.raw,Gaussian.ListOperation.zip_ofFn,List.length_ofFn,range_ofFn]

theorem active_raw (I : Input) : active I.raw=List.ofFn (fun j : Fin I.μ.support.card =>
    let i := ((I.μ.support.orderIsoOfFin rfl) j).val
    (i.val,(I.μ.numerator i,List.ofFn (I.v i)))) := by
  rw [active,entries_raw,List.ofFn_eq_map,List.filter_map]
  exact EncodingLists.map_filter_enum _ (fun i => I.μ.numerator i≠0)

theorem activeRows_raw (I : Input) : activeRows I.raw=
    List.ofFn (fun j => List.ofFn (activeMatrix I.μ I.v j)) := by
  rw [activeRows,active_raw]
  simp only [Input.raw,List.length_replicate,List.map_ofFn,Function.comp_def]
  rw [indices_ofFn,List.map_ofFn,List.ofFn_succ]
  congr 1
  congr 1
  funext j
  simp only [Function.comp_apply,Gaussian.ListOperation.get_ofFn]
  rfl

theorem activeData_raw (I : Input) : activeData I.raw=I.kernel.raw := by
  simp only [activeData,activeRows_raw,active_raw,List.map_ofFn,Function.comp_def,List.ofFn_const,
    Input.kernel,Gaussian.IntegerProgram.Input.raw]

theorem extend_ofFn {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ) (i : Fin n) :
    extend (List.ofFn (fun j => (((s.orderIsoOfFin rfl) j).val.val,z j))) i.val=
      Compression.extendVector s z i := by
  unfold extend
  have he : ∀ xs : List (ℕ × ℤ), ((xs.filter (fun e => decide (e.1=i.val))).map Prod.snd).sum=
      (xs.map (fun e => if e.1=i.val then e.2 else 0)).sum := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih => by_cases h : a.1=i.val <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  by_cases hi : i∈s
  · let k : Fin s.card := (s.orderIsoOfFin rfl).symm ⟨i,hi⟩
    have hik : ((s.orderIsoOfFin rfl) k).val=i := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩)
    have hh (j : Fin s.card) : ((s.orderIsoOfFin rfl) j).val.val=i.val ↔ j=k := by
      constructor
      · intro h
        apply (s.orderIsoOfFin rfl).injective
        apply Subtype.ext
        exact (Fin.ext h).trans hik.symm
      · rintro rfl
        exact congrArg Fin.val hik
    simp only [Function.comp_apply,hh,Finset.sum_ite_eq',mem_univ,ite_true,Compression.extendVector,dite_eq_left hi]
    rfl
  · have hh (j : Fin s.card) : ((s.orderIsoOfFin rfl) j).val.val ≠ i.val := by
      intro h
      exact hi ((Fin.val_inj.mp h) ▸ ((s.orderIsoOfFin rfl) j).property)
    simp only [Function.comp_apply,hh,ite_false,sum_const_zero,Compression.extendVector,dite_eq_right hi]

theorem full_raw (I : Input) :
    full I.raw (List.ofFn (Gaussian.computedIntegerKernel (I.d+1) I.μ.support.card (activeMatrix I.μ I.v)))=
      List.ofFn (computedAffineKernel I.μ I.v) := by
  rw [full,active_raw]
  simp only [List.map_ofFn,Function.comp_def,Gaussian.ListOperation.zip_ofFn]
  simp only [Input.raw,List.length_ofFn,indices_ofFn,List.map_ofFn,Function.comp_def,extend_ofFn,
    computedAffineKernel,Vector.getElem_ofFn]

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
