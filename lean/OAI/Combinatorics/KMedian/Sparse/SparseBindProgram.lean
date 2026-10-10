import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseBind
import OAI.Combinatorics.KMedian.Binary.BinaryAutomatic
import OAI.Combinatorics.KMedian.Geometry.ListSigma
import OAI.Combinatorics.KMedian.Sparse.SparseListTrim

namespace OAI


                                         
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly Finset

variable {α β A : Type}

def weights (x : LawData) : List ℚ := x.2.map (fun z : ℤ => (z:ℚ)/(x.1:ℚ))
def jointWeights (x : LawData × List (Data A)) : List ℚ :=
  ((weights x.1).zip x.2).flatMap (fun z => (weights z.2.1).map (fun q => z.1*q))
def bindData (x : LawData × List (Data A)) : Data A :=
  ((IntegerList.denominator (jointWeights x),IntegerList.numerators (jointWeights x)),
    x.2.flatMap Prod.snd)

 theorem weights_law {n : ℕ} (μ : IntegerLaw (Fin n)) :
    weights (μ.denominator,List.ofFn μ.numerator)=List.ofFn μ.rational.weight := by
  simp only [weights,List.map_ofFn,Function.comp_def,IntegerLaw.rational]

 theorem jointWeights_raw (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (view : β → A) :
    jointWeights ((raw μ).1,List.ofFn (fun i => ((raw (κ i)).1,(κ i).states.toList.map view)))=
      List.ofFn (fun j => let z := (finSigmaFinEquiv (n:=fun i => (κ i).length)).symm j;
        μ.law.rational.weight z.1*(κ z.1).law.rational.weight z.2) := by
  simp only [jointWeights,raw,weights_law,Gaussian.ListOperation.zip_ofFn,List.flatMap_def,
    List.map_ofFn,Function.comp_def,weights_law]
  exact ListSigma.ofFn_sigma _

 theorem scaling_denominator_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : ι → ℚ) :
    RationalScaling.denominator (fun j => w (e.symm j))=RationalScaling.denominator w := by
  unfold RationalScaling.denominator
  exact e.symm.prod_comp (fun i => ((w i).den:ℤ))

 theorem scaling_numerator_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (w : ι → ℚ) (j : κ) :
    RationalScaling.numerator (fun j => w (e.symm j)) j=RationalScaling.numerator w (e.symm j) := by
  apply Int.cast_injective (α:=ℚ)
  rw [RationalScaling.numerator_cast,RationalScaling.numerator_cast,scaling_denominator_equiv]

 theorem bindData_raw (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (view : β → A) :
    bindData ((raw μ).1,List.ofFn (fun i => ((raw (κ i)).1,(κ i).states.toList.map view)))=
      ((raw (μ.bindIndexed κ)).1,(μ.bindIndexed κ).states.toList.map view) := by
  unfold bindData
  rw [jointWeights_raw,IntegerList.denominator_ofFn,IntegerList.numerators_ofFn]
  let w := (μ.law.rational.sigma (fun i => (κ i).law.rational)).weight
  change ((RationalScaling.denominator (fun j => w (finSigmaFinEquiv.symm j)),
    List.ofFn (RationalScaling.numerator (fun j => w (finSigmaFinEquiv.symm j)))),_) = _
  rw [scaling_denominator_equiv finSigmaFinEquiv w]
  rw [show RationalScaling.numerator (fun j => w (finSigmaFinEquiv.symm j)) =
    (fun j => RationalScaling.numerator w (finSigmaFinEquiv.symm j)) from
      funext (scaling_numerator_equiv finSigmaFinEquiv w)]
  have hs : (List.ofFn fun i => ((raw (κ i)).1,(κ i).states.toList.map view)).flatMap Prod.snd=
      (μ.bindIndexed κ).states.toList.map view := by
    simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,states_list,List.map_ofFn]
    rw [ListSigma.ofFn_sigma]
    simp only [bindIndexed,Vector.getElem_ofFn]
  rw [hs]
  rfl

@[fun_prop] theorem weights_poly : Poly weights := by
  unfold weights
  apply list_map <;> fun_prop

@[fun_prop] theorem jointWeights_poly [Coding A] [Inhabited A] : Poly (jointWeights (A:=A)) := by
  unfold jointWeights
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop

@[fun_prop] theorem bindData_poly [Coding A] [Inhabited A] : Poly (bindData (A:=A)) := by
  have hd : Poly IntegerList.denominator := ⟨IntegerList.denominatorProgram⟩
  have hn : Poly IntegerList.numerators := ⟨IntegerList.numeratorsProgram⟩
  have hs : Poly (fun x : LawData × List (Data A) => x.2.flatMap Prod.snd) := by
    apply list_flatMap <;> fun_prop
  exact pair (pair (comp hd jointWeights_poly) (comp hn jointWeights_poly)) hs

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
