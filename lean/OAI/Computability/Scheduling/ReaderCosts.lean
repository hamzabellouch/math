import OAI.Computability.Scheduling.RequestBounds

namespace OAI

universe u1 u2 u3

section
namespace ThreeMachine.StackCompiler.Costs
open RequestData

def requestSlots (x : Index) : Option (List ℕ) :=
  ThreeMachine.StackCompiler.answerMatrix (closureMatrix x.2.graph x.1) x.2.deadline

theorem requestSlotsLength : Poly size (fun x : Index => ((requestSlots x).getD []).length) 1 :=
  Poly.of_le (fun _x => answerMatrix_length _ _) nPoly

theorem requestSlotsBound : Poly (fun p : Poly.ListPool (fun x : Index => (requestSlots x).getD []) => size p.1)
    (fun p => p.2.1) 1 := by
  apply Poly.of_le (fun p : Poly.ListPool (fun x : Index => (requestSlots x).getD []) =>
    answerMatrix_bound (closureMatrix p.1.2.graph p.1.1) p.1.2.deadline p.2.2)
  have hn := nPoly.precomp (Sigma.fst : Poly.ListPool (fun x : Index => (requestSlots x).getD []) → Index)
  have hd := deadlinePoly.precomp (Sigma.fst : Poly.ListPool (fun x : Index => (requestSlots x).getD []) → Index)
  poly_auto

theorem requestSlotsVolume : Poly size (fun x : Index => volume (requestSlots x)) 2 := by
  have hi : Poly (fun p : Poly.ListPool (fun x : Index => (requestSlots x).getD []) => size p.1)
      (fun p => volume p.2.1) 1 := Poly.volumeNat requestSlotsBound
  have hv := Poly.volumeListOfPool (fun x : Index => (requestSlots x).getD []) requestSlotsLength hi
  apply Poly.of_le (fun x : Index => volume_option_le_getD (requestSlots x) [])
  poly_auto

theorem requestEncodeAnswer : Poly size
    (fun x : Index => (Uniform.binaryEncodeAnswer (I := ℕ)).time x.1 (requestSlots x)) 5 :=
  binaryEncodeAnswer size Sigma.fst requestSlots requestSlotsLength requestSlotsBound

theorem requestOutputLength : Poly size (fun x : Index => (Algorithm.output x.2.graph x.2.deadline).length) 2 := by
  have he := lengthEncodeNatList size (fun x : Index => (requestSlots x).getD []) requestSlotsLength requestSlotsBound
  have hb (x : Index) : (ThreeMachine.encodeAnswer (requestSlots x)).length ≤
      1+(ThreeMachine.encodeList ThreeMachine.encodeNat ((requestSlots x).getD [])).length := by
    cases requestSlots x <;> simp only [ThreeMachine.encodeAnswer,Option.getD_none,Option.getD_some,
      List.length_cons,List.length_nil] <;> omega
  have ho : ∀ x : Index, ThreeMachine.encodeAnswer (requestSlots x) = Algorithm.output x.2.graph x.2.deadline :=
    fun x => answerMatrix_closure x.2.graph x.2.deadline
  apply Poly.of_le (g := fun x : Index => 1+(ThreeMachine.encodeList ThreeMachine.encodeNat ((requestSlots x).getD [])).length) (fun x : Index => by rw [← ho x]; exact hb x)
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type} [∀ i, Coding (α i)]
theorem time_binaryReadStep_le {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (i : I) (bs : List Bool) (acc : List (α i)) :
    R.binaryReadStep.time i (bs,acc) ≤ 1000*(R.time i bs+volume bs+volume acc+volume (reader i bs)+1) := by
  unfold binaryReadStep
  erw [time_congr]
  simp only [time_pair,time_comp,time_fst,time_snd,time_cons,Function.comp_def,volume_pair,volume_cons]
  have hv := volume_pair (reader i bs).1 (reader i bs).2
  simp only [Prod.mk.eta] at hv
  omega
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} {α : I → Type} [∀ i, Coding (α i)]
variable (s : J → ℕ) (idx : J → I)
theorem binaryReadStep {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (bs : J → List Bool) (acc : ∀ j, List (α (idx j))) {d : ℕ}
    (ht : Poly s (fun j => R.time (idx j) (bs j)) d)
    (hb : Poly s (fun j => volume (bs j)) d)
    (ha : Poly s (fun j => volume (acc j)) d)
    (hv : Poly s (fun j => volume (reader (idx j) (bs j))) d) :
    Poly s (fun j => R.binaryReadStep.time (idx j) (bs j,acc j)) d := by
  apply Poly.of_le (fun j : J => Uniform.time_binaryReadStep_le R (idx j) (bs j) (acc j))
  poly_bound
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Binary
variable {α : Type u2}
theorem flatMap_drop_length (enc : α → List Bool) (xs : List α) (k : ℕ) (rest : List Bool) :
    ((xs.drop k).flatMap enc ++ rest).length ≤ (xs.flatMap enc ++ rest).length := by
  have h := congrArg List.length ((List.flatMap_append (xs := xs.take k) (ys := xs.drop k) (f := enc)))
  rw [List.take_append_drop] at h
  simp only [List.length_append] at h ⊢
  omega
end ThreeMachine.StackCompiler.Binary
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u3} {α : I → Type} [∀ i, Coding (α i)]
theorem time_binaryReadMany_le {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (i : I) (k : ℕ) (bs : List Bool) :
    R.binaryReadMany.time i (k,bs) ≤ 1000*(R.binaryReadStep.iterate.time i (k,(bs,[]))+
      (reverse (I := I) (α := α)).time i (((Binary.readStep (reader i))^[k] (bs,[])).2)+
      volume bs+k+volume ((Binary.readStep (reader i))^[k] (bs,[]))+1) := by
  unfold binaryReadMany
  erw [time_congr]
  simp only [time_comp,time_pair,time_fst,time_snd,time_nil,volume_pair,volume_nil,volume_nat,
    Function.comp_def,volume_reverse]
  have hv := volume_pair (((Binary.readStep (reader i))^[k] (bs,[])).1)
    (((Binary.readStep (reader i))^[k] (bs,[])).2)
  simp only [Prod.mk.eta] at hv
  omega
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} {α : I → Type} [∀ i, Coding (α i)]
variable (s : J → ℕ) (idx : J → I)
theorem binaryReadManyEncoded {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (encode : ∀ i, α i → List Bool)
    (hr : ∀ i a rest, reader i (encode i a ++ rest) = (a,rest))
    (xs : ∀ j, List (α (idx j))) (rest : J → List Bool)
    (hl : Poly s (fun j => (xs j).length) 1)
    (hb : Poly s (fun j => ((xs j).flatMap (encode (idx j)) ++ rest j).length) 1)
    (hx : Poly s (fun j => volume (xs j)) 2)
    (ht : Poly (fun p : Poly.StrictIterPool (fun j => (xs j).length) => s p.1)
      (fun p => R.time (idx p.1) (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1)) 3)
    (hv : Poly (fun p : Poly.StrictIterPool (fun j => (xs j).length) => s p.1)
      (fun p => volume (reader (idx p.1) (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1))) 2) :
    Poly s (fun j => R.binaryReadMany.time (idx j) ((xs j).length,(xs j).flatMap (encode (idx j)) ++ rest j)) 4 := by
  let m j := (xs j).length
  let a j := ((xs j).flatMap (encode (idx j)) ++ rest j,([] : List (α (idx j))))
  have hp (p : Poly.IterPool m) : (Binary.readStep (reader (idx p.1)))^[p.2.1] (a p.1) =
      (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1,((xs p.1).take p.2.1).reverse) := by
    simpa only [a,List.append_nil] using Binary.readStep_prefix (hr (idx p.1)) (xs p.1) (rest p.1) [] p.2.1 (by have := p.2.2; dsimp [m] at *; omega)
  have hrem : Poly (fun p : Poly.IterPool m => s p.1)
      (fun p => (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1).length) 1 :=
    Poly.of_le (fun p : Poly.IterPool m => Binary.flatMap_drop_length _ _ _ _) (hb.precomp Sigma.fst)
  have hbrem : Poly (fun p : Poly.IterPool m => s p.1)
      (fun p => volume (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1)) 1 := by poly_auto
  have hac : Poly (fun p : Poly.IterPool m => s p.1)
      (fun p => volume (((xs p.1).take p.2.1).reverse)) 2 := by
    simp only [volume_reverse]
    exact Poly.of_le (fun p : Poly.IterPool m => volume_sublist (List.take_sublist _ _)) (hx.precomp Sigma.fst)
  have hvol : Poly (fun p : Poly.IterPool m => s p.1)
      (fun p => volume ((Binary.readStep (reader (idx p.1)))^[p.2.1] (a p.1))) 2 := by
    simp only [hp,volume_pair]
    poly_bound
  let inc (p : Poly.StrictIterPool m) : Poly.IterPool m := ⟨p.1,⟨p.2.1,by have := p.2.2; omega⟩⟩
  have hstep := binaryReadStep (fun p : Poly.StrictIterPool m => s p.1) (fun p => idx p.1) R
    (fun p => ((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1)
    (fun p => ((xs p.1).take p.2.1).reverse) ht
    ((hbrem.precomp inc).lift (by decide)) ((hac.precomp inc).lift (by decide)) (hv.lift (by decide))
  have hti : Poly (fun p : Poly.StrictIterPool m => s p.1)
      (fun p => R.binaryReadStep.time (idx p.1) ((Binary.readStep (reader (idx p.1)))^[p.2.1] (a p.1))) 3 := by
    convert hstep using 1
    funext p
    rw [hp (inc p)]
  have hIter := Poly.iterateTimeStrict R.binaryReadStep idx m a hl hti hvol
  have hOut : Poly s (fun j => volume ((Binary.readStep (reader (idx j)))^[m j] (a j))) 2 :=
    hvol.precomp (fun j => ⟨j,⟨m j,by omega⟩⟩)
  have hRev : Poly s (fun j => ((Binary.readStep (reader (idx j)))^[m j] (a j)).2.length) 1 := by
    have he (j : J) := hp ⟨j,⟨m j,by omega⟩⟩
    simp only [he,List.length_reverse,List.length_take,m,Nat.min_self]
    exact hl
  have hSndVol : Poly s (fun j => volume (((Binary.readStep (reader (idx j)))^[m j] (a j)).2)) 2 := by
    apply Poly.of_le _ hOut
    intro j
    let t := (Binary.readStep (reader (idx j)))^[m j] (a j)
    have he := volume_pair t.1 t.2
    simp only [Prod.mk.eta] at he
    change volume t.2 ≤ volume t
    omega
  have hRevTime : Poly s (fun j => (Uniform.reverse (I := I) (α := α)).time (idx j)
      (((Binary.readStep (reader (idx j)))^[m j] (a j)).2)) 3 := by
    apply Poly.of_le (fun j : J => Uniform.time_reverse (idx j) (((Binary.readStep (reader (idx j)))^[m j] (a j)).2))
    poly_auto
  have hbs : Poly s (fun j => volume ((xs j).flatMap (encode (idx j)) ++ rest j)) 1 := by poly_auto
  apply Poly.of_le (fun j : J => Uniform.time_binaryReadMany_le R (idx j) (xs j).length
    ((xs j).flatMap (encode (idx j)) ++ rest j))
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
