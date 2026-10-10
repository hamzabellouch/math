import OAI.Computability.Scheduling.ReaderCosts

namespace OAI

section
namespace ThreeMachine.StackCompiler.Binary
variable {α : Type}
theorem readNat_listHeader (enc : α → List Bool) (xs : List α) (rest : List Bool) :
    readNat (ThreeMachine.encodeList enc xs ++ rest) = (xs.length,xs.flatMap enc ++ rest) := by
  simp only [ThreeMachine.encodeList,List.append_assoc,readNat_encodeNat]
theorem readAtSuffix {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest)) (xs : List α) (rest : List Bool)
    (k : ℕ) (hk : k < xs.length) :
    reader ((xs.drop k).flatMap encode ++ rest) = (xs[k],(xs.drop (k+1)).flatMap encode ++ rest) := by
  rw [List.drop_eq_getElem_cons hk,List.flatMap_cons,List.append_assoc,hr]
end ThreeMachine.StackCompiler.Binary
namespace ThreeMachine.StackCompiler.Realizer
theorem time_pred (n : ℕ) : pred.time n = volume n+2 := rfl
end ThreeMachine.StackCompiler.Realizer
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type} {α : I → Type} [∀ i, Coding (α i)]
theorem time_binaryReadList {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (i : I) (bs : List Bool) :
    R.binaryReadList.time i bs = binaryReadNat.time i bs +
      R.binaryReadMany.time i (Binary.readNat bs)+10*(volume (Binary.readNat bs)+1) := by
  change (binaryReadNat.comp R.binaryReadMany).time i bs = _
  exact time_comp _ _ _ _
theorem time_binaryReadEdge_le (i : I) (bs : List Bool) :
    (binaryReadEdge (I := I)).time i bs ≤ 1000*(binaryReadNat.time i bs+
      binaryReadNat.time i (Binary.readNat bs).2+volume bs+
      volume (Binary.readNat bs)+volume (Binary.readNat (Binary.readNat bs).2)+1) := by
  let A := binaryReadNat (I := I)
  let B := A.comp (snd.comp binaryReadNat)
  change (((A.comp (fst.comp (Realizer.pred.uniform I))).pair
      (B.comp (fst.comp (Realizer.pred.uniform I)))).pair (B.comp snd)).time i bs ≤ _
  simp only [A,B,time_pair,time_comp,time_snd,time_fst,time_uniform,Realizer.time_pred,
    Function.comp_apply,volume_prod,volume_nat,Nat.pred_eq_sub_one]
  omega
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)

theorem volumeNatBools (k : J → ℕ) (bs : J → List Bool)
    (hk : Poly s k 1) (hb : Poly s (fun j => (bs j).length) 1) :
    Poly s (fun j => volume (k j,bs j)) 1 := by
  have hv := Poly.of_le (fun j : J => volume_boolList_le (bs j))
    (show Poly s (fun j => 4*(bs j).length+1) 1 from by poly_auto)
  simp only [volume_pair,volume_nat]
  poly_auto

theorem binaryReadNatEncoded (k : J → ℕ) (rest : J → List Bool)
    (hk : Poly s k 1) (hl : Poly s (fun j => (ThreeMachine.encodeNat (k j) ++ rest j).length) 1) :
    Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j) (ThreeMachine.encodeNat (k j) ++ rest j)) 3 := by
  apply binaryReadNat s idx _ hl
  simpa only [Binary.readNat_encodeNat] using hk

theorem binaryReadEdgeCost (bs : J → List Bool)
    (hA : Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j) (bs j)) 3)
    (hB : Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j) (Binary.readNat (bs j)).2) 3)
    (hvI : Poly s (fun j => volume (bs j)) 1)
    (hvA : Poly s (fun j => volume (Binary.readNat (bs j))) 1)
    (hvB : Poly s (fun j => volume (Binary.readNat (Binary.readNat (bs j)).2)) 1) :
    Poly s (fun j => (Uniform.binaryReadEdge (I := I)).time (idx j) (bs j)) 3 := by
  apply Poly.of_le (fun j : J => Uniform.time_binaryReadEdge_le (idx j) (bs j))
  poly_auto

theorem binaryReadEdgeEncoded (edge : J → ℕ × ℕ) (rest : J → List Bool)
    (ha : Poly s (fun j => (edge j).1) 1) (hb : Poly s (fun j => (edge j).2) 1)
    (hl : Poly s (fun j => (Binary.encodeEdge (edge j) ++ rest j).length) 1) :
    Poly s (fun j => (Uniform.binaryReadEdge (I := I)).time (idx j) (Binary.encodeEdge (edge j) ++ rest j)) 3 := by
  have he (j) : Binary.readNat (Binary.encodeEdge (edge j) ++ rest j) =
      ((edge j).1+1,ThreeMachine.encodeNat ((edge j).2+1) ++ rest j) := by
    simp only [Binary.encodeEdge,List.append_assoc,Binary.readNat_encodeNat]
  have ha1 : Poly s (fun j => (edge j).1+1) 1 := ha.add (Poly.const s 1)
  have hb1 : Poly s (fun j => (edge j).2+1) 1 := hb.add (Poly.const s 1)
  have hA := binaryReadNat s idx (fun j => Binary.encodeEdge (edge j) ++ rest j) hl
    (show Poly s (fun j => (Binary.readNat (Binary.encodeEdge (edge j) ++ rest j)).1) 1 from by
      simpa only [he] using ha1)
  have hRest : Poly s (fun j => (ThreeMachine.encodeNat ((edge j).2+1) ++ rest j).length) 1 := by
    apply Poly.of_le _ hl
    intro j
    simp only [List.length_append,Binary.encodeEdge]
    omega
  have hB := binaryReadNatEncoded s idx (fun j => (edge j).2+1) rest hb1 hRest
  have hvA : Poly s (fun j => volume (Binary.readNat (Binary.encodeEdge (edge j) ++ rest j))) 1 := by
    simp only [he]
    exact volumeNatBools s (fun j => (edge j).1+1) _ ha1 hRest
  have hrl : Poly s (fun j => (rest j).length) 1 :=
    Poly.of_le (fun j : J => by simp only [List.length_append]; omega) hRest
  have hvB : Poly s (fun j => volume (Binary.readNat (ThreeMachine.encodeNat ((edge j).2+1) ++ rest j))) 1 := by
    simp only [Binary.readNat_encodeNat]
    exact volumeNatBools s (fun j => (edge j).2+1) _ hb1 hrl
  have hExact : Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j)
      (Binary.readNat (Binary.encodeEdge (edge j) ++ rest j)).2) 3 := by simpa only [he] using hB
  have hvExact : Poly s (fun j => volume (Binary.readNat (Binary.readNat (Binary.encodeEdge (edge j) ++ rest j)).2)) 1 := by
    simpa only [he] using hvB
  have hvIn : Poly s (fun j => volume (Binary.encodeEdge (edge j) ++ rest j)) 1 :=
    Poly.of_le (fun j => volume_boolList_le _) ((Poly.const s 4 |>.mul hl).add (Poly.const s 1))
  exact binaryReadEdgeCost s idx _ hA hExact hvIn hvA hvExact

variable {α : I → Type} [∀ i, Coding (α i)]
theorem binaryReadListEncoded {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader)
    (encode : ∀ i, α i → List Bool)
    (hr : ∀ i a rest, reader i (encode i a ++ rest) = (a,rest))
    (xs : ∀ j, List (α (idx j))) (rest : J → List Bool)
    (hl : Poly s (fun j => (xs j).length) 1)
    (hb : Poly s (fun j => (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j).length) 1)
    (hx : Poly s (fun j => volume (xs j)) 2)
    (ht : Poly (fun p : Poly.StrictIterPool (fun j => (xs j).length) => s p.1)
      (fun p => R.time (idx p.1) (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1)) 3)
    (hv : Poly (fun p : Poly.StrictIterPool (fun j => (xs j).length) => s p.1)
      (fun p => volume (reader (idx p.1) (((xs p.1).drop p.2.1).flatMap (encode (idx p.1)) ++ rest p.1))) 2) :
    Poly s (fun j => R.binaryReadList.time (idx j) (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j)) 4 := by
  have hpay : Poly s (fun j => ((xs j).flatMap (encode (idx j)) ++ rest j).length) 1 := by
    apply Poly.of_le _ hb
    intro j
    simp only [ThreeMachine.encodeList,List.length_append]
    omega
  have hM := binaryReadManyEncoded s idx R encode hr xs rest hl hpay hx ht hv
  have hN := binaryReadNat s idx (fun j => ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j) hb
    (show Poly s (fun j => (Binary.readNat (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j)).1) 1 from by
      simpa only [Binary.readNat_listHeader] using hl)
  have hExact : Poly s (fun j => R.binaryReadMany.time (idx j)
      (Binary.readNat (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j))) 4 := by
    simpa only [Binary.readNat_listHeader] using hM
  have hvN : Poly s (fun j => volume (Binary.readNat (ThreeMachine.encodeList (encode (idx j)) (xs j) ++ rest j))) 1 := by
    simp only [Binary.readNat_listHeader]
    exact volumeNatBools s _ _ hl hpay
  simp only [Uniform.time_binaryReadList]
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)
theorem binaryNatList (xs : J → List ℕ) (rest : J → List Bool) (K : J → ℕ)
    (hl : Poly s (fun j => (xs j).length) 1) (hK : Poly s K 1)
    (hB : ∀ j a, a ∈ xs j → a ≤ K j)
    (hb : Poly s (fun j => (ThreeMachine.encodeList ThreeMachine.encodeNat (xs j) ++ rest j).length) 1) :
    Poly s (fun j => (Uniform.binaryReadNat (I := I)).binaryReadList.time (idx j)
      (ThreeMachine.encodeList ThreeMachine.encodeNat (xs j) ++ rest j)) 4 := by
  let P := Poly.StrictIterPool (fun j => (xs j).length)
  let sp (p : P) := s p.1
  let a (p : P) := (xs p.1)[p.2.val]
  let suf (p : P) := ((xs p.1).drop p.2.val).flatMap ThreeMachine.encodeNat ++ rest p.1
  have hpay : Poly s (fun j => ((xs j).flatMap ThreeMachine.encodeNat ++ rest j).length) 1 := by
    apply Poly.of_le _ hb
    intro j
    simp only [ThreeMachine.encodeList,List.length_append]
    omega
  have hsuf : Poly sp (fun p => (suf p).length) 1 := by
    apply Poly.of_le (fun p : P => Binary.flatMap_drop_length _ _ _ _)
    exact hpay.precomp Sigma.fst
  have hafter : Poly sp (fun p => (((xs p.1).drop (p.2.val+1)).flatMap ThreeMachine.encodeNat ++ rest p.1).length) 1 := by
    apply Poly.of_le (fun p : P => Binary.flatMap_drop_length _ _ _ _)
    exact hpay.precomp Sigma.fst
  have ha : Poly sp a 1 := Poly.of_le (fun p => hB p.1 (a p) (List.getElem_mem _)) (hK.precomp Sigma.fst)
  have he (p : P) : Binary.readNat (suf p) =
      (a p,((xs p.1).drop (p.2.val+1)).flatMap ThreeMachine.encodeNat ++ rest p.1) :=
    Binary.readAtSuffix Binary.readNat_encodeNat (xs p.1) (rest p.1) _ p.2.isLt
  have hval : Poly sp (fun p => (Binary.readNat (suf p)).1) 1 := by simpa only [he] using ha
  have hT := binaryReadNat sp (fun p => idx p.1) suf hsuf hval
  have hV : Poly sp (fun p => volume (Binary.readNat (suf p))) 2 := by
    simp only [he]
    exact (volumeNatBools sp a _ ha hafter).lift (by omega)
  have hX : Poly s (fun j => volume (xs j)) 2 := by
    apply Poly.volumeList hl (show Poly s (fun j => 2*K j+1) 1 from by poly_bound)
    intro j a ha
    rw [volume_nat]
    have := hB j a ha
    omega
  exact binaryReadListEncoded s idx (Uniform.binaryReadNat (I := I)) (fun _ => ThreeMachine.encodeNat)
    (fun _ => Binary.readNat_encodeNat) xs rest hl hb hX hT hV
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)
theorem binaryEdgeList (xs : J → List (ℕ × ℕ)) (rest : J → List Bool) (K : J → ℕ)
    (hl : Poly s (fun j => (xs j).length) 1) (hK : Poly s K 1)
    (hB : ∀ j a, a ∈ xs j → a.1 ≤ K j ∧ a.2 ≤ K j)
    (hb : Poly s (fun j => (ThreeMachine.encodeList Binary.encodeEdge (xs j) ++ rest j).length) 1) :
    Poly s (fun j => (Uniform.binaryReadEdge (I := I)).binaryReadList.time (idx j)
      (ThreeMachine.encodeList Binary.encodeEdge (xs j) ++ rest j)) 4 := by
  let P := Poly.StrictIterPool (fun j => (xs j).length)
  let sp (p : P) := s p.1
  let a (p : P) := (xs p.1)[p.2.val]
  let suf (p : P) := ((xs p.1).drop p.2.val).flatMap Binary.encodeEdge ++ rest p.1
  have hpay : Poly s (fun j => ((xs j).flatMap Binary.encodeEdge ++ rest j).length) 1 := by
    apply Poly.of_le _ hb
    intro j
    simp only [ThreeMachine.encodeList,List.length_append]
    omega
  have hsuf : Poly sp (fun p => (suf p).length) 1 := by
    apply Poly.of_le (fun p : P => Binary.flatMap_drop_length _ _ _ _)
    exact hpay.precomp Sigma.fst
  have hafter : Poly sp (fun p => (((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1).length) 1 := by
    apply Poly.of_le (fun p : P => Binary.flatMap_drop_length _ _ _ _)
    exact hpay.precomp Sigma.fst
  have ha : Poly sp (fun p => (a p).1) 1 :=
    Poly.of_le (fun p => (hB p.1 (a p) (List.getElem_mem _)).1) (hK.precomp Sigma.fst)
  have hc : Poly sp (fun p => (a p).2) 1 :=
    Poly.of_le (fun p => (hB p.1 (a p) (List.getElem_mem _)).2) (hK.precomp Sigma.fst)
  have hs (p : P) : suf p = Binary.encodeEdge (a p) ++
      ((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1 := by
    dsimp [suf,a]
    rw [List.drop_eq_getElem_cons p.2.isLt,List.flatMap_cons,List.append_assoc]
  have hlenc : Poly sp (fun p => (Binary.encodeEdge (a p) ++
      (((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1)).length) 1 := by
    simpa only [hs,List.append_assoc] using hsuf
  have hT0 := binaryReadEdgeEncoded sp (fun p => idx p.1) a
    (fun p => ((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1) ha hc hlenc
  have hT : Poly sp (fun p => (Uniform.binaryReadEdge (I := I)).time (idx p.1) (suf p)) 3 := by
    simpa only [hs,List.append_assoc] using hT0
  have he (p : P) : Binary.readEdge (suf p) =
      (a p,((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1) :=
    Binary.readAtSuffix Binary.readEdge_correct (xs p.1) (rest p.1) _ p.2.isLt
  have hV : Poly sp (fun p => volume (Binary.readEdge (suf p))) 2 := by
    simp only [he,volume_prod,volume_nat]
    have hbV := Poly.of_le (fun p : P => volume_boolList_le
      (((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1))
      (show Poly sp (fun p => 4*((((xs p.1).drop (p.2.val+1)).flatMap Binary.encodeEdge ++ rest p.1).length)+1) 1 from by poly_bound)
    poly_auto
  have hX : Poly s (fun j => volume (xs j)) 2 := by
    apply Poly.volumeList hl (show Poly s (fun j => 4*K j+3) 1 from by poly_bound)
    intro j a ha
    rw [volume_prod,volume_nat,volume_nat]
    have := hB j a ha
    omega
  exact binaryReadListEncoded s idx (Uniform.binaryReadEdge (I := I)) (fun _ => Binary.encodeEdge)
    (fun _ => Binary.readEdge_correct) xs rest hl hb hX hT hV
end ThreeMachine.StackCompiler.Costs
end

end OAI
