import OAI.Computability.Scheduling.BinaryCosts

namespace OAI

universe u1

section
namespace ThreeMachine.StackCompiler.Binary
variable {α : Type u1}

theorem readStep_prefix {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest))
    (xs : List α) (rest : List Bool) (acc : List α) (k : ℕ) (hk : k ≤ xs.length) :
    (readStep reader)^[k] (xs.flatMap encode ++ rest,acc) =
      ((xs.drop k).flatMap encode ++ rest,(xs.take k).reverse ++ acc) := by
  have h := readStep_iterate hr (xs.take k) ((xs.drop k).flatMap encode ++ rest) acc
  rw [List.length_take,Nat.min_eq_left hk] at h
  rw [← List.append_assoc,← List.flatMap_append,List.take_append_drop] at h
  exact h

theorem readNat_rest_length (bs : List Bool) : (readNat bs).2.length ≤ bs.length := by
  exact (List.drop_sublist _ _).length_le.trans (List.drop_sublist _ _).length_le

theorem readEdge_rest_length (bs : List Bool) : (readEdge bs).2.length ≤ bs.length :=
  (readNat_rest_length _).trans (readNat_rest_length _)

theorem increment_length (bs : List Bool) : (increment bs).length ≤ bs.length+1 := by
  induction bs with
  | nil => simp [increment]
  | cons b bs ih => cases b <;> simp only [increment,List.length_cons] <;> omega

theorem encodeNat_length (n : ℕ) : (Computability.encodeNat n).length ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← increment_encodeNat]; exact (increment_length _).trans (Nat.add_le_add_right ih 1)

theorem encodeNat_length_le (n : ℕ) : (ThreeMachine.encodeNat n).length ≤ 2*n+1 := by
  have h := encodeNat_length n
  simp only [ThreeMachine.encodeNat,List.length_append,List.length_replicate,List.length_cons]
  omega

end ThreeMachine.StackCompiler.Binary
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)

theorem binaryIncrement (bs : J → List Bool) (hl : Poly s (fun j => (bs j).length) 1) :
    Poly s (fun j => (Uniform.binaryIncrement (I := I)).time (idx j) (bs j)) 3 := by
  have ht := binaryLeading s idx bs hl
  have hk : Poly s (fun j => Binary.leading (bs j)) 1 := Poly.of_le (fun j => Binary.leading_le _) hl
  poly_auto

theorem rawEncodeNat (k : J → ℕ) (hk : Poly s k 1) :
    Poly s (fun j => (Uniform.rawEncodeNat (I := I)).time (idx j) (k j)) 4 := by
  have hp : Poly (fun p : Poly.IterPool k => s p.1) (fun p => p.2.1) 1 :=
    Poly.of_le (fun p => Nat.le_of_lt_succ p.2.2) (hk.precomp Sigma.fst)
  have hlen : Poly (fun p : Poly.IterPool k => s p.1)
      (fun p => (Binary.increment^[p.2.1] []).length) 1 := by
    simp only [Binary.iterate_increment]
    exact Poly.of_le (fun p => Binary.encodeNat_length p.2.1) hp
  have ht := binaryIncrement (fun p : Poly.IterPool k => s p.1) (fun p => idx p.1)
    (fun p => Binary.increment^[p.2.1] []) hlen
  have hv : Poly (fun p : Poly.IterPool k => s p.1)
      (fun p => volume (Binary.increment^[p.2.1] [])) 1 := by poly_auto
  have hiter := Poly.iterateTime (Uniform.binaryIncrement (I := I)) idx k (fun _ => []) hk ht hv
  poly_auto

theorem binaryEncodeNat (k : J → ℕ) (hk : Poly s k 1) :
    Poly s (fun j => (Uniform.binaryEncodeNat (I := I)).time (idx j) (k j)) 4 := by
  have ht := rawEncodeNat s idx k hk
  have hl : Poly s (fun j => (Computability.encodeNat (k j)).length) 1 :=
    Poly.of_le (fun j => Binary.encodeNat_length _) hk
  poly_auto

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s : J → ℕ} {α : J → Type} [∀ j, Coding (α j)] {l v : ℕ}
theorem volumeListOfPool (xs : ∀ j, List (α j))
    (hl : Poly s (fun j => (xs j).length) l)
    (hv : Poly (fun p : ListPool xs => s p.1) (fun p => volume p.2.1) v) :
    Poly s (fun j => volume (xs j)) (l+v) := by
  obtain ⟨C,hC⟩ := hv
  apply volumeList hl (powerBase s C v)
  intro j a ha
  exact hC ⟨j,⟨a,ha⟩⟩
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)

theorem binaryEncodeNatMap (xs : J → List ℕ) (hl : Poly s (fun j => (xs j).length) 1)
    (hk : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => (Uniform.binaryEncodeNat (I := I)).mapList.time (idx j) (xs j)) 5 := by
  have ht := binaryEncodeNat (fun p : Poly.ListPool xs => s p.1) (fun p => idx p.1)
    (fun p => p.2.1) hk
  have vxp : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => volume p.2.1) 1 := by poly_auto
  have vx := Poly.volumeListOfPool xs hl vxp
  have hendlen : Poly (fun p : Poly.ListPool xs => s p.1)
      (fun p => (ThreeMachine.encodeNat p.2.1).length) 1 := by
    apply Poly.of_le (fun p : Poly.ListPool xs => Binary.encodeNat_length_le p.2.1)
    poly_auto
  have hendvol : Poly (fun p : Poly.ListPool xs => s p.1)
      (fun p => volume (ThreeMachine.encodeNat p.2.1)) 1 := by poly_auto
  poly_auto

theorem volumeEncodeNatList (xs : J → List ℕ) (hl : Poly s (fun j => (xs j).length) 1)
    (hk : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => volume ((xs j).map ThreeMachine.encodeNat)) 2 := by
  have hb : Poly (fun p : Poly.ListPool xs => s p.1)
      (fun p => (ThreeMachine.encodeNat p.2.1).length) 1 := by
    apply Poly.of_le (fun p : Poly.ListPool xs => Binary.encodeNat_length_le p.2.1)
    poly_auto
  have hv : Poly (fun p : Poly.ListPool xs => s p.1)
      (fun p => volume (ThreeMachine.encodeNat p.2.1)) 1 := by poly_auto
  exact Poly.volumeMap _root_.id xs (fun _ => ()) (f := fun _ (x : ℕ × Unit) => ThreeMachine.encodeNat x.1) hl hv

theorem binaryEncodeList (xs : J → List ℕ) (hl : Poly s (fun j => (xs j).length) 1)
    (hk : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => (Uniform.binaryEncodeList (I := I)).time (idx j) (xs j)) 5 := by
  have hMap := binaryEncodeNatMap s idx xs hl hk
  have hMV := volumeEncodeNatList s xs hl hk
  have hfv : Poly s (fun j => volume (((xs j).map ThreeMachine.encodeNat).flatten)) 2 :=
    Poly.of_le (fun j : J => by rw [volume_flatten]; omega) hMV
  have hfl := Poly.lengthVolume _ hfv
  have hFlat : Poly s (fun j => (Uniform.flatten (I := I) (α := fun _ => Bool)).time
      (idx j) ((xs j).map ThreeMachine.encodeNat)) 4 := by
    apply Poly.of_le (fun j : J => Uniform.time_flatten (α := fun _ : I => Bool) (idx j) ((xs j).map ThreeMachine.encodeNat))
    have hlm : Poly s (fun j => ((xs j).map ThreeMachine.encodeNat).length) 1 := by
      simpa only [List.length_map] using hl
    poly_auto
  have hc := binaryEncodeNat s idx (fun j => (xs j).length) hl
  have vxp : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => volume p.2.1) 1 := by poly_auto
  have vx := Poly.volumeListOfPool xs hl vxp
  have hlenhead : Poly s (fun j => (ThreeMachine.encodeNat (xs j).length).length) 1 := by
    apply Poly.of_le (fun j => Binary.encodeNat_length_le _)
    poly_auto
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler

theorem volume_option_le_getD {α : Type} [Coding α] (o : Option α) (a : α) :
    volume o ≤ volume (o.getD a)+2 := by
  cases o <;> simp only [Option.getD_none,Option.getD_some,volume_none,volume_some] <;> omega
end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)
theorem lengthEncodeNatList (xs : J → List ℕ) (hl : Poly s (fun j => (xs j).length) 1)
    (hk : Poly (fun p : Poly.ListPool xs => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => (ThreeMachine.encodeList ThreeMachine.encodeNat (xs j)).length) 2 := by
  have hMV := volumeEncodeNatList s xs hl hk
  have hfv : Poly s (fun j => volume (((xs j).map ThreeMachine.encodeNat).flatten)) 2 :=
    Poly.of_le (fun j : J => by rw [volume_flatten]; omega) hMV
  have hfl := Poly.lengthVolume _ hfv
  have hhead : Poly s (fun j => (ThreeMachine.encodeNat (xs j).length).length) 1 := by
    apply Poly.of_le (fun j : J => Binary.encodeNat_length_le _)
    poly_auto
  simp only [ThreeMachine.encodeList,List.length_append,List.flatMap_def]
  poly_auto

theorem binaryEncodeAnswer (o : J → Option (List ℕ))
    (hl : Poly s (fun j => ((o j).getD []).length) 1)
    (hk : Poly (fun p : Poly.ListPool (fun j => (o j).getD []) => s p.1) (fun p => p.2.1) 1) :
    Poly s (fun j => (Uniform.binaryEncodeAnswer (I := I)).time (idx j) (o j)) 5 := by
  have hE := binaryEncodeList s idx (fun j => (o j).getD []) hl hk
  have hitem : Poly (fun p : Poly.ListPool (fun j => (o j).getD []) => s p.1)
      (fun p => volume p.2.1) 1 := by poly_auto
  have hL := Poly.volumeListOfPool (fun j => (o j).getD []) hl hitem
  have hO : Poly s (fun j => volume (o j)) 2 := by
    apply Poly.of_le (fun j : J => volume_option_le_getD (o j) [])
    poly_bound
  have hEncoded := lengthEncodeNatList s (fun j => (o j).getD []) hl hk
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
