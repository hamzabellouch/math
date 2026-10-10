import OAI.Computability.Scheduling.Parser

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

section
namespace ThreeMachine.StackCompiler.Costs
private theorem valueStepCost : Poly (fun x : Bool × ℕ => x.2)
    (fun x => (Uniform.binaryValueStep (I := Unit)).time () x) 2 := by poly_auto
private theorem leadingStepCost : Poly (fun x : Bool × (Bool × ℕ) => x.2.2)
    (fun x => (Uniform.binaryLeadingStep (I := Unit)).time () x) 1 := by poly_auto
noncomputable def valueStepC : ℕ := Classical.choose valueStepCost
noncomputable def leadingStepC : ℕ := Classical.choose leadingStepCost
end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1}
theorem time_binaryValueStep_le (i : I) (x : Bool × ℕ) :
    (binaryValueStep (I := I)).time i x ≤ Costs.valueStepC*(x.2+2)^2 := by
  change (binaryValueStep (I := Unit)).time () x ≤ _
  exact Classical.choose_spec Costs.valueStepCost x
theorem time_binaryLeadingStep_le (i : I) (x : Bool × (Bool × ℕ)) :
    (binaryLeadingStep (I := I)).time i x ≤ Costs.leadingStepC*(x.2.2+2) := by
  change (binaryLeadingStep (I := Unit)).time () x ≤ _
  simpa only [Costs.leadingStepC,pow_one] using Classical.choose_spec Costs.leadingStepCost x
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Realizer
variable {α : Type u2} {β : Type u3} [Coding α] [Coding β] {f : α × β → β}
theorem foldTime_prefix_le (R : Realizer f) (xs : List α) (b : β) (T V : ℕ)
    (hvol : ∀ ys zs, xs = ys ++ zs → volume (ys.foldl (fun b a => f (a,b)) b) ≤ V)
    (htime : ∀ ys a zs, xs = ys ++ a :: zs → R.time (a,ys.foldl (fun b a => f (a,b)) b) ≤ T) :
    foldTime R b xs ≤ xs.length*(T+20*(volume xs+2*V+1))+1 := by
  induction xs generalizing b with
  | nil => simp only [foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have hi := ih (f (a,b))
      (fun ys zs he => by
        have h := hvol (a::ys) zs (by simpa using congrArg (List.cons a) he)
        simpa only [List.foldl_cons] using h)
      (fun ys c zs he => by
        have h := htime (a::ys) c zs (by simpa using congrArg (List.cons a) he)
        simpa only [List.foldl_cons] using h)
    have ht : R.time (a,b) ≤ T := htime [] a xs rfl
    have hb : volume b ≤ V := hvol [] (a::xs) rfl
    have hc : volume (f (a,b)) ≤ V := hvol [a] xs rfl
    simp only [foldTime,volume_cons,List.length_cons] at hi ⊢
    nlinarith [volume_pos a,volume_pos xs]
end ThreeMachine.StackCompiler.Realizer
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u4} {α : I → Type u5} {β : I → Type u6} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
variable {f : ∀ i, α i × β i → β i}
theorem time_fold_prefix_le (R : Uniform f) (i : I) (xs : List (α i)) (b : β i) (T V : ℕ)
    (hvol : ∀ ys zs, xs = ys ++ zs → volume (ys.foldl (fun b a => f i (a,b)) b) ≤ V)
    (htime : ∀ ys a zs, xs = ys ++ a :: zs → R.time i (a,ys.foldl (fun b a => f i (a,b)) b) ≤ T) :
    R.fold.time i (xs,b) ≤ 50*(xs.length+1)*(T+volume xs+V+1) := by
  have h := Realizer.foldTime_prefix_le (R.specialize i) xs b T V hvol htime
  rw [time_fold]
  simp only [volume_pair]
  have hv : volume b ≤ V := hvol [] xs rfl
  nlinarith [volume_pos xs]
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Binary

theorem valueStep_fold_ge (bs : List Bool) (n : ℕ) :
    n ≤ bs.foldl (fun n b => valueStep (b,n)) n := by
  induction bs generalizing n with
  | nil => rfl
  | cons b bs ih =>
    rw [List.foldl_cons]
    exact le_trans (by unfold valueStep; omega) (ih _)

theorem value_prefix_le (bs ys zs : List Bool) (h : bs.reverse = ys ++ zs) :
    ys.foldl (fun n b => valueStep (b,n)) 0 ≤ value bs := by
  rw [← value_fold,h,List.foldl_append]
  exact valueStep_fold_ge _ _

theorem leading_le (bs : List Bool) : leading bs ≤ bs.length :=
  (List.takeWhile_sublist id).length_le

end ThreeMachine.StackCompiler.Binary
namespace ThreeMachine.StackCompiler

theorem volume_boolList_le (bs : List Bool) : volume bs ≤ 4*bs.length+1 := by
  have h := volume_list_le bs 3 (fun a _ => volume_bool a)
  omega
namespace Uniform
variable {I : Type u7}

theorem time_binaryValueFold_le (i : I) (bs : List Bool) :
    binaryValueStep.fold.time i (bs.reverse,0) ≤
      50*(bs.length+1)*(Costs.valueStepC*(Binary.value bs+2)^2 + volume bs+2*Binary.value bs+2) := by
  have hv : ∀ ys zs, bs.reverse = ys ++ zs →
      volume (ys.foldl (fun n b => Binary.valueStep (b,n)) 0) ≤ 2*Binary.value bs+1 := by
    intro ys zs h; rw [volume_nat]; have := Binary.value_prefix_le bs ys zs h; omega
  have ht : ∀ ys a zs, bs.reverse = ys ++ a::zs →
      binaryValueStep.time i (a,ys.foldl (fun n b => Binary.valueStep (b,n)) 0) ≤
        Costs.valueStepC*(Binary.value bs+2)^2 := by
    intro ys a zs h
    exact (time_binaryValueStep_le i _).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by have := Binary.value_prefix_le bs ys (a::zs) h; omega) _))
  have h := time_fold_prefix_le binaryValueStep i bs.reverse 0 _ _ hv ht
  simpa only [List.length_reverse,volume_reverse, Nat.add_assoc] using h

theorem time_binaryLeadingFold_le (i : I) (bs : List Bool) :
    binaryLeadingStep.fold.time i (bs,(true,0)) ≤
      50*(bs.length+1)*(Costs.leadingStepC*(bs.length+2) + volume bs+2*bs.length+6) := by
  have hb : ∀ ys zs, bs = ys ++ zs →
      (ys.foldl (fun s a => Binary.leadingStep (a,s)) (true,0)).2 ≤ bs.length := by
    intro ys zs h
    rw [Binary.leading_fold]; simp only [ite_true,Nat.zero_add]
    have hL := Binary.leading_le ys
    rw [h,List.length_append]; omega
  have hv : ∀ ys zs, bs = ys ++ zs →
      volume (ys.foldl (fun s a => Binary.leadingStep (a,s)) (true,0)) ≤ 2*bs.length+5 := by
    intro ys zs h
    rw [volume_prod,volume_nat]
    have := volume_bool (ys.foldl (fun s a => Binary.leadingStep (a,s)) (true,0)).1
    have := hb ys zs h; omega
  have ht : ∀ ys a zs, bs = ys ++ a::zs →
      binaryLeadingStep.time i (a,ys.foldl (fun s a => Binary.leadingStep (a,s)) (true,0)) ≤
        Costs.leadingStepC*(bs.length+2) := by
    intro ys a zs h
    exact (time_binaryLeadingStep_le i _).trans (Nat.mul_le_mul_left _ (by dsimp only; have := hb ys (a::zs) h; omega))
  have h := time_fold_prefix_le binaryLeadingStep i bs (true,0) _ _ hv ht
  simpa only [Nat.add_assoc] using h
end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
private theorem takeStepCost (I : Type u8) :
    Poly (fun x : Σ _ : I, List Bool × List Bool => x.2.1.length+x.2.2.length)
      (fun x => (Uniform.takeStep (I := I) (α := fun _ => Bool)).time x.1 x.2) 1 := by
  let sz (x : Σ _ : I, List Bool × List Bool) := x.2.1.length+x.2.2.length
  have hx : Poly sz (fun x => x.2.1.length) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size sz)
  have hy : Poly sz (fun x => x.2.2.length) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size sz)
  have hhead : Poly sz (fun x => volume x.2.1.head?) 0 := by
    apply Poly.volumeOption _ (Poly.const sz 3)
    intro x b hb; exact volume_bool b
  have htail : Poly sz (fun x => x.2.1.tail.length) 1 :=
    Poly.of_le (fun x => by simp only [List.length_tail]; omega) hx
  have hget : Poly sz (fun x => ((x.2.1.head?.map (fun a => a :: x.2.2)).getD x.2.2).length) 1 := by
    apply Poly.of_le (g := fun x => x.2.2.length+1)
    · intro x
      cases x.2.1 <;> simp
    · poly_bound
  poly_auto
noncomputable def takeStepC (I : Type u9) : ℕ := Classical.choose (takeStepCost I)
end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u10}
theorem time_binaryTakeStep_le (i : I) (x : List Bool × List Bool) :
    (takeStep (I := I) (α := fun _ => Bool)).time i x ≤ Costs.takeStepC I*(x.1.length+x.2.length+2) := by
  simpa only [Costs.takeStepC,pow_one] using Classical.choose_spec (Costs.takeStepCost I) ⟨i,x⟩
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u11}

theorem time_binaryTakeIter_le (i : I) (bs : List Bool) (k : ℕ) :
    (takeStep (α := fun _ : I => Bool)).iterate.time i (k,(bs,[])) ≤
      10000*(k+1)*(Costs.takeStepC I*(2*bs.length+2)+(8*bs.length+3)+k+1) := by
  apply time_iterate_le
  · intro j hj
    rw [Binary.takeStep_iterate]
    apply (time_binaryTakeStep_le i _).trans
    apply Nat.mul_le_mul_left
    simp only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero]
    have h₁ := (List.drop_sublist j bs).length_le
    have h₂ := (List.take_sublist j bs).length_le
    omega
  · intro j hj
    rw [Binary.takeStep_iterate,volume_pair]
    have h₁ := volume_boolList_le (bs.drop j)
    have h₂ := volume_boolList_le ((bs.take j).reverse ++ [])
    simp only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero] at h₂
    have h₃ := (List.drop_sublist j bs).length_le
    have h₄ := (List.take_sublist j bs).length_le
    omega
end Uniform
namespace Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I) (bs : J → List Bool)

theorem binaryValue (hl : Poly s (fun j => (bs j).length) 1)
    (hv : Poly s (fun j => Binary.value (bs j)) 1) :
    Poly s (fun j => (Uniform.binaryValue (I := I)).time (idx j) (bs j)) 3 := by
  have hb : Poly s (fun j => volume (bs j)) 1 := by poly_auto
  have hfold : Poly s (fun j => (Uniform.binaryValueStep (I := I)).fold.time (idx j) ((bs j).reverse,0)) 3 := by
    apply Poly.of_le (fun j => Uniform.time_binaryValueFold_le (idx j) (bs j))
    poly_bound
  poly_auto

theorem binaryLeading (hl : Poly s (fun j => (bs j).length) 1) :
    Poly s (fun j => (Uniform.binaryLeading (I := I)).time (idx j) (bs j)) 2 := by
  have hb : Poly s (fun j => volume (bs j)) 1 := by poly_auto
  have hfold : Poly s (fun j => (Uniform.binaryLeadingStep (I := I)).fold.time (idx j) (bs j,(true,0))) 2 := by
    apply Poly.of_le (fun j => Uniform.time_binaryLeadingFold_le (idx j) (bs j))
    poly_bound
  have hfv : Poly s (fun j => ((bs j).foldl (fun s a => Binary.leadingStep (a,s)) (true,0)).2) 1 := by
    simp only [Binary.leading_fold,ite_true,Nat.zero_add]
    exact Poly.of_le (fun j => Binary.leading_le (bs j)) hl
  poly_auto

theorem binaryTake (k : J → ℕ) (hl : Poly s (fun j => (bs j).length) 1) (hk : Poly s k 1) :
    Poly s (fun j => (Uniform.take (I := I) (α := fun _ => Bool)).time (idx j) (bs j,k j)) 2 := by
  have hb : Poly s (fun j => volume (bs j)) 1 := by poly_auto
  have hIter : Poly s (fun j => (Uniform.takeStep (I := I) (α := fun _ => Bool)).iterate.time
      (idx j) (k j,(bs j,[]))) 2 := by
    apply Poly.of_le (fun j => Uniform.time_binaryTakeIter_le (idx j) (bs j) (k j))
    poly_bound
  have htake : Poly s (fun j => volume ((bs j).take (k j))) 1 :=
    Poly.of_le (fun j => volume_sublist (List.take_sublist _ _)) hb
  have hout : Poly s (fun j => volume (Binary.takeStep^[k j] (bs j,[]))) 1 := by
    simp only [Binary.takeStep_iterate,List.append_nil]
    poly_auto
  have hlen : Poly s (fun j => (Binary.takeStep^[k j] (bs j,[])).2.length) 1 := by
    simp only [Binary.takeStep_iterate,List.append_nil,List.length_reverse]
    exact Poly.of_le (fun j => (List.take_sublist _ _).length_le) hl
  poly_auto

theorem binaryReadNat (hl : Poly s (fun j => (bs j).length) 1)
    (hv : Poly s (fun j => (Binary.readNat (bs j)).1) 1) :
    Poly s (fun j => (Uniform.binaryReadNat (I := I)).time (idx j) (bs j)) 3 := by
  have hb : Poly s (fun j => volume (bs j)) 1 := by poly_auto
  have hlead := binaryLeading s idx bs hl
  have hkl : Poly s (fun j => Binary.leading (bs j)) 1 := Poly.of_le (fun j => Binary.leading_le (bs j)) hl
  have htail : Poly s (fun j => ((bs j).drop (Binary.leading (bs j)+1)).length) 1 := by
    apply Poly.of_le _ hl
    intro j; exact (List.drop_sublist _ _).length_le
  have hbits : Poly s (fun j => (((bs j).drop (Binary.leading (bs j)+1)).take (Binary.leading (bs j))).length) 1 := by
    apply Poly.of_le _ htail
    intro j; exact (List.take_sublist _ _).length_le
  have ht := binaryTake s idx (fun j => (bs j).drop (Binary.leading (bs j)+1))
    (fun j => Binary.leading (bs j)) htail hkl
  change Poly s (fun j => Binary.value (((bs j).drop (Binary.leading (bs j)+1)).take (Binary.leading (bs j)))) 1 at hv
  have hval := binaryValue s idx
    (fun j => ((bs j).drop (Binary.leading (bs j)+1)).take (Binary.leading (bs j))) hbits hv
  poly_auto
end Costs
end ThreeMachine.StackCompiler
end

end OAI
