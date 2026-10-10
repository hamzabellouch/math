import OAI.Computability.Scheduling.FiniteRoutines

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18

section

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i × γ i → β i}

theorem time_mapBody (R : Uniform f) (i : I) (a : α i) (e : γ i) (ys : List (β i)) :
    (mapBody R).time i (a,(e,ys)) ≤ R.time i (a,e)+
      1000*(volume a+volume e+volume ys+volume (f i (a,e))+1) := by
  simp only [mapBody,time_pair,time_comp,time_fst,time_snd,time_cons,volume_pair,volume_cons,Function.comp_apply]
  omega

theorem foldTime_mapBody (R : Uniform f) (i : I) (e : γ i) (T : ℕ)
    (xs : List (α i)) (ys : List (β i))
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T) :
    Realizer.foldTime ((mapBody R).specialize i) (e,ys) xs ≤
      xs.length*(T+4000*(volume xs+volume e+volume (xs.map (fun a => f i (a,e)))+volume ys+1))+1 := by
  induction xs generalizing ys with
  | nil => simp only [Realizer.foldTime,List.length_nil,Nat.zero_mul,Nat.zero_add]; rfl
  | cons a xs ih =>
    have hta := hT a (by simp)
    have ht := ih (f i (a,e) :: ys) (fun a ha => hT a (by simp [ha]))
    have hb := time_mapBody R i a e ys
    simp only [Realizer.foldTime]
    change (mapBody R).time i (a,(e,ys))+
      Realizer.foldTime ((mapBody R).specialize i) (e,f i (a,e) :: ys) xs+
      20*(volume (a :: xs)+volume (e,ys)+volume (e,f i (a,e) :: ys)+1) ≤ _
    simp only [volume_pair,volume_cons,List.length_cons,List.map_cons] at ht hb ⊢
    nlinarith [volume_pos a,volume_pos e,volume_pos ys,volume_pos xs,volume_pos (f i (a,e))]

theorem time_map (R : Uniform f) (i : I) (xs : List (α i)) (e : γ i) (T : ℕ)
    (hT : ∀ a ∈ xs, R.time i (a,e) ≤ T) :
    R.map.time i (xs,e) ≤
      30000*(xs.length+1)*(T+volume xs+volume e+volume (xs.map (fun a => f i (a,e)))+1) := by
  have hf := foldTime_mapBody R i e T xs [] hT
  have hr := time_reverse i ((xs.map (fun a => f i (a,e))).reverse)
  simp only [volume_nil] at hf
  simp only [List.length_reverse,List.length_map,volume_reverse] at hr
  simp only [map,time_congr,time_comp,time_pair,time_fst,time_snd,time_nil,time_fold,
    Function.comp_apply,Realizer.map_fold_eq,List.append_nil,volume_pair,volume_nil,volume_reverse]
  nlinarith [volume_pos xs,volume_pos e,volume_pos (xs.map (fun a => f i (a,e)))]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler

def lookupList {K : Type u5} {V : Type u6} [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (a,b) :: xs, k => if a = k then some b else lookupList xs k

namespace Uniform
variable {I : Type u7} {α : I → Type u8} {β : I → Type u9} {γ : I → Type u10}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

def mapList {f : ∀ i, α i → β i} (R : Uniform f) :
    Uniform (fun i (xs : List (α i)) => xs.map (f i)) :=
  ((id.pair unit).comp (fst.comp R).map).congr (fun _ _ => rfl)

def mapOption {f : ∀ i, α i → β i} (R : Uniform f) :
    Uniform (fun i (x : Option (α i)) => x.map (f i)) :=
  ((id.pair unit).comp (fst.comp R).optionMap).congr (fun _ _ => rfl)

def bindOption {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : Option (α i) × γ i) => x.1.bind (fun a => f i (a,x.2))) :=
  (((optionToList.onFst.comp R.filterMap).comp head?)).congr (fun _ x => by
    rcases x with ⟨o,e⟩; cases o with
    | none => rfl
    | some a => simp only [Function.comp_apply,Option.toList_some,List.filterMap_cons,List.filterMap_nil,Option.bind_some]; cases f _ (a,e) <;> rfl)

def optionOrElse : Uniform (fun (i : I) (x : Option (α i) × Option (α i)) => x.1.or x.2) :=
  (fst.comp optionIsSome).ite fst snd |>.congr (fun _ x => by
    rcases x with ⟨o,e⟩; cases o <;> rfl)

def lookup [∀ i, DecidableEq (α i)]
    (E : Uniform (fun i (x : α i × α i) => decide (x.1 = x.2))) :
    Uniform (fun i (x : List (α i × β i) × α i) => lookupList x.1 x.2) :=
  ((((fst.comp fst).pair snd).comp E).find?.comp snd.mapOption).congr (fun i x => by
    dsimp only [Function.comp_apply]
    induction x.1 with
    | nil => rfl
    | cons a xs ih =>
      by_cases ha : a.1 = x.2 <;> simp [lookupList,ha,ih])

end Uniform
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u11} {J : Type u12} {α : I → Type u13} {β : I → Type u14} {γ : I → Type u15}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → β i}

def reindex (R : Uniform f) (φ : J → I) : Uniform (fun j => f (φ j)) where
  transform := R.transform
  charge := R.charge
  routine := R.routine
  correct j x := R.correct (φ j) x

def finValue (d : I → ℕ) : Uniform (fun i (x : Fin (d i)) => x.val) :=
  reinterpret _ (fun _ _ => rfl)

def cardinalValue (d : I → ℕ) : Uniform (fun i (_ : Cardinal (d i)) => d i) :=
  reinterpret _ (fun _ _ => rfl)

def universeListAny (d : I → ℕ) : Uniform (fun i (_ : Universe (d i)) => List.finRange (d i)) :=
  reinterpret _ (fun _ _ => rfl)

def makeUniverseAny (d : I → ℕ) : Uniform (fun i (_ : Cardinal (d i)) => (Universe.mk () : Universe (d i))) :=
  makeUniverse.reindex d

def functionListAny (d : I → ℕ) : Uniform (fun i (f : Fin (d i) → α i) => List.ofFn f) :=
  reinterpret _ (fun _ _ => rfl)

def functionGetOptionAny (d : I → ℕ) :
    Uniform (fun i (x : (Fin (d i) → α i) × Fin (d i)) => Option.some (x.1 x.2)) :=
  (((fst.comp (functionListAny d)).pair (snd.comp (finValue d))).comp getElem?).congr (fun _ x => by
    simp only [Function.comp_apply,List.getElem?_ofFn,dite_eq_left x.2.isLt])

def functionGetAny (d : I → ℕ) : Uniform (fun i (x : (Fin (d i) → α i) × Fin (d i)) => x.1 x.2) where
  transform := Data.head ∘ (functionGetOptionAny (α := α) d).transform
  charge := _
  routine := (functionGetOptionAny (α := α) d).routine.comp (Routine.select true)
  correct i x := by
    simp only [Function.comp_apply,(functionGetOptionAny (α := α) d).correct,enc_some,Data.head]

def vectorMapAny (d : I → ℕ) {f : ∀ i, Fin (d i) × α i → β i} (R : Uniform f) :
    Uniform (fun i (x : Universe (d i) × α i) => fun v => f i (v,x.2)) where
  transform := ((universeListAny d).onFst.comp R.map).transform
  charge := ((universeListAny d).onFst.comp R.map).charge
  routine := ((universeListAny d).onFst.comp R.map).routine
  correct i x := by
    rw [((universeListAny d).onFst.comp R.map).correct]
    simp only [Function.comp_apply,enc_function,List.ofFn_eq_map]

def recode {H : Type u16} {δ : H → Type u17} {ε : H → Type u18} [∀ h, Coding (δ h)] [∀ h, Coding (ε h)]
    {g : ∀ h, δ h → ε h} (R : Uniform g) (f : ∀ i, α i → β i)
    (h : ∀ i x, ∃ j y, enc y = enc x ∧ enc (g j y) = enc (f i x)) : Uniform f where
  transform := R.transform
  charge := R.charge
  routine := R.routine
  correct i x := by
    obtain ⟨j,y,hin,hout⟩ := h i x
    rw [← hin,R.correct,hout]

def cardinalMap (d : I → ℕ) {g : ℕ → ℕ} (R : Realizer g) :
    Uniform (fun i (_ : Cardinal (d i)) => (Cardinal.mk () : Cardinal (g (d i)))) where
  transform := R.transform
  charge := R.charge
  routine := R.routine
  correct i _ := R.correct (d i)

end ThreeMachine.StackCompiler.Uniform

end

end OAI
