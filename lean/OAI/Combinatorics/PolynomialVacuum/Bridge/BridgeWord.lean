import OAI.Combinatorics.HoneycombCorridor.BridgeFiniteness

namespace OAI

namespace PolynomialVacuumBridge.Corridor

def shiftVertex (x y : ℤ) : Vertex → Vertex
  | .up i j => .up (i+x) (j+y)
  | .down i j => .down (i+x) (j+y)
def shiftGerm (x y : ℤ) (g : Germ) : Germ := (shiftVertex x y g.1,g.2)
@[simp] theorem shiftVertex_zero (v : Vertex) : shiftVertex 0 0 v=v := by cases v <;> simp [shiftVertex]
@[simp] theorem shiftGerm_zero (g : Germ) : shiftGerm 0 0 g=g := by simp [shiftGerm]
@[simp] theorem shiftVertex_add (x y a b : ℤ) (v : Vertex) :
    shiftVertex x y (shiftVertex a b v)=shiftVertex (x+a) (y+b) v := by
  cases v <;> simp [shiftVertex,add_comm,add_left_comm]
@[simp] theorem shiftGerm_add (x y a b : ℤ) (g : Germ) :
    shiftGerm x y (shiftGerm a b g)=shiftGerm (x+a) (y+b) g := by simp [shiftGerm]
theorem shiftVertex_injective (x y : ℤ) : Function.Injective (shiftVertex x y) := by
  intro v u h
  have := congrArg (shiftVertex (-x) (-y)) h
  simpa using this
@[simp] theorem layer_shift (x y : ℤ) (v : Vertex) : layer (shiftVertex x y v)=layer v+y := by
  cases v <;> rfl
@[simp] theorem shift_neighbor (x y : ℤ) (v : Vertex) (k : Fin 3) :
    shiftVertex x y (neighbor v k)=neighbor (shiftVertex x y v) k := by
  cases v <;> fin_cases k <;> simp [shiftVertex,neighbor] <;> omega
@[simp] theorem shift_advance (x y : ℤ) (g : Germ) (b : Bool) :
    shiftGerm x y (advance g b)=advance (shiftGerm x y g) b := by
  simp [shiftGerm,advance,outgoingSlot]
@[simp] theorem shift_terminal (x y : ℤ) (g : Germ) (w : List Bool) :
    shiftGerm x y (terminalGerm g w)=terminalGerm (shiftGerm x y g) w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [terminalGerm,← ih,← shift_advance]
@[simp] theorem shift_traced (x y : ℤ) (g : Germ) (w : List Bool) :
    (traced g w).map (shiftVertex x y)=traced (shiftGerm x y g) w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [traced,List.map_cons,ih,← shift_advance]; rfl

 

structure BridgeWord where
  word : List Bool
  height : ℕ
  endX : ℤ
  distinct : (traced bottomSource word).Nodup
  terminal : terminalGerm bottomSource word=(.up endX height,0)
  inStrip : ∀ v∈traced bottomSource word, 0≤layer v ∧ layer v<(height : ℤ)

namespace BridgeWord
@[ext] theorem ext {A B : BridgeWord} (h : A.word=B.word) : A=B := by
  have ht := A.terminal.symm.trans (h ▸ B.terminal)
  have hx : A.endX=B.endX := by simpa using congrArg (fun g : Germ => match g.1 with | .up i _ => i | .down i _ => i) ht
  have hh : A.height=B.height := by have := congrArg (fun g : Germ => layer g.1) ht; simpa [layer] using this
  cases A; cases B; cases h; cases hx; cases hh; rfl

def one : BridgeWord := ⟨[],0,0,by simp [traced],rfl,by simp [traced]⟩
instance : One BridgeWord := ⟨one⟩
@[simp] theorem word_one : (1 : BridgeWord).word=[] := rfl
@[simp] theorem height_one : (1 : BridgeWord).height=0 := rfl
@[simp] theorem endX_one : (1 : BridgeWord).endX=0 := rfl
@[simp] theorem word_eq_nil {A : BridgeWord} : A.word=[] ↔ A=1 := ⟨fun h => ext h,fun h => h ▸ rfl⟩
@[simp] theorem terminal_source (A : BridgeWord) :
    terminalGerm bottomSource A.word=shiftGerm A.endX A.height bottomSource := by
  simpa [shiftGerm,shiftVertex,bottomSource] using A.terminal

theorem positive_of_nonempty {A : BridgeWord} (h : A≠1) : 0<A.height := by
  have hw : A.word≠[] := fun hw => h (word_eq_nil.mp hw)
  obtain ⟨b,w,he⟩ := List.exists_cons_of_ne_nil hw
  have hs := A.inStrip bottomSource.1 (by simp [he,traced])
  norm_num [bottomSource,layer] at hs
  omega

def mul (A B : BridgeWord) : BridgeWord where
  word := A.word++B.word
  height := A.height+B.height
  endX := A.endX+B.endX
  distinct := by
    rw [traced_append,A.terminal_source,← shift_traced]
    apply List.nodup_append.mpr
    refine ⟨A.distinct,B.distinct.map (shiftVertex_injective _ _),?_⟩
    intro v hv u hu he
    obtain ⟨u',hu',rfl⟩ := List.mem_map.mp hu
    have ha := (A.inStrip v hv).2
    have hb := (B.inStrip u' hu').1
    rw [he,layer_shift] at ha
    omega
  terminal := by
    rw [terminalGerm_append,A.terminal_source,← shift_terminal,B.terminal]
    simp [shiftGerm,shiftVertex,Nat.cast_add,add_comm]
  inStrip := by
    intro v hv
    rw [traced_append,A.terminal_source,← shift_traced,List.mem_append] at hv
    rcases hv with hv | hv
    · have hv := A.inStrip v hv
      constructor <;> push_cast <;> omega
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
      have hu := B.inStrip u hu
      rw [layer_shift]
      constructor <;> push_cast <;> omega
instance : Mul BridgeWord := ⟨mul⟩
@[simp] theorem word_mul (A B : BridgeWord) : (A*B).word=A.word++B.word := rfl
@[simp] theorem height_mul (A B : BridgeWord) : (A*B).height=A.height+B.height := rfl
@[simp] theorem endX_mul (A B : BridgeWord) : (A*B).endX=A.endX+B.endX := rfl
instance : Monoid BridgeWord where
  one_mul A := ext (by simp)
  mul_one A := ext (by simp)
  mul_assoc A B C := ext (List.append_assoc _ _ _)

@[simp] theorem length_nonzero {A : BridgeWord} : A.word.length≠0 ↔ A≠1 := by simp

def IsPrimitive (A : BridgeWord) : Prop := A≠1 ∧ ∀ B C, A=B*C → B=1 ∨ C=1
end BridgeWord
end PolynomialVacuumBridge.Corridor

end OAI
