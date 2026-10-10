import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.DeriveFintype

namespace OAI

namespace DepthThreeLowerBound

abbrev TapeRegister := Fin 32

namespace TapeRegister

abbrev input : TapeRegister := 0
abbrev length : TapeRegister := 1
abbrev dataLength : TapeRegister := 2
abbrev ringDegree : TapeRegister := 3
abbrev coeffCount : TapeRegister := 4
abbrev candidate : TapeRegister := 5
abbrev powerTarget : TapeRegister := 6
abbrev powerScratch : TapeRegister := 7
abbrev requiredLength : TapeRegister := 8
abbrev loop0 : TapeRegister := 9
abbrev loop1 : TapeRegister := 10
abbrev loop2 : TapeRegister := 11
abbrev loop3 : TapeRegister := 12
abbrev loop4 : TapeRegister := 13
abbrev loop5 : TapeRegister := 14
abbrev dataBits : TapeRegister := 15
abbrev keyBits : TapeRegister := 16
abbrev polyBits : TapeRegister := 17
abbrev coeffBits : TapeRegister := 18
abbrev hashBits : TapeRegister := 19
abbrev accumBits : TapeRegister := 20
abbrev productBits : TapeRegister := 21
abbrev indexA : TapeRegister := 22
abbrev indexB : TapeRegister := 23
abbrev indexC : TapeRegister := 24
abbrev scratchA : TapeRegister := 25
abbrev scratchB : TapeRegister := 26
abbrev scratchC : TapeRegister := 27
abbrev savedCount : TapeRegister := 28
abbrev temp0 : TapeRegister := 29
abbrev temp1 : TapeRegister := 30
abbrev temp2 : TapeRegister := 31

end TapeRegister

inductive TapeAtom where
  | blank
  | home
  | delimiter (r : TapeRegister)
  | bit (b : Bool)
  | endMark
  deriving DecidableEq, Fintype, Inhabited

abbrev TapeMark := Fin 4

abbrev TapeSymbol := TapeAtom × (TapeMark → Bool)

def cleanAtom (a : TapeAtom) : TapeSymbol := (a, fun _ => false)

def blankSymbol : TapeSymbol := cleanAtom .blank

def rawInputSymbol (b : Bool) : TapeSymbol := cleanAtom (.bit b)

@[simp] theorem cleanAtom_atom (a : TapeAtom) : (cleanAtom a).1 = a := rfl

@[simp] theorem cleanAtom_mark (a : TapeAtom) (m : TapeMark) :
    (cleanAtom a).2 m = false := rfl

@[simp] theorem default_tapeSymbol : (default : TapeSymbol) = blankSymbol := rfl

theorem cleanAtom_injective : Function.Injective cleanAtom := by
  intro a b h
  exact congrArg Prod.fst h

theorem rawInputSymbol_injective : Function.Injective rawInputSymbol := by
  intro a b h
  have hab : TapeAtom.bit a = TapeAtom.bit b := congrArg Prod.fst h
  cases hab
  rfl

@[simp] theorem rawInputSymbol_ne_blank (b : Bool) : rawInputSymbol b ≠ blankSymbol := by
  intro h
  have hab : TapeAtom.bit b = TapeAtom.blank := congrArg Prod.fst h
  cases hab

abbrev TapeStore := TapeRegister → List Bool

def tapeRegisters : List TapeRegister := List.ofFn id

@[simp] theorem tapeRegisters_length : tapeRegisters.length = 32 := by
  simp [tapeRegisters]

@[simp] theorem mem_tapeRegisters (r : TapeRegister) : r ∈ tapeRegisters := by
  change r ∈ List.ofFn (fun i : TapeRegister => i)
  exact List.mem_ofFn.mpr ⟨r, rfl⟩

theorem tapeRegisters_nodup : tapeRegisters.Nodup := by
  exact List.nodup_ofFn_ofInjective (fun _ _ h => h)

def encodeInput (bits : List Bool) : List TapeSymbol := bits.map rawInputSymbol

@[simp] theorem encodeInput_length (bits : List Bool) :
    (encodeInput bits).length = bits.length := by
  simp [encodeInput]

def encodeBlock (σ : TapeStore) (r : TapeRegister) : List TapeSymbol :=
  cleanAtom (.delimiter r) :: encodeInput (σ r)

def encodeStore (σ : TapeStore) : List TapeSymbol :=
  cleanAtom .home :: (tapeRegisters.flatMap (encodeBlock σ) ++ [cleanAtom .endMark])

@[simp] theorem encodeBlock_length (σ : TapeStore) (r : TapeRegister) :
    (encodeBlock σ r).length = (σ r).length + 1 := by
  simp [encodeBlock]

theorem encodeBlocks_length (σ : TapeStore) (rs : List TapeRegister) :
    (rs.flatMap (encodeBlock σ)).length =
      rs.length + (rs.map (fun r => (σ r).length)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
      simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem encodeStore_length (σ : TapeStore) :
    (encodeStore σ).length =
      34 + (tapeRegisters.map (fun r => (σ r).length)).sum := by
  simp [encodeStore, Nat.add_comm]
  simp only [← Nat.add_assoc]

@[simp] theorem encodeStore_head? (σ : TapeStore) :
    (encodeStore σ).head? = some (cleanAtom .home) := rfl

@[simp] theorem encodeStore_ne_nil (σ : TapeStore) : encodeStore σ ≠ [] := by
  simp [encodeStore]

theorem encodeInput_symbols {bits : List Bool} {s : TapeSymbol}
    (hs : s ∈ encodeInput bits) :
    (∃ b : Bool, s.1 = .bit b) ∧ ∀ m, s.2 m = false := by
  rcases List.mem_map.mp hs with ⟨b, _, rfl⟩
  exact ⟨⟨b, rfl⟩, fun _ => rfl⟩

theorem encodeBlock_symbols {σ : TapeStore} {r : TapeRegister} {s : TapeSymbol}
    (hs : s ∈ encodeBlock σ r) :
    s.1 ≠ .blank ∧ s.1 ≠ .home ∧ s.1 ≠ .endMark ∧ ∀ m, s.2 m = false := by
  rcases List.mem_cons.mp hs with hs | hs
  · subst s
    simp [cleanAtom]
  · obtain ⟨⟨b, hb⟩, hm⟩ := encodeInput_symbols hs
    exact ⟨by simp [hb], by simp [hb], by simp [hb], hm⟩

theorem encodeBlocks_symbols {σ : TapeStore} {rs : List TapeRegister} {s : TapeSymbol}
    (hs : s ∈ rs.flatMap (encodeBlock σ)) :
    s.1 ≠ .blank ∧ s.1 ≠ .home ∧ s.1 ≠ .endMark ∧ ∀ m, s.2 m = false := by
  rcases List.mem_flatMap.mp hs with ⟨r, _, hr⟩
  exact encodeBlock_symbols hr

theorem encodeStore_no_blank {σ : TapeStore} {s : TapeSymbol}
    (hs : s ∈ encodeStore σ) : s.1 ≠ .blank := by
  rcases List.mem_cons.mp hs with hs | hs
  · subst s
    simp [cleanAtom]
  · rcases List.mem_append.mp hs with hs | hs
    · exact (encodeBlocks_symbols hs).1
    · have hs' : s = cleanAtom .endMark := List.mem_singleton.mp hs
      subst s
      simp [cleanAtom]

theorem encodeStore_clean {σ : TapeStore} {s : TapeSymbol}
    (hs : s ∈ encodeStore σ) (m : TapeMark) : s.2 m = false := by
  rcases List.mem_cons.mp hs with hs | hs
  · subst s
    rfl
  · rcases List.mem_append.mp hs with hs | hs
    · exact (encodeBlocks_symbols hs).2.2.2 m
    · have hs' : s = cleanAtom .endMark := List.mem_singleton.mp hs
      subst s
      rfl

theorem encodeStore_tail_no_home {σ : TapeStore} {s : TapeSymbol}
    (hs : s ∈ (encodeStore σ).tail) : s.1 ≠ .home := by
  change s ∈ tapeRegisters.flatMap (encodeBlock σ) ++ [cleanAtom .endMark] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact (encodeBlocks_symbols hs).2.1
  · have hs' : s = cleanAtom .endMark := List.mem_singleton.mp hs
    subst s
    simp [cleanAtom]

end DepthThreeLowerBound

end OAI
