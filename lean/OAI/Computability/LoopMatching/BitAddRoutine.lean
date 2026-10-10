import OAI.Computability.LoopMatching.BitAdd

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.BitAdd
open BinaryMatching.StackCode

lemma boolList_code_length (l : List Bool) : (encode l).length = 3*l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [code_cons, pairBits_length, encode_bool, List.length_cons,
      List.length_nil, ih]
    omega

lemma state_code_length (s : State) :
    (encode s).length = 12*s.1.1.length + 6*s.1.2.length + 3*s.2.2.length + 6 := by
  simp only [encode_prod, pairBits_length, boolList_code_length, encode_bool,
    List.length_singleton]
  omega

@[fun_prop] theorem xor_poly : Poly (fun z : Bool × Bool => xor z.1 z.2) := by
  unfold xor
  fun_prop

@[fun_prop] theorem digit_poly : Poly (fun z : (Bool × Bool) × Bool => digit z.1.1 z.1.2 z.2) := by
  unfold digit
  fun_prop

@[fun_prop] theorem carry_poly : Poly (fun z : (Bool × Bool) × Bool => carry z.1.1 z.1.2 z.2) := by
  unfold carry
  fun_prop

@[fun_prop] theorem step_poly : Poly step := by
  have hi : Poly (fun z : State × Bool =>
      ((z.1.1.1.headD false, z.1.1.2.headD false), z.1.2.1)) := by fun_prop
  have hc : Poly (fun z : State × Bool =>
      carry (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1) :=
    Poly.comp _ _ carry_poly hi
  have hd : Poly (fun z : State × Bool =>
      digit (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1) :=
    Poly.comp _ _ digit_poly hi
  have ho : Poly (fun z : State × Bool =>
      z.1.2.2 ++ [digit (z.1.1.1.headD false) (z.1.1.2.headD false) z.1.2.1]) :=
    Poly.comp (fun p : List Bool × Bool => p.1 ++ [p.2]) _ (by fun_prop)
      (Poly.pair _ _ (by fun_prop) hd)
  unfold step
  exact Poly.pair _ _ (by fun_prop) (Poly.pair _ _ hc ho)

lemma step_growth (z : State × Bool) :
    (encode (step z)).length ≤ (encode z.1).length + 1*(2*(encode z.2).length+1) := by
  rw [state_code_length, state_code_length]
  simp only [step, encode_bool, List.length_singleton, List.length_append]
  have hx : z.1.1.1.tail.length ≤ z.1.1.1.length := by simp
  have hy : z.1.1.2.tail.length ≤ z.1.1.2.length := by simp
  omega

@[fun_prop] theorem run_poly : Poly (fun z : List Bool × State => run z.1 z.2) := by
  exact Poly.listFoldAdd step step_poly 1 step_growth

@[fun_prop] theorem initial_poly : Poly initial := by
  unfold initial
  fun_prop

@[fun_prop] theorem finish_poly : Poly finish := by
  unfold finish
  fun_prop

@[fun_prop] theorem add_poly : Poly add := by
  unfold add
  fun_prop

end LoopMatching.BitAdd

end OAI
