import OAI.Computability.MatchingCount.OptionCases

namespace OAI

section

namespace BinaryMatching.Raw
open StackCode Polynomial
abbrev SearchContext := ℕ×(Matrix ℕ×(Matrix ℤ×ℕ))
abbrev SearchState := SearchContext×Paths

def searchStep (s : SearchState) : SearchState :=
  (s.1,pathStep s.1.1 s.1.2.1 s.1.2.2.1 s.2)
def searchInitial (z : SearchContext×ℕ) : SearchState :=
  (z.1,initial z.1.1 z.1.2.2.2)

lemma searchStep_iterate (z : SearchContext×ℕ) (j : ℕ) :
    searchStep^[j] (searchInitial z)=(z.1,search z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply',ih,searchStep,search]

namespace Compiler
open StackCode.Poly

@[fun_prop] theorem residual_poly :
    Poly (fun z : (Matrix ℕ×Matrix ℤ)×(ℕ×ℕ) => residual z.1.1 z.1.2 z.2.1 z.2.2) := by
  unfold residual
  fun_prop

@[fun_prop] theorem initial_poly : Poly (fun z : ℕ×ℕ => initial z.1 z.2) := by
  unfold initial
  apply Poly.rawTab Prod.fst (fun z : (ℕ×ℕ)×ℕ => if z.2=z.1.2 then Option.some [z.1.2] else none)
  · fun_prop
  · have h : Poly (fun z : (ℕ×ℕ)×ℕ => if decide (z.2=z.1.2) then Option.some [z.1.2] else none) := by fun_prop
    exact h.congr (fun z => by simp)

@[fun_prop] theorem predecessor_poly :
    Poly (fun z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ =>
      predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2) := by
  unfold predecessor
  apply Poly.findWith (fun z => List.range z.1.1.1)
    (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ =>
      residual z.1.1.1.2.1 z.1.1.1.2.2 z.2 z.1.2 && (nth z.1.1.2 z.2).isSome)
  · fun_prop
  · have hr := Poly.comp _ (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ =>
        ((z.1.1.1.2.1,z.1.1.1.2.2),(z.2,z.1.2))) residual_poly (by fun_prop)
    have hs : Poly (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ =>
        (nth z.1.1.2 z.2).isSome) := by fun_prop
    exact Poly.comp _ _ Poly.boolAnd (Poly.pair _ _ hr hs)

def pathEntry (z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ) : Option (List ℕ) :=
  match nth z.1.2 z.2 with
  | Option.some l => Option.some l
  | none => match predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2 with
    | none => none
    | Option.some u => (nth z.1.2 u).map (fun l => z.2::l)

@[fun_prop] theorem pathEntry_poly : Poly pathEntry := by
  have h := Poly.optionCasesWith
    (fun z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ => nth z.1.2 z.2)
    (fun z => match predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2 with
      | none => none
      | Option.some u => (nth z.1.2 u).map (fun l => z.2::l))
    (fun z => Option.some z.2)
    (by fun_prop)
    (by
      have hi := Poly.optionCasesWith
        (fun z : ((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ => predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)
        (fun _ => (none:Option (List ℕ)))
        (fun z => (nth z.1.1.2 z.2).map (fun l => z.1.2::l))
        predecessor_poly (by fun_prop)
        (Poly.optionMapWith (fun z : (((ℕ×(Matrix ℕ×Matrix ℤ))×Paths)×ℕ)×ℕ => nth z.1.1.2 z.2)
          (fun z => z.1.1.2::z.2) (by fun_prop) (by fun_prop))
      exact hi.congr (fun z => by cases predecessor z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2 <;> rfl))
    (by fun_prop)
  exact h.congr (fun z => by unfold pathEntry; cases nth z.1.2 z.2 <;> rfl)

@[fun_prop] theorem pathStep_poly :
    Poly (fun z : (ℕ×(Matrix ℕ×Matrix ℤ))×Paths => pathStep z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  exact Poly.rawTab (fun z => z.1.1) pathEntry (by fun_prop) pathEntry_poly

@[fun_prop] theorem searchStep_poly : Poly searchStep := by
  unfold searchStep
  apply Poly.pair
  · fun_prop
  · exact Poly.comp _ (fun s : SearchState => ((s.1.1,(s.1.2.1,s.1.2.2.1)),s.2))
      pathStep_poly (by fun_prop)

@[fun_prop] theorem searchInitial_poly : Poly searchInitial := by
  unfold searchInitial
  apply Poly.pair
  · fun_prop
  · exact Poly.comp _ (fun z : SearchContext×ℕ => (z.1.1,z.1.2.2.2)) initial_poly (by fun_prop)

@[fun_prop] theorem search_poly : Poly (fun z : SearchContext×ℕ =>
    search z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hi := Poly.iterateFrom searchStep searchStep_poly Prod.snd searchInitial (by fun_prop)
    searchInitial_poly (100*(X+1)^3) (by
      intro z j hj
      rw [searchStep_iterate]
      let N := (encode (z.2,searchInitial z)).length
      have hctx : (encode z.1).length≤N := by
        simp only [N,searchInitial,code_pair_length,code_nat_length]; omega
      have hn : z.1.1≤N := by
        have := (pair_left_le z.1).trans hctx
        simpa only [code_nat_length] using this
      have ha : z.1.2.2.2≤N := by
        have := (pair_right_le z.1.2.2).trans ((pair_right_le z.1.2).trans ((pair_right_le z.1).trans hctx))
        simpa only [code_nat_length] using this
      have hk : j≤N := by
        simp only [N,code_pair_length,code_nat_length]; omega
      have hb := search_code_bound z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j
      have hm : z.1.1*(2*(4*z.1.2.2.2+3+j*(4*z.1.1+2))+1)≤
          N*(2*(4*N+3+N*(4*N+2))+1) := by gcongr
      simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      change (encode (z.1,search z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 j)).length≤100*(N+1)^3
      rw [code_pair_length]
      have hbb := hb.trans hm
      nlinarith)
  have h := Poly.second _ hi
  exact h.congr (fun z => by rw [searchStep_iterate])

end Compiler
end BinaryMatching.Raw
end

end OAI
