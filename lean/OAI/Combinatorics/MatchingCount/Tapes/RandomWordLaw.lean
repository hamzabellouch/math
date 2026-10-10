import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.RandomWord

namespace OAI

namespace MatchingFPRAS.RandomWord
open Turing BinaryArithmetic

def splitBits (m n : ℕ) : (Fin (m+n) → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)
def gridBits (m n : ℕ) : (Fin (m*n) → Bool) ≃ (Fin m → Fin n → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)
def wordTapeEquiv (m : ℕ) : (Fin (m*2+(m+3)) → Bool) ≃
    ((Fin m → Bool×Bool) × (Fin (m+3) → Bool)) :=
  (splitBits (m*2) (m+3)).trans (Equiv.prodCongr
    ((gridBits m 2).trans (Equiv.piCongrRight fun _=>finTwoArrowEquiv Bool)) (Equiv.refl _))
lemma gridBits_apply (m n : ℕ) (b : Fin (m*n) → Bool) (i : Fin m) (j : Fin n) :
    gridBits m n b i j=b (finProdFinEquiv (i,j)) := rfl
lemma splitBits_symm (m n : ℕ) (x : Fin m → Bool) (y : Fin n → Bool) :
    (splitBits m n).symm (x,y)=Fin.append x y := by
  ext i
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;> simp [splitBits,Fin.append,finSumFinEquiv]
lemma wordTape_list (m : ℕ) (x : Fin m → Bool×Bool) (y : Fin (m+3) → Bool) :
    List.ofFn ((wordTapeEquiv m).symm (x,y))=pairCoins (List.ofFn x)++List.ofFn y := by
  let rows : Fin m → Fin 2 → Bool:=fun i=>![ (x i).1,(x i).2 ]
  let b : Fin (m*2) → Bool:=(gridBits m 2).symm rows
  have hb (i : Fin m) (j : Fin 2) : b (finProdFinEquiv (i,j))=rows i j := by
    exact congrFun (congrFun ((gridBits m 2).apply_symm_apply rows) i) j
  have he : (wordTapeEquiv m).symm (x,y)=Fin.append b y := splitBits_symm _ _ b y
  rw [he,List.ofFn_fin_append]
  congr 1
  rw [List.ofFn_mul]
  have hi (i : Fin m) : (List.ofFn fun j : Fin 2=>b ⟨i*2+j,by omega⟩)=[(x i).1,(x i).2] := by
    have he' : (fun j : Fin 2=>b ⟨i*2+j,by omega⟩)=rows i := by
      funext j
      have hc : finProdFinEquiv (i,j)=(⟨i*2+j,by omega⟩ : Fin (m*2)) := by
        apply Fin.ext
        change j.val+2*i.val=i.val*2+j.val
        omega
      exact hc ▸ hb i j
    rw [he']
    simp [rows,List.ofFn_succ]
  simp_rw [hi]
  simp [pairCoins,List.map_ofFn,List.flatMap,Function.comp_def]
lemma wordTape_run (m : ℕ) (x : Fin m → Bool×Bool) (y : Fin (m+3) → Bool) :
    MatchingFPRAS.run machine (List.replicate m 1++[3]) ((wordTapeEquiv m).symm (x,y))=
      cfg none [] (drawnWord (List.ofFn x)++[3]) := by
  change execute (List.ofFn ((wordTapeEquiv m).symm (x,y)))
    (cfg (some 0) [] (List.replicate m 1++[3]))=_
  rw [wordTape_list]
  convert execute_word (List.ofFn x) (List.ofFn y) (by simp) using 1
  simp

theorem run_word (m : ℕ) (bits : Fin (m*2+(m+3)) → Bool) :
    MatchingFPRAS.run machine (List.replicate m 1++[3]) bits=
      cfg none [] (drawnWord (List.ofFn (wordTapeEquiv m bits).1)++[3]) := by
  have he:=wordTape_run m (wordTapeEquiv m bits).1 (wordTapeEquiv m bits).2
  simpa only [Prod.mk.eta,Equiv.symm_apply_apply] using he

def outputCoins (m : ℕ) (bits : Fin (m*2+(m+3)) → Bool) : Fin m → Bool :=
  fun i=>(wordTapeEquiv m bits).1 i |>.1

def outputSplit (m : ℕ) : (Fin (m*2+(m+3)) → Bool) ≃
    ((Fin m → Bool) × ((Fin m → Bool) × (Fin (m+3) → Bool))) :=
  (wordTapeEquiv m).trans ((Equiv.prodCongr (Equiv.arrowProdEquivProdArrow _ _ _) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _))
lemma outputSplit_fst (m : ℕ) (bits : Fin (m*2+(m+3)) → Bool) :
    (outputSplit m bits).1=outputCoins m bits := rfl

theorem outputCoins_fiber (m : ℕ) (x : Fin m → Bool) :
    (Finset.univ.filter (fun b=>outputCoins m b=x)).card=2^(2*m+3) := by
  classical
  let e : ({b : Fin (m*2+(m+3)) → Bool // outputCoins m b=x}) ≃
      ((Fin m → Bool) × (Fin (m+3) → Bool)) := {
    toFun := fun b=>(outputSplit m b.1).2
    invFun := fun y=>⟨(outputSplit m).symm (x,y),by
      change (outputSplit m ((outputSplit m).symm (x,y))).1=x
      rw [Equiv.apply_symm_apply]⟩
    left_inv b := by
      apply Subtype.ext
      apply (outputSplit m).injective
      rw [Equiv.apply_symm_apply]
      exact Prod.ext b.property.symm rfl
    right_inv y := by change (outputSplit m ((outputSplit m).symm (x,y))).2=y; rw [Equiv.apply_symm_apply] }
  rw [←Fintype.card_subtype]
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,←pow_add]
  congr 1
  omega
end MatchingFPRAS.RandomWord

end OAI
