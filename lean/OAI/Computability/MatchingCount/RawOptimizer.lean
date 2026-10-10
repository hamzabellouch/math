import OAI.Computability.MatchingCount.ScaledBounds

namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Algorithm Finset StackCode
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

def value (p : Params) (a : Matrix ℤ) (r : Row) : ℤ :=
  upperSum p.n (fun i j => scaledPsi p (get a i j)+get p.beta i j*get a i j*p.pow)-
    (p.M:ℤ)*rowNumerator p.D a r*p.pow
lemma value_rep (G : Input) (a : Table G.n ℤ) (r : Affine G.n) :
    value (params G) (tableRep a) (rowRep r)=integralValue G a r := by
  unfold value integralValue
  rw [rowNumerator_rep]
  congr 1
  change upperSum G.n _=_
  apply upperSum_rep
  intro e
  rw [get_tableRep,get_beta,scaledPsi_rep]
  rfl

def gradient (p : Params) (a : Matrix ℤ) (r : Row) (i j : ℕ) : ℤ :=
  scaledSlope p (get a i j)+get p.beta i j-(p.M:ℤ)*get r.1 i j
lemma gradient_rep (G : Input) (a : Table G.n ℤ) (r : Affine G.n) (e : Pair G.n) :
    gradient (params G) (tableRep a) (rowRep r) e.val.1.val e.val.2.val=integralGradient G a r e := by
  unfold gradient integralGradient
  rw [get_tableRep,get_beta,get_rowRep,scaledSlope_rep]
  rfl

def update (p : Params) (a : Matrix ℤ) (r : Row) : Matrix ℤ :=
  matrix p.n (fun i j => if i < j then min (p.D:ℤ) (max 0 (get a i j+gradient p a r i j)) else 0)
lemma update_rep (G : Input) (a : Table G.n ℤ) (r : Affine G.n) :
    update (params G) (tableRep a) (rowRep r)=tableRep (integralUpdate G a r) := by
  change matrix G.n _=matrixRep _
  apply matrix_eq_rep
  intro i j
  change (if i.val<j.val then _ else 0)=(integralUpdate G a r)[i][j]
  by_cases h : i < j
  · simp [integralUpdate,toTable,tabulate,h,get_tableRep,
      gradient_rep G a r ⟨(i,j),h⟩,show (params G).D=D₀ G from rfl,entry]
  · simp [integralUpdate,toTable,tabulate,h]

def step (z : Params×IntState) : Params×IntState :=
  let r := selectedRow z.1.n z.1.D z.2.1
  let v := value z.1 z.2.1 r
  (z.1,(update z.1 z.2.1 r,some (z.2.2.elim v (max v))))

def initial (p : Params) : Params×IntState := (p,(matrix p.n (fun _ _ => 0),none))
lemma initial_rep (G : Input) : initial (params G)=(params G,stateRep (integralInitial G.n)) := by
  change (params G,(matrix G.n (fun _ _ => 0),none))=(params G,(tableRep (integralInitial G.n).numerators,none))
  apply congrArg (fun a : Matrix ℤ => (params G,(a,(none:Option ℤ))))
  apply matrix_eq_rep
  intro i j
  simp [integralInitial,tabulate]
lemma step_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) (s : IntegralState G.n) :
    step (params G,stateRep s)=(params G,stateRep (integralStep G s)) := by
  dsimp only [step]
  rw [show (stateRep s).1=tableRep s.numerators from rfl,
    show (params G).n=G.n from rfl,selectedRow_rep hn he,value_rep,update_rep]
  rfl
lemma step_iterate_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) (k : ℕ) :
    step^[k] (initial (params G))=(params G,stateRep (integralIterate G k)) := by
  induction k with
  | zero => exact initial_rep G
  | succ k ih => rw [Function.iterate_succ_apply',ih,step_rep G hn he]; rfl

lemma integralIterate_lower (G : Input) (t : ℕ) (i j : Fin G.n) (h : ¬i < j) :
    (integralIterate G t).numerators[i][j]=0 := by
  cases t with
  | zero => simp [integralIterate,integralInitial,tabulate]
  | succ t => simp [integralIterate,integralStep,integralUpdate,toTable,tabulate,h]
lemma integralIterate_all_abs (G : Input) (hn : 2≤G.n) (t : ℕ) (i j : Fin G.n) :
    ((integralIterate G t).numerators[i][j]).natAbs≤D₀ G := by
  by_cases hij : i < j
  · exact integralIterate_abs G hn t ⟨(i,j),hij⟩
  · rw [integralIterate_lower G t i j hij]
    exact Nat.zero_le _

def operandBound (p : Params) : ℕ := p.D*p.pow*(p.q*(p.k+p.L+1)+p.M*(p.q+1))
def budget (p : Params) : ℕ :=
  2*(encode p).length+2*(p.n*(2*(p.n*(2*(p.D+3)+1))+1))+(2*(operandBound p+3)+1)+2

lemma state_code_bound (G : Input) (hn : 2≤G.n) (t : ℕ) :
    (encode (params G,stateRep (integralIterate G t))).length≤budget (params G) := by
  have ht : (encode (tableRep (integralIterate G t).numerators)).length≤
      G.n*(2*(G.n*(2*(D₀ G+3)+1))+1) := by
    apply vectorRep_code_bound
    intro i
    apply vectorRep_code_bound
    intro j
    rw [code_int_length]
    exact Nat.add_le_add_right (integralIterate_all_abs G hn t i j) 3
  have hb : (encode (integralIterate G t).best).length≤2*(Algorithm.operandBound G+3)+1 := by
    cases h : (integralIterate G t).best with
    | none => simp only [code_option_none,List.length_nil]; omega
    | some v =>
      simp only [code_option_some,code_int_length]
      have hv := integralBest_abs G hn t v h
      omega
  simp only [code_pair_length,stateRep] at ht ⊢
  change 2*(encode (params G)).length+
    (2*(encode (tableRep (integralIterate G t).numerators)).length+
     (encode (integralIterate G t).best).length+1)+1≤_
  change _≤2*(encode (params G)).length+2*(G.n*(2*(G.n*(2*(D₀ G+3)+1))+1))+
    (2*(Algorithm.operandBound G+3)+1)+2
  omega

def run (p : Params) : IntState :=
  (((guardedStep step)^[p.q*p.D] (budget p,initial p)).2).2
lemma run_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) :
    run (params G)=stateRep (integralIterate G (q G.n*D₀ G)) := by
  unfold run
  rw [guardedStep_eq step (budget (params G)) (initial (params G)) _ (by
    intro j hj
    rw [step_iterate_rep G hn he]
    exact state_code_bound G hn j),step_iterate_rep G hn he]
  rfl

def result (p : Params) : ℤ := (run p).2.getD 0/(p.D*p.pow:ℕ)
lemma result_rep (G : Input) (hn : 2≤G.n) (he : Even G.n) : result (params G)=integralR G := by
  unfold result integralR
  rw [run_rep G hn he]
  rfl
end BinaryMatching.Raw.Optimize
end

end OAI
