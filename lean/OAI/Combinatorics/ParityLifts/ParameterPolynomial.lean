import OAI.Combinatorics.ParityLifts.UniformBasics

namespace OAI

namespace ParityWL.Complexity

/-- A single finite program, polynomial on each fixed parameter fibre. The
parameter is genuine input data, not an infinite family of finite controls. -/
structure ParamPolyProgram (ρ α β : Type) [TreeCodec ρ] [TreeCodec α] [TreeCodec β]
    (f : ρ → α → β) where
  program : TreeProgram (ρ × α) β (fun x => f x.1 x.2)
  coefficient : ρ → ℕ
  degree : ρ → ℕ
  bound : ∀ r x, program.time (r,x) ≤ coefficient r*((treeEncode (r,x)).size+1)^(degree r)

def ParamPolyProgram.ofPoly {ρ α β : Type} [TreeCodec ρ] [TreeCodec α] [TreeCodec β]
    {f : ρ → α → β} (P : PolyProgram (ρ × α) β (fun x => f x.1 x.2)) : ParamPolyProgram ρ α β f where
  program := P.program
  coefficient := fun _ => P.coefficient
  degree := fun _ => P.degree
  bound := fun r x => P.bound (r,x)

def ParamPolyProgram.pair {ρ α β γ : Type} [TreeCodec ρ] [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : ρ → α → β} {g : ρ → α → γ} (P : ParamPolyProgram ρ α β f) (Q : ParamPolyProgram ρ α γ g) :
    ParamPolyProgram ρ α (β × γ) (fun r x => (f r x,g r x)) where
  program := P.program.pair Q.program
  coefficient := fun r => P.coefficient r+Q.coefficient r+1
  degree := fun r => P.degree r+Q.degree r
  bound := by
    intro r x
    exact (Nat.add_le_add_right (Nat.add_le_add (P.bound r x) (Q.bound r x)) 1).trans
      (nat_poly_add _ _ _ _ _ (by omega))

def ParamPolyProgram.comp {ρ α β γ : Type} [TreeCodec ρ] [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : ρ → α → β} {g : ρ → β → γ} (P : ParamPolyProgram ρ α β f) (Q : ParamPolyProgram ρ β γ g) :
    ParamPolyProgram ρ α γ (fun r x => g r (f r x)) where
  program := ((TreeProgram.fst ρ α).pair P.program).comp Q.program
  coefficient := fun r => 2*P.coefficient r+Q.coefficient r*(2*(P.coefficient r+1))^(Q.degree r)+2
  degree := fun r => P.degree r+P.degree r*Q.degree r
  bound := by
    intro r x
    let X := (treeEncode (r,x)).size+1
    have hX : 1≤X := by dsimp [X]; omega
    let A := P.coefficient r
    let a := P.degree r
    let B := Q.coefficient r
    let b := Q.degree r
    have hp : P.program.time (r,x)≤A*X^a := P.bound r x
    have hs := (P.program.run (r,x)).bounds.1
    have ho := (P.program.run (r,x)).bounds.2.1
    have hr : (treeEncode r).size≤(treeEncode (r,x)).size := by simp [DataTree.size]; omega
    have hi : (treeEncode (r,f r x)).size+1≤(2*(A+1))*X^a := by
      simp only [treeEncode_pair,DataTree.size]
      have h1 := Nat.one_le_pow a X hX
      change (treeEncode (f r x)).size≤P.program.time (r,x) at ho
      nlinarith
    have hq : Q.program.time (r,f r x)≤B*(2*(A+1))^b*X^(a*b) := by
      calc
        _ ≤ B*((treeEncode (r,f r x)).size+1)^b := Q.bound r _
        _ ≤ B*((2*(A+1))*X^a)^b := by gcongr
        _ = _ := by rw [mul_pow,←pow_mul]; ring
    have h0 : (treeEncode (r,x)).size+P.program.time (r,x)+1≤(2*A+1)*X^a := by
      have h1 := Nat.one_le_pow a X hX
      nlinarith
    have hn := nat_poly_add X (2*A+1) (B*(2*(A+1))^b) a (a*b) hX
    change (treeEncode (r,x)).size+P.program.time (r,x)+1+Q.program.time (r,f r x)+1≤_
    dsimp only [A,a,B,b,X] at h0 hq hn
    nlinarith only [(Nat.add_le_add_right (Nat.add_le_add h0 hq) 1).trans hn]

lemma TreeProgram.fixed_fold_polynomial {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α × β → β} (P : PolyProgram (α × β) β f) (n : ℕ) :
    ∃ C d : ℕ, ∀ (xs : List α) (b : β), xs.length≤n →
      P.program.foldWork xs b ≤ C*((treeEncode (xs,b)).size+1)^d := by
  induction n with
  | zero =>
    refine ⟨1,1,?_⟩
    intro xs b hn
    have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    simp only [TreeProgram.foldWork,pow_one,one_mul]
    omega
  | succ n ih =>
    obtain ⟨C,d,ih⟩ := ih
    let A := P.coefficient
    let a := P.degree
    refine ⟨A+12+C*(A+2)^d,(a+1)*(d+1),?_⟩
    intro xs b hn
    let X := (treeEncode (xs,b)).size+1
    have hX : 1≤X := by dsimp [X]; omega
    have hpow : X≤X^(a+1) := by
      simpa using Nat.pow_le_pow_right hX (show 1≤a+1 by omega)
    have hpow' : X≤X^((a+1)*(d+1)) := by
      simpa using Nat.pow_le_pow_right hX (show 1≤(a+1)*(d+1) by nlinarith)
    cases xs with
    | nil =>
      simp only [TreeProgram.foldWork]
      dsimp only [X] at hpow'
      exact (by omega : (treeEncode (([] : List α),b)).size≤((treeEncode (([] : List α),b)).size+1)^((a+1)*(d+1))).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    | cons u us =>
      have hup : (treeEncode (u,b)).size≤(treeEncode (u::us,b)).size := by simp [DataTree.size]; omega
      have hp : P.program.time (u,b)≤A*X^a := by
        exact (P.bound _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hup 1) _))
      have ho := (P.program.run (u,b)).bounds.2.1
      change (treeEncode (f (u,b))).size≤P.program.time (u,b) at ho
      have htail : (treeEncode (us,f (u,b))).size+1≤(A+2)*X^(a+1) := by
        have haa : X^a≤X^(a+1) := Nat.pow_le_pow_right hX (by omega)
        have h1 := Nat.one_le_pow (a+1) X hX
        have hun : (treeEncode us).size+2≤X := by dsimp [X]; simp [DataTree.size]; omega
        simp only [treeEncode_pair,DataTree.size]
        nlinarith [Nat.mul_le_mul_left A haa]
      have ht : P.program.foldWork us (f (u,b))≤C*(A+2)^d*X^((a+1)*d) := by
        calc
          _ ≤ C*((treeEncode (us,f (u,b))).size+1)^d := ih us _ (by simpa using hn)
          _ ≤ C*((A+2)*X^(a+1))^d := by gcongr
          _ = _ := by rw [mul_pow,←pow_mul]; ring
      have hbase : 10*X+P.program.time (u,b)+1≤(A+11)*X^(a+1) := by
        have haa : X^a≤X^(a+1) := Nat.pow_le_pow_right hX (by omega)
        have h1 := Nat.one_le_pow (a+1) X hX
        nlinarith [Nat.mul_le_mul_left A haa]
      have hadd := nat_poly_add X (A+11) (C*(A+2)^d) (a+1) ((a+1)*d) hX
      change 10*X+P.program.time (u,b)+P.program.foldWork us (f (u,b))+1≤_
      have hh := (Nat.add_le_add_right (Nat.add_le_add hbase ht) 1).trans hadd
      rw [show (a+1)*(d+1)=(a+1)+(a+1)*d by ring]
      dsimp only [X] at hh ⊢
      nlinarith only [hh]

end ParityWL.Complexity

end OAI
