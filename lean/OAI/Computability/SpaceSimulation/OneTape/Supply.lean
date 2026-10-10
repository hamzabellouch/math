import OAI.Computability.SpaceSimulation.OneTape.Wander
import OAI.Computability.SpaceSimulation.Epoch.Uniform
import OAI.Computability.SpaceSimulation.Register.External

namespace OAI

namespace Fifths

namespace Entry
open Fifths.Comp
variable {X I A B J : Type} {x : I → List X} {S a : I → ℕ}

/-- Computes a value from a fixed finite type. -/
def Tells [Fintype A] (x : I → List X) (S a : I → ℕ) (v : I → A) : Prop :=
  Comp x S a fun i => Entry.code (v i)

variable [Fintype A] [Fintype B]
  {v : I → A} {w : I → B}

theorem finite_map (f : A → ℕ) (h : Tells x S a v) :
    Comp x S a (fun i => f (v i)) :=
  chooseCase code (code_inj _) (fun _ b => f b) h
    (fun _ => Comp.constant (Comp.source h) _)

theorem tell_both (p : Tells x S a v) (q : Tells x S a w) :
    Tells x S a (fun i => (v i,w i)) :=
  chooseCase code (code_inj _) (fun i b => code (b,w i)) p
    (fun b => finite_map (fun c => code (b,c)) q)

theorem tell_all [Fintype J] [DecidableEq J] {v : I → J → A} (o : Fits S a)
    (p : ∀ j, Tells x S a (fun i => v i j)) : Tells x S a v := by
  classical
  let L := (Finset.univ : Finset J).toList
  let e := fun (f : J → A) => Bin.tuple (fun j => code (f j)) L
  have c (l : List J) (a b : J → A)
      (h : Bin.tuple (fun j => code (a j)) l = Bin.tuple (fun j => code (b j)) l) :
      ∀ j ∈ l, a j = b j := by
    induction l with
    | nil => simp
    | cons k l ih =>
      simp only [Bin.tuple,Bin.pair_inj] at h
      simp [(code_inj A) h.1]
      exact ih h.2
  have g : Function.Injective e := by
    intro a b h
    funext j
    exact c L a b h j (by simp [L])
  exact chooseCase e g (fun _ b => code b) (w := v)
    (Comp.tuple (f := fun i j => code (v i j)) L p o)
    (fun _ => Comp.constant o _)
end Entry

namespace Single
open Square Entry Fifths.Comp
variable {I X : Type} (M : Single X)

inductive Arg
  | cap | tag | minus | magnitude
  deriving DecidableEq

instance : Fintype Arg :=
  ⟨{.cap, .tag, .minus, .magnitude}, by intro a; cases a <;> simp⟩
abbrev Sym := TM X Arg M.A

noncomputable def arg (T : ℕ) (h : M.Tag) (p : ℤ) : Arg → ℕ
  | .cap => T
  | .tag => code h
  | .minus => (decide (p < 0)).toNat
  | .magnitude => p.natAbs

/-- Access condition with a numeric allowance of cells (bits accounting
of TM.Within). -/
def Gives (A : M.Sym) (x : List X) (T s : ℕ) : Prop :=
  ∀ (h : M.Tag) (p : ℤ), Inside T p →
    A.Within (binaryIn x (M.arg T h p)) (M.sensor x h p) s

theorem Gives.mono {M : Single X} {A : M.Sym} {x T s d} (p : M.Gives A x T s)
    (h : s ≤ d) : M.Gives A x T d :=
  fun h' q m => (p h' q m).mono h

/-- Sufficient resources and access for a family of offset trials. -/
structure Kit (A : M.Sym) (x : I → List X) (S a : I → ℕ) (W : I → Site) : Prop where
  ofCap : Comp x S a (fun i => (W i).T)
  ofK : Comp x S a (fun i => (W i).k)
  ofPosition : Comp x S a (fun i => (W i).left.val)
  budget : Fits S (fun i => let C := (M.tour (x i) (W i)).circuit
    C.P.n^(C.width+1))
  access : ∃ d : ℕ, ∀ i, M.Gives A (x i) (W i).T (d*(S i+1))

namespace Kit
variable {M} {A : M.Sym} {x : I → List X} {S a b : I → ℕ} {W : I → Site}
variable (p : M.Kit A x S a W)
include p

theorem changeInput {J : Type} (r : J → I) {b : J → ℕ}
    (h : ReComp x S r b (fun i => a (r i))) :
    M.Kit A (fun i => x (r i)) (fun i => S (r i)) b (fun i => W (r i)) :=
  { ofCap := Comp.trans h (p.ofCap.pull r)
    ofK := Comp.trans h (p.ofK.pull r)
    ofPosition := Comp.trans h (p.ofPosition.pull r)
    budget := p.budget.pull r
    access := by obtain ⟨d,h⟩ := p.access; exact ⟨d,fun i => h (r i)⟩ }

theorem read (h : M.Tag) {u : ∀ i, Square (W i).T}
    (q : Comp x S a (fun i => (u i).val)) :
    Tells x S a (fun i => M.sensor (x i) h (disp (u i))) := by
  obtain ⟨d,l⟩ := p.access
  change Comp _ _ _ _
  apply Comp.call A Entry.code q.source (f := fun i => M.arg (W i).T h (disp (u i)))
    ?_ d (fun i => l i h (disp (u i)) (Square.bounded _))
  intro j
  have r := p.ofCap
  cases j with
  | cap => exact r
  | tag => exact Comp.constant q.source _
  | minus =>
    exact (q.lt r).congr (fun i => by simp [arg,disp])
  | magnitude =>
    exact ((q.sub r).add (r.sub q)).congr (fun i => by
      simp only [arg,disp]; omega)

-- Common sizes. radix itself and its b-th power included in S.
theorem ofBlock : Comp x S a (fun i => (W i).b) := p.ofK.mul p.ofK
theorem double : Comp x S a (fun i => 2*(W i).T) :=
  (Comp.constant p.ofCap.source 2).mul p.ofCap
theorem ofBlocks : Comp x S a (fun i => (W i).N) :=
  (p.double.add p.ofBlock).add (Comp.constant p.ofCap.source 2)
theorem ofW : Comp x S a (fun i => M.w (W i).T) :=
  (((p.double.add (Comp.constant p.ofCap.source (Fintype.card M.Q))).add
    (Comp.constant p.ofCap.source (Fintype.card M.A))).plus1).size
theorem ofC : Comp x S a (fun i => M.c (W i).T) :=
  p.ofW.mul (Comp.constant p.ofCap.source M.fields)

theorem granted : Fits S (fun i => M.radix (W i).T ^ ((W i).b+1)) :=
  (fitBitsD (P := fun i => (M.tour (x i) (W i)).circuit.P) p.budget).congr
    (fun i => Tour.powers (M.tour (x i) (W i)) _)

theorem subGranted (h : ∀ i, b i ≤ (W i).b+1) :
    Fits S (fun i => M.radix (W i).T ^ b i) :=
  p.granted.mono (fun i => Nat.pow_le_pow_right (M.rpos _) (h i))
theorem ofRadix : Comp x S a (fun i => M.radix (W i).T) :=
  (Comp.constant p.ofCap.source 2).pow p.ofC ((p.subGranted
    (fun i => Nat.succ_le_succ (Nat.zero_le (W i).b))).congr (fun i => by simp [Single.radix]))
theorem ofQ : Comp x S a (fun i => M.q (W i).T) :=
  (Comp.constant p.ofCap.source 2).pow p.ofW
    (p.ofRadix.target.mono (fun _ => M.moduli _))

theorem neighbors {r : ∀ i, Square (W i).T} (c : Comp x S a (fun i => (r i).val))
    {u : I → Dir} (q : Tells x S a u) :
    Comp x S a (fun i => (Square.adjacent (r i) (u i)).val) := by
  apply chooseCase code (code_inj Dir) (fun i k => (Square.adjacent (r i) k).val) q
  intro k; cases k
  · exact p.double.min c.minus1
  · exact c
  · exact p.double.min c.plus1
end Kit
end Single
end Fifths

end OAI
