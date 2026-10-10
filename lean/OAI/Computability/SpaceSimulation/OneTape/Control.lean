import OAI.Computability.SpaceSimulation.OneTape.Supply

namespace OAI

namespace Fifths.Single
open Square Entry Fifths.Comp Radix
variable {I X : Type}

namespace Kit
variable {M : Single X} {A : M.Sym} {x : I → List X} {S a b B j : I → ℕ} {W : I → Site}
variable (p : M.Kit A x S a W)

structure Controller (M : Single X) (x : I → List X) (S a : I → ℕ) (W : I → Site)
    (c : ∀ i : I, M.Control (W i).T) : Prop where
  time : Comp x S a (fun i => (c i).tick.val)
  state : Tells x S a (fun i => (c i).state)
  index : Comp x S a (fun i => (c i).now.val)
  extraPos : ∀ j : Fin M.heads, Comp x S a (fun i => ((c i).other j).val)

include p
theorem expConst (n : ℕ) :
    Comp x S a (fun i => M.q (W i).T ^ n) := by
  induction n with
  | zero => exact (Comp.constant p.ofQ.source 1).congr (fun _ => by simp)
  | succ n ih => exact (ih.mul p.ofQ).congr (fun _ => by simp [pow_succ])

theorem parsed (z : Comp x S a b) :
    Controller M x S a W (fun i => M.parseCtrl (W i).T (b i)) := by
  have d (n) : Comp x S a (fun i => get (M.q (W i).T) (b i) n) :=
    digit p.ofQ z (Comp.constant z.source n) (p.expConst n).target
  constructor
  · exact p.ofCap.min (d 0)
  · refine ((d 1).mod (Comp.constant z.source (Fintype.card M.Q))).congr ?_
    intro i
    exact (Entry.code_parse ..).symm
  · exact p.double.min (d 2)
  · intro j
    exact p.double.min (d (j.val+3))

theorem composeCtrl (c : ∀ i : I, M.Control (W i).T)
    (l : Controller M x S a W c) :
    Comp x S a (fun i => M.packCtrl (c i)) := by
  have h (k : ℕ) : Comp x S a (fun i => M.key (c i) k) := by
    by_cases e : k=0
    · exact l.time.congr fun i => by simp [key,e]
    by_cases t : k=1
    · exact (Comp.congr l.state) (fun i => by simp [key,t])
    by_cases r : k=2
    · exact l.index.congr fun i => by simp [key,r]
    by_cases v : k-3 < M.heads
    · exact (l.extraPos ⟨_,v⟩).congr fun i => by simp [key,v,r,t,e]
    · exact (Comp.constant l.time.source 0).congr fun i => by simp [key,v,r,t,e]
  suffices g : ∀ n : ℕ, Comp x S a (fun i => pack (M.q (W i).T) (M.key (c i)) n) from g _
  intro n
  induction n with
  | zero => exact Comp.constant l.time.source 0
  | succ n ih => exact ih.add ((p.expConst n).mul (h n))

theorem start :
    Comp x S a (fun i => (M.tour (x i) (W i)).init) := by
  let q := fun i => M.capture (W i).T 0 (M.atTime (x i) 0)
  have h : ∀ r : I, (atDisp (W r).T 0).val = (W r).T := by
    intro r
    unfold atDisp
    rw [cut_ok] <;> omega
  exact composeCtrl p q
    { time := (Comp.constant p.ofCap.source 0).congr (fun i => by simp [q,capture])
      state := Comp.constant (x := x) p.ofCap.source (code M.beginState)
      index := p.ofCap.congr fun i => (h i).symm
      extraPos := fun _ => p.ofCap.congr fun i => (h i).symm }

theorem basisStep {c : ∀ i, M.Control (W i).T}
    (o : Controller M x S a W c) (w : Comp x S a B)
    (encode : SingleAct M.Q M.A M.heads → ℕ) :
    Comp x S a (fun i => encode (M.localTable (x i) (W i) (c i) (B i))) := by
  have q : Comp x S a (fun i => (W i).slot (c i).now) :=
    (p.ofPosition.add o.index).mod p.ofBlock
  have h := digit p.ofRadix w q (p.subGranted (fun i =>
    Nat.le_succ_of_le ((W i).slot_lt _).le))
  let work (i : I) := parse M.A
    (get (M.radix (W i).T) (B i) ((W i).slot (c i).now))
  let others (i : I) := fun j => M.sensor (x i) (some j) (disp ((c i).other j))
  have f : Tells x S a work :=
    (h.mod (Comp.constant h.source (Fintype.card M.A))).congr (fun i =>
      (Entry.code_parse ..).symm)
  have g : Tells x S a others := tell_all h.source (fun j => p.read _ (o.extraPos j))
  exact finite_map (fun t => encode (M.move t.1 t.2.1 t.2.2))
    (tell_both o.state (tell_both f g))

theorem refreshable (o : Comp x S a B) (q : Comp x S a j) {v : I → M.A}
    (h : Tells x S a v) :
    Comp x S a (fun i => M.refresh (W i) (B i) (j i) (v i)) := by
  let b i := (W i).b
  apply digits p.ofRadix p.ofBlock (p.subGranted (fun i => Nat.le_succ (b i))) (fun i => M.rpos _)
    (fun i k => if k=j i then code (v i) else get (M.radix (W i).T) (B i) k)
  · intro i k _
    split
    · exact M.sym_lt ..
    · exact get_lt (M.rpos _) _ _
  intro e g w
  let f := fun i : Before b => i.1.1
  have u := p.changeInput f g
  have z := digit u.ofRadix (g.trans (o.pull f)) w
    (u.subGranted (fun i => Nat.le_succ_of_le i.2.le))
  exact ((w.eq (g.trans (q.pull f))).iteB (g.trans (Comp.pull h f)) z).congr fun i => by
    simp [f]

theorem stepCode (o : Comp x S a B) (q : Comp x S a j) (h : Comp x S a b) :
    Comp x S a (fun i =>
      let v := M.localStep (x i) (W i) (j i) (b i,B i)
      Bin.pair v.1 v.2) := by
  let u := fun i => M.parseCtrl (W i).T (b i)
  have c := p.parsed h
  have y := (p.ofPosition.add c.index)
  let r := fun i => M.localTable (x i) (W i) (u i) (B i)
  have v : Controller M x S a W (fun i => M.traceCtrl (u i) (r i)) :=
    { time := p.ofCap.min c.time.plus1
      state := p.basisStep c o (fun t => code t.out)
      index := p.neighbors c.index (p.basisStep c o (fun t => code t.write.dir))
      extraPos := fun j => p.neighbors (c.extraPos j)
        (p.basisStep c o (fun t => code (t.others j))) }
  have w := p.refreshable o (y.mod p.ofBlock) (v := fun i => (r i).write.sym)
    (p.basisStep c o (fun t => code t.write.sym))
  have g := (c.time.lt p.ofCap).both ((y.div p.ofBlock).eq q)
  exact (g.iteB ((p.composeCtrl _ v).pair w) (h.pair o)).congr (fun i => by
    by_cases l : (u i).tick.val < (W i).T ∧ (W i).home (u i).now = j i <;>
      simp only [u,Site.home] at l <;> simp only [localStep,u,r,Bool.and_eq_true,decide_eq_true_eq,Site.slot,Site.home,l,true_and,↓reduceIte])

theorem selecting (q : Comp x S a j) :
    Comp x S a (fun i => M.chooseBlock (W i) (j i)) :=
  (p.ofPosition.add (p.parsed q).index).div p.ofBlock

theorem sweeping (o : Comp x S a B) (q : Comp x S a j)
    (b₀ : ∀ i, B i < M.radix (W i).T ^ (W i).b)
    (c₀ : ∀ i, j i < M.radix (W i).T) :
    Comp x S a (fun i =>
      let v := M.sweep (x i) (W i) (j i) (B i) (W i).T
      Bin.pair v.1 v.2) := by
  let z i k := M.sweep (x i) (W i) (j i) (B i) k
  let T := fun i => (W i).T
  apply fold (fun i k => Bin.pair (z i k).1 (z i k).2) p.ofCap (q.pair o)
  · let f := fun i : Through T => i.1.1
    have h i k := M.sweep_bounded (W i) (x i) _ _ k (c₀ i) (b₀ i)
    exact ((p.ofRadix.target.pull f).mono fun i => (h (f i) i.1.2).1.le).pair
      (((p.subGranted (fun i => Nat.le_succ (W i).b)).pull f).mono fun i =>
        (h (f i) i.1.2).2.le)
  intro e h _ v
  let f := fun i : Before T => i.1.1
  have c := p.changeInput f h
  exact c.stepCode v.right (h.trans ((p.selecting q).pull f)) v.left

end Kit
end Fifths.Single

end OAI
