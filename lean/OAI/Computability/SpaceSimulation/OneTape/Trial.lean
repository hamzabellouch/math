import OAI.Computability.SpaceSimulation.OneTape.Control
import OAI.Computability.SpaceSimulation.OneTape.Sweeps
import OAI.Computability.SpaceSimulation.Epoch.Theorem

namespace OAI

namespace Fifths.Single
open Square Entry Fifths.Comp Radix Tour
variable {I X : Type}

namespace Kit
variable {M : Single X} {A : M.Sym} {x : I → List X} {S a b j : I → ℕ} {W : I → Site}
variable (p : M.Kit A x S a W)
include p

theorem onPaper (h : Comp x S a b) :
    Comp x S a (fun i => (M.tour (x i) (W i)).tape (b i)) := by
  let d (i : I) := M.glimpse (W i) (M.sensor (x i) none) (b i)
  let n i := (W i).b
  apply digits p.ofRadix p.ofBlock (p.subGranted (fun i => Nat.le_succ (n i)))
    (fun i => M.rpos _) d (fun i j _ => M.sym_lt _ _)
  intro e g w
  let k : Before n → I := fun i => i.1.1
  let u (i : Before n) := (W (k i)).pin (b (k i)) i.1.2
  have c := p.changeInput k g
  have l := c.ofPosition
  have v := ((g.trans (h.pull k)).mul c.ofBlock).add w
  have z := c.double
  have y := c.read none (u := u) (z.min (v.sub l))
  refine (((l.le v).both (v.le (l.add z))).iteB y
    (Comp.constant v.source (Entry.code (Entry.parse M.A 0)))).congr ?_
  intro i
  change _ = d (k i) _
  dsimp only [d,glimpse,Site.reach]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  split <;> rfl

theorem runnability : Runnable (fun i => M.tour (x i) (W i)) x S a :=
  { kOf := p.ofK
    cOf := p.ofC
    nOf := p.ofBlocks
    fitReg := p.budget
    initOf := p.start
    tapeOf := fun {_U} r {_s _t} o h => (p.changeInput r o).onPaper h
    selectOf := fun {_U} r {_s _t} o h _ => (p.changeInput r o).selecting h
    visitOf := fun {_U} r {_s _t _u} o h g a b => (p.changeInput r o).sweeping g h b a }
end Kit

noncomputable def lastWord (M : Single X) (x : List X) (W : Site) : ℕ :=
  let D := M.tour x W
  (D.story D.visits).ctrl

noncomputable def complete (M : Single X) (x : List X) (W : Site) :=
  M.doneAt W (M.lastWord x W)
noncomputable def readout (M : Single X) (x : List X) (W : Site) :=
  M.predict W (M.lastWord x W)
theorem if_complete (M : Single X) (x : List X) (W : Site)
    (h : M.complete x W) : M.readout x W = M.outcome x W.T :=
  M.reported x W h
theorem some_complete (M : Single X) (x : List X) (T k : ℕ) (h : 0<k) (l : T ≤ k^5) :
    ∃ a : Fin (k*k), M.complete x (Site.mk T k h a) = true := by
  exact M.sufficient x T k h l

namespace Kit
variable {M : Single X} {A : M.Sym} {x : I → List X} {S a : I → ℕ} {W : I → Site}
variable (p : M.Kit A x S a W)

include p
theorem solves (b : Scaled S (fun i =>
    let D := M.tour (x i) (W i); D.E * D.per)) :
    Comp x S a (fun i => (M.complete (x i) (W i)).toNat)
    ∧ Tells x S a (fun i => M.readout (x i) (W i)) := by
  have c := Tour.follows p.runnability (fun i => M.tour_bounded (x i) (W i)) b
  have d := p.parsed c
  exact ⟨d.time.eq p.ofCap, finite_map (fun y => code (M.finish y)) d.state⟩
end Kit
end Fifths.Single

end OAI
