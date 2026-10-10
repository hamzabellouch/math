import OAI.Analysis.FourierLLogL.Procedure.Capital

/-! # The finite spatial and spectral play -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund
open scoped Classical
variable {M J j : ℕ}

structure Scene (M : ℕ) where
  here : Node
  wage : Grid M → ℝ
  fund : Fund M
  live : Bool
  norm : ℝ

def cutoff (j : ℕ) : ℝ := ((j:ℝ)+1)^3

namespace Scene
def mass (s : Scene M) := s.here.avg s.wage
def actor (s : Scene M) : Law (Grid M) :=
    if h : ∃ P : Law (Grid M), PieceLaw s.here s.wage P then Classical.choose h
    else uniform _
def openHere (s : Scene M) (j J : ℕ) (f : Grid M → ℝ) :=
    s.here.lev < J ∧ s.here.avg f ≤ cutoff j ∧ 0 < s.mass
def retire (s : Scene M) (j : ℕ) :=
    s.live=true ∧ (s.fund.breached j ∨ s.mass < exp (-height j))
def enter (s : Scene M) := 2*s.norm < s.mass
def work (s : Scene M) (j J : ℕ) (f : Grid M → ℝ) :=
    s.openHere j J f ∧ ¬ s.retire j ∧ ¬ s.enter
def settled (s : Scene M) (j : ℕ) :=
    s.live=true → ∀ i, i ≤ testIx j →
      ¬ request s.fund.mood j s.here s.wage s.norm (side i) (kappa j (codeWeight capA) i)

def reset (s : Scene M) := {s with norm := s.mass}
def out (s : Scene M) := {s with norm := 0, live := false}
def smaller (s : Scene M) (b : Bool) := {s with here := s.here.child b}
def win (s : Scene M) (u : Update j M s.here) : Scene M :=
    {s with wage := (Set.ofPred (u.take s.fund.mood)).indicator s.wage
            norm := 0
            fund := s.fund.advance s.here u}
def lose (s : Scene M) (u : Update j M s.here) : Scene M :=
    {s with wage := (Set.ofPred fun x => ¬ u.take s.fund.mood x).indicator s.wage}



def beginPlay (f : Grid M → ℝ) (b : Bool) : Scene M :=
    { here:=root
      wage:=f
      fund:=initial M
      live:=b
      norm:=0 }

structure Safe (s : Scene M) (j J : ℕ) (f : Grid M → ℝ) : Prop where
  within : s.here.ok M
  depth_ok : s.here.lev ≤ J
  capital : s.fund.Ok s.here j
  norm_ok : 0 ≤ s.norm
  positive : 0 ≤ s.wage
  sub : s.wage ≤ f
  cut : s.here.avg f ≤ 2*cutoff j

variable {f : Grid M → ℝ} {s : Scene M}

lemma actor_def (hp : s.here.ok M) (hv : 0 ≤ s.wage) (he : 0 < s.mass) :
    PieceLaw s.here s.wage s.actor := by
  unfold actor; split
  · exact Classical.choose_spec _
  · rename_i hh
    exact (hh (make_piece _ hp hv he)).elim

lemma Safe.mass_lower (hh : s.Safe j J f) : 0 ≤ s.mass :=
  avg_nonneg _ (fun x _ => hh.positive x)
lemma Safe.mass_upper (hh : s.Safe j J f) :
    s.mass ≤ s.here.avg f := by
  unfold mass; rw [avg_ex hh.within,avg_ex hh.within]; exact Ex_mono _ hh.sub
lemma Safe.budget (hh : s.Safe j J f) : s.mass ≤ 2*cutoff j :=
    hh.mass_upper.trans hh.cut

end Scene

open Scene

inductive Play (j M : ℕ) : Scene M → Type
| rest (s : Scene M) : Play j M s
| freeze (s : Scene M) (t : Play j M s.out) : Play j M s
| ticket (s : Scene M) (t : Play j M s.reset) : Play j M s
| jump (s : Scene M)
    (l : Play j M (s.smaller false)) (r : Play j M (s.smaller true)) : Play j M s
| attempt (s : Scene M) (u : Update j M s.here)
    (l : Play j M (s.lose u)) (r : Play j M (s.win u)) : Play j M s

namespace Play
variable {s : Scene M}

def Follows (J : ℕ) (f : Grid M → ℝ) : {s : Scene M} → Play j M s → Prop
  | _, .rest s => s.Safe j J f ∧ ¬s.openHere j J f
  | _, .ticket s t => s.Safe j J f ∧ s.openHere j J f ∧ ¬s.retire j ∧
      s.enter ∧ Follows J f t
  | _, .freeze s t => s.Safe j J f ∧ s.openHere j J f ∧ s.retire j ∧ Follows J f t
  | _, .jump s l r => s.Safe j J f ∧ s.work j J f ∧ s.settled j ∧
      Follows J f l ∧ Follows J f r
  | _, .attempt s u l r => s.Safe j J f ∧ s.work j J f ∧ s.live=true ∧
      u.Good capA s.fund.mood s.actor ∧ Follows J f l ∧ Follows J f r

variable {t : Play j M s} {f : Grid M → ℝ}
lemma first (h : t.Follows J f) : s.Safe j J f := by
  cases t <;> exact h.1

end Play
end FourierLLogL.Dyadic.Procedure

end OAI
