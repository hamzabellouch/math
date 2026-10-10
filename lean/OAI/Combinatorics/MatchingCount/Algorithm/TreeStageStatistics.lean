import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeEstimator
import OAI.Combinatorics.MatchingCount.Algorithm.TreeObservables

namespace OAI

namespace MatchingFPRAS.ExecutableStatistics
open TreeTyped TreeFraction ExecutableMarking ExecutableEstimator

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]

def averageA (xs : List (Marks E)) : Fraction := mean (xs.map observableA)
def averageARealizer : Realizer (averageA (E:=E)) := composition (map observableARealizer) meanRealizer
omit [LinearOrder E] [Inhabited E] in
lemma polynomial_averageA : PolynomialTime (averageARealizer (E:=E)) :=
  polynomial_composition (polynomial_map polynomial_observableA) polynomial_mean

def averageD (q : C×E→Fraction) (x : C×List (Marks E)) : Fraction :=
  mean (x.2.map fun s=>observableD q (x.1,s))
def averageDRealizer {q : C×E→Fraction} (Q : Realizer q) : Realizer (averageD q) :=
  (composition (mapWith (observableDRealizer Q)) meanRealizer).congr (fun _=>rfl)
omit [LinearOrder E] [Inhabited E] in
lemma polynomial_averageD {q : C×E→Fraction} {Q : Realizer q} (hQ : PolynomialTime Q) :
    PolynomialTime (averageDRealizer Q) := by
  unfold averageDRealizer
  exact polynomial_congr _ (polynomial_composition
    (polynomial_mapWith (polynomial_observableD hQ)) polynomial_mean)

def averageProbe (q : C×E→Fraction) (x : (C×E)×List (Marks E)) : Fraction :=
  mean (x.2.map fun s=>observableProbe q (x.1.1,(x.1.2,s)))
def averageProbeRealizer {q : C×E→Fraction} (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (averageProbe q) :=
  (composition (mapWith (composition (pair first.fst (pair first.snd second))
      (observableProbeRealizer Q Eq))) meanRealizer).congr (fun _=>rfl)
omit [Inhabited E] in
lemma polynomial_averageProbe {q : C×E→Fraction} {Q : Realizer q}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hQ : PolynomialTime Q) (hE : PolynomialTime Eq) : PolynomialTime (averageProbeRealizer Q Eq) := by
  unfold averageProbeRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_observableProbe hQ hE
  have := polynomial_mean
  tree_cost

abbrev ProbeContext (C E : Type) := (C×ℕ)×(Fraction×List (Marks E))
def estimateProbe (q : C×E→Fraction) (x : ProbeContext C E×E) : E×Fraction :=
  (x.2,upper (x.1.1.2,(x.1.2.1,averageProbe q ((x.1.1.1,x.2),x.1.2.2))))
def estimateProbeRealizer {q : C×E→Fraction} (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (estimateProbe q) :=
  (pair second (composition (pair first.fst.snd (pair first.snd.fst
    (composition (pair (pair first.fst.fst second) first.snd.snd) (averageProbeRealizer Q Eq)))) upperRealizer)).congr (fun _=>rfl)
omit [Inhabited E] in
lemma polynomial_estimateProbe {q : C×E→Fraction} {Q : Realizer q}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hQ : PolynomialTime Q) (hE : PolynomialTime Eq) : PolynomialTime (estimateProbeRealizer Q Eq) := by
  unfold estimateProbeRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_averageProbe hQ hE
  have := polynomial_upper
  tree_cost

abbrev StageInput (C E : Type) := (C×(ℕ×List E))×List (Marks E)
def estimates (q : C×E→Fraction) (x : StageInput C E) : Fraction×List (E×Fraction) :=
  let dbar:=averageD q (x.1.1,x.2)
  (ratio (averageA x.2,dbar),x.1.2.2.map fun e=>estimateProbe q (((x.1.1,x.1.2.1),(dbar,x.2)),e))
def estimatesRealizer {q : C×E→Fraction} (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (estimates q) := by
  let dbar : Realizer (fun x : StageInput C E=>averageD q (x.1.1,x.2)) :=
    (composition (pair first.fst second) (averageDRealizer Q)).congr (fun _=>rfl)
  exact (pair (composition (pair (composition second averageARealizer) dbar) ratioRealizer)
    (composition (pair (pair (pair first.fst first.snd.fst) (pair dbar second)) first.snd.snd)
      (mapWith (estimateProbeRealizer Q Eq)))).congr (fun _=>rfl)
omit [Inhabited E] in
lemma polynomial_estimates {q : C×E→Fraction} {Q : Realizer q}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hQ : PolynomialTime Q) (hE : PolynomialTime Eq) : PolynomialTime (estimatesRealizer Q Eq) := by
  unfold estimatesRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_averageA (E:=E)
  have := polynomial_averageD hQ
  have := polynomial_estimateProbe hQ hE
  have := polynomial_ratio
  tree_cost
end MatchingFPRAS.ExecutableStatistics

end OAI
