import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound1

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval32 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm32 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm32 (originalVector B) := by
  rw [reducedTermArithmetic32, ← sound35 B hB hF]
  change (2018339593389342720000 : ℝ) * mixedMoment B node35 node35Labels =
    (37623398400 : ℝ) * ((53645860800 : ℝ) * mixedMoment B node35 node35Labels + 0)
  ring

theorem reducedTermEval33 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm33 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm33 (originalVector B) := by
  rw [reducedTermArithmetic33, ← sound36 B hB hF]
  change (568486539952128000000 : ℝ) * mixedMoment B node36 node36Labels =
    (37623398400 : ℝ) * ((15109920000 : ℝ) * mixedMoment B node36 node36Labels + 0)
  ring

theorem reducedTermEval34 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm34 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm34 (originalVector B) := by
  rw [reducedTermArithmetic34, ← sound37 B hB hF]
  change (1241591289985105920000 : ℝ) * mixedMoment B node37 node37Labels =
    (37623398400 : ℝ) * ((33000508800 : ℝ) * mixedMoment B node37 node37Labels + 0)
  ring

theorem reducedTermEval35 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm35 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm35 (originalVector B) := by
  rw [reducedTermArithmetic35, ← sound38 B hB hF]
  change (2146424329717678080000 : ℝ) * mixedMoment B node38 node38Labels =
    (37623398400 : ℝ) * ((57050251200 : ℝ) * mixedMoment B node38 node38Labels + 0)
  ring

theorem reducedTermEval36 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm36 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm36 (originalVector B) := by
  rw [reducedTermArithmetic36, ← sound39 B hB hF]
  change (-1040603062503997440000 : ℝ) * mixedMoment B node39 node39Labels =
    (37623398400 : ℝ) * (((-27658401600 : ℤ) : ℝ) * mixedMoment B node39 node39Labels + 0)
  ring

theorem reducedTermEval37 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm37 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm37 (originalVector B) := by
  rw [reducedTermArithmetic37, ← sound40 B hB hF]
  change (1114225491652116480000 : ℝ) * mixedMoment B node40 node40Labels =
    (37623398400 : ℝ) * ((29615227200 : ℝ) * mixedMoment B node40 node40Labels + 0)
  ring

theorem reducedTermEval38 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm38 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm38 (originalVector B) := by
  rw [reducedTermArithmetic38, ← sound41 B hB hF]
  change (163104113979555840000 : ℝ) * mixedMoment B node41 node41Labels =
    (37623398400 : ℝ) * ((4335177600 : ℝ) * mixedMoment B node41 node41Labels + 0)
  ring

theorem reducedTermEval39 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm39 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm39 (originalVector B) := by
  rw [reducedTermArithmetic39, ← sound42 B hB hF]
  change (-182676889381109760000 : ℝ) * mixedMoment B node42 node42Labels =
    (37623398400 : ℝ) * (((-4855406400 : ℤ) : ℝ) * mixedMoment B node42 node42Labels + 0)
  ring

theorem reducedTermEval40 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm40 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm40 (originalVector B) := by
  rw [reducedTermArithmetic40, ← sound58 B hB hF]
  change (-10004385195786240000000 : ℝ) * mixedMoment B node58 node58Labels =
    (37623398400 : ℝ) * (((-265908600000 : ℤ) : ℝ) * mixedMoment B node58 node58Labels + 0)
  ring

theorem reducedTermEval41 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm41 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm41 (originalVector B) := by
  rw [reducedTermArithmetic41, ← sound59 B hB hF]
  change (-2203761666510028800000 : ℝ) * mixedMoment B node59 node59Labels =
    (37623398400 : ℝ) * (((-58574232000 : ℤ) : ℝ) * mixedMoment B node59 node59Labels + 0)
  ring

theorem reducedTermEval42 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm42 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm42 (originalVector B) := by
  rw [reducedTermArithmetic42, ← sound60 B hB hF]
  change (2085180239432908800000 : ℝ) * mixedMoment B node60 node60Labels =
    (37623398400 : ℝ) * ((55422432000 : ℝ) * mixedMoment B node60 node60Labels + 0)
  ring

theorem reducedTermEval43 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm43 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm43 (originalVector B) := by
  rw [reducedTermArithmetic43, ← sound63 B hB hF]
  change (2127030701889945600000 : ℝ) * mixedMoment B node63 node63Labels =
    (37623398400 : ℝ) * ((56534784000 : ℝ) * mixedMoment B node63 node63Labels + 0)
  ring

theorem reducedTermEval44 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm44 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm44 (originalVector B) := by
  rw [reducedTermArithmetic44, ← sound65 B hB hF]
  change (-1707972381290004480000 : ℝ) * mixedMoment B node65 node65Labels =
    (37623398400 : ℝ) * (((-45396547200 : ℤ) : ℝ) * mixedMoment B node65 node65Labels + 0)
  ring

theorem reducedTermEval45 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm45 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm45 (originalVector B) := by
  rw [reducedTermArithmetic45, ← sound66 B hB hF]
  change (-1138648254193336320000 : ℝ) * mixedMoment B node66 node66Labels =
    (37623398400 : ℝ) * (((-30264364800 : ℤ) : ℝ) * mixedMoment B node66 node66Labels + 0)
  ring

theorem reducedTermEval46 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm46 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm46 (originalVector B) := by
  rw [reducedTermArithmetic46, ← sound67 B hB hF]
  change (2328725225904537600000 : ℝ) * mixedMoment B node67 node67Labels =
    (37623398400 : ℝ) * ((61895664000 : ℝ) * mixedMoment B node67 node67Labels + 0)
  ring

theorem reducedTermEval47 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm47 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm47 (originalVector B) := by
  rw [reducedTermArithmetic47, ← sound68 B hB hF]
  change (474211573967093760000 : ℝ) * mixedMoment B node68 node68Labels =
    (37623398400 : ℝ) * ((12604166400 : ℝ) * mixedMoment B node68 node68Labels + 0)
  ring

theorem reducedTermEval48 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm48 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm48 (originalVector B) := by
  rw [reducedTermArithmetic48, ← sound69 B hB hF]
  change (-2127030701889945600000 : ℝ) * mixedMoment B node69 node69Labels =
    (37623398400 : ℝ) * (((-56534784000 : ℤ) : ℝ) * mixedMoment B node69 node69Labels + 0)
  ring

theorem reducedTermEval49 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm49 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm49 (originalVector B) := by
  rw [reducedTermArithmetic49, ← sound70 B hB hF]
  change (-515328109266862080000 : ℝ) * mixedMoment B node70 node70Labels =
    (37623398400 : ℝ) * (((-13697011200 : ℤ) : ℝ) * mixedMoment B node70 node70Labels + 0)
  ring

theorem reducedTermEval50 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm50 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm50 (originalVector B) := by
  rw [reducedTermArithmetic50, ← sound71 B hB hF]
  change (736180046364672000000 : ℝ) * mixedMoment B node71 node71Labels =
    (37623398400 : ℝ) * ((19567080000 : ℝ) * mixedMoment B node71 node71Labels + 0)
  ring

theorem reducedTermEval51 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm51 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm51 (originalVector B) := by
  rw [reducedTermArithmetic51, ← sound72 B hB hF]
  change (-413398015754895360000 : ℝ) * mixedMoment B node72 node72Labels =
    (37623398400 : ℝ) * (((-10987790400 : ℤ) : ℝ) * mixedMoment B node72 node72Labels + 0)
  ring

theorem reducedTermEval52 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm52 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm52 (originalVector B) := by
  rw [reducedTermArithmetic52, ← sound73 B hB hF]
  change (102561083051212800000 : ℝ) * mixedMoment B node73 node73Labels =
    (37623398400 : ℝ) * ((2725992000 : ℝ) * mixedMoment B node73 node73Labels + 0)
  ring

theorem reducedTermEval53 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm53 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm53 (originalVector B) := by
  rw [reducedTermArithmetic53, ← sound74 B hB hF]
  change (289949987045376000000 : ℝ) * mixedMoment B node74 node74Labels =
    (37623398400 : ℝ) * ((7706640000 : ℝ) * mixedMoment B node74 node74Labels + 0)
  ring

theorem reducedTermEval54 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm54 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm54 (originalVector B) := by
  rw [reducedTermArithmetic54, ← sound75 B hB hF]
  change (-289949987045376000000 : ℝ) * mixedMoment B node75 node75Labels =
    (37623398400 : ℝ) * (((-7706640000 : ℤ) : ℝ) * mixedMoment B node75 node75Labels + 0)
  ring

theorem reducedTermEval55 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm55 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm55 (originalVector B) := by
  rw [reducedTermArithmetic55, ← sound76 B hB hF]
  change (-1241591289985105920000 : ℝ) * mixedMoment B node76 node76Labels =
    (37623398400 : ℝ) * (((-33000508800 : ℤ) : ℝ) * mixedMoment B node76 node76Labels + 0)
  ring

theorem reducedTermEval56 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm56 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm56 (originalVector B) := by
  rw [reducedTermArithmetic56, ← sound87 B hB hF]
  change (7122003490024980480000 : ℝ) * mixedMoment B node87 node87Labels =
    (37623398400 : ℝ) * ((189297187200 : ℝ) * mixedMoment B node87 node87Labels + 0)
  ring

theorem reducedTermEval57 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm57 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm57 (originalVector B) := by
  rw [reducedTermArithmetic57, ← sound88 B hB hF]
  change (3644952519390658560000 : ℝ) * mixedMoment B node88 node88Labels =
    (37623398400 : ℝ) * ((96879938400 : ℝ) * mixedMoment B node88 node88Labels + 0)
  ring

theorem reducedTermEval58 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm58 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm58 (originalVector B) := by
  rw [reducedTermArithmetic58, ← sound91 B hB hF]
  change (1860757992320532480000 : ℝ) * mixedMoment B node91 node91Labels =
    (37623398400 : ℝ) * ((49457467200 : ℝ) * mixedMoment B node91 node91Labels + 0)
  ring

theorem reducedTermEval59 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm59 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm59 (originalVector B) := by
  rw [reducedTermArithmetic59, ← sound93 B hB hF]
  change (-5848546686531010560000 : ℝ) * mixedMoment B node93 node93Labels =
    (37623398400 : ℝ) * (((-155449718400 : ℤ) : ℝ) * mixedMoment B node93 node93Labels + 0)
  ring

theorem reducedTermEval60 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm60 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm60 (originalVector B) := by
  rw [reducedTermArithmetic60, ← sound95 B hB hF]
  change (1138648254193336320000 : ℝ) * mixedMoment B node95 node95Labels =
    (37623398400 : ℝ) * ((30264364800 : ℝ) * mixedMoment B node95 node95Labels + 0)
  ring

theorem reducedTermEval61 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm61 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm61 (originalVector B) := by
  rw [reducedTermArithmetic61, ← sound96 B hB hF]
  change (1707972381290004480000 : ℝ) * mixedMoment B node96 node96Labels =
    (37623398400 : ℝ) * ((45396547200 : ℝ) * mixedMoment B node96 node96Labels + 0)
  ring

theorem reducedTermEval62 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm62 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm62 (originalVector B) := by
  rw [reducedTermArithmetic62, ← sound97 B hB hF]
  change (-446672871669104640000 : ℝ) * mixedMoment B node97 node97Labels =
    (37623398400 : ℝ) * (((-11872209600 : ℤ) : ℝ) * mixedMoment B node97 node97Labels + 0)
  ring

theorem reducedTermEval63 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm63 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm63 (originalVector B) := by
  rw [reducedTermArithmetic63, ← sound98 B hB hF]
  change (3037264535314759680000 : ℝ) * mixedMoment B node98 node98Labels =
    (37623398400 : ℝ) * ((80728075200 : ℝ) * mixedMoment B node98 node98Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
