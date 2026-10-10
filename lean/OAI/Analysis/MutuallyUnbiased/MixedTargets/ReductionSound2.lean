import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound2

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval64 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm64 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm64 (originalVector B) := by
  rw [reducedTermArithmetic64, ← sound99 B hB hF]
  change (3987788694210478080000 : ℝ) * mixedMoment B node99 node99Labels =
    (37623398400 : ℝ) * ((105992251200 : ℝ) * mixedMoment B node99 node99Labels + 0)
  ring

theorem reducedTermEval65 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm65 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm65 (originalVector B) := by
  rw [reducedTermArithmetic65, ← sound100 B hB hF]
  change (-175688147486638080000 : ℝ) * mixedMoment B node100 node100Labels =
    (37623398400 : ℝ) * (((-4669651200 : ℤ) : ℝ) * mixedMoment B node100 node100Labels + 0)
  ring

theorem reducedTermEval66 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm66 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm66 (originalVector B) := by
  rw [reducedTermArithmetic66, ← sound101 B hB hF]
  change (-965157553963008000000 : ℝ) * mixedMoment B node101 node101Labels =
    (37623398400 : ℝ) * (((-25653120000 : ℤ) : ℝ) * mixedMoment B node101 node101Labels + 0)
  ring

theorem reducedTermEval67 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm67 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm67 (originalVector B) := by
  rw [reducedTermArithmetic67, ← sound102 B hB hF]
  change (-1741060865937899520000 : ℝ) * mixedMoment B node102 node102Labels =
    (37623398400 : ℝ) * (((-46276012800 : ℤ) : ℝ) * mixedMoment B node102 node102Labels + 0)
  ring

theorem reducedTermEval68 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm68 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm68 (originalVector B) := by
  rw [reducedTermArithmetic68, ← sound103 B hB hF]
  change (965157553963008000000 : ℝ) * mixedMoment B node103 node103Labels =
    (37623398400 : ℝ) * ((25653120000 : ℝ) * mixedMoment B node103 node103Labels + 0)
  ring

theorem reducedTermEval69 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm69 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm69 (originalVector B) := by
  rw [reducedTermArithmetic69, ← sound104 B hB hF]
  change (870530432968949760000 : ℝ) * mixedMoment B node104 node104Labels =
    (37623398400 : ℝ) * ((23138006400 : ℝ) * mixedMoment B node104 node104Labels + 0)
  ring

theorem reducedTermEval70 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm70 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm70 (originalVector B) := by
  rw [reducedTermArithmetic70, ← sound111 B hB hF]
  change (306647732834795520000 : ℝ) * mixedMoment B node111 node111Labels =
    (37623398400 : ℝ) * ((8150452800 : ℝ) * mixedMoment B node111 node111Labels + 0)
  ring

theorem reducedTermEval71 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm71 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm71 (originalVector B) := by
  rw [reducedTermArithmetic71, ← sound112 B hB hF]
  change (-1515350453861744640000 : ℝ) * mixedMoment B node112 node112Labels =
    (37623398400 : ℝ) * (((-40276809600 : ℤ) : ℝ) * mixedMoment B node112 node112Labels + 0)
  ring

theorem reducedTermEval72 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm72 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm72 (originalVector B) := by
  rw [reducedTermArithmetic72, ← sound113 B hB hF]
  change (-177534884472422400000 : ℝ) * mixedMoment B node113 node113Labels =
    (37623398400 : ℝ) * (((-4718736000 : ℤ) : ℝ) * mixedMoment B node113 node113Labels + 0)
  ring

theorem reducedTermEval73 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm73 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm73 (originalVector B) := by
  rw [reducedTermArithmetic73, ← sound114 B hB hF]
  change (-5781227470859796480000 : ℝ) * mixedMoment B node114 node114Labels =
    (37623398400 : ℝ) * (((-153660427200 : ℤ) : ℝ) * mixedMoment B node114 node114Labels + 0)
  ring

theorem reducedTermEval74 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm74 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm74 (originalVector B) := by
  rw [reducedTermArithmetic74, ← sound115 B hB hF]
  change (-4305813787869511680000 : ℝ) * mixedMoment B node115 node115Labels =
    (37623398400 : ℝ) * (((-114445105200 : ℤ) : ℝ) * mixedMoment B node115 node115Labels + 0)
  ring

theorem reducedTermEval75 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm75 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm75 (originalVector B) := by
  rw [reducedTermArithmetic75, ← sound116 B hB hF]
  change (4739092895251169280000 : ℝ) * mixedMoment B node116 node116Labels =
    (37623398400 : ℝ) * ((125961319200 : ℝ) * mixedMoment B node116 node116Labels + 0)
  ring

theorem reducedTermEval76 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm76 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm76 (originalVector B) := by
  rw [reducedTermArithmetic76, ← sound117 B hB hF]
  change (1906777247715164160000 : ℝ) * mixedMoment B node117 node117Labels =
    (37623398400 : ℝ) * ((50680622400 : ℝ) * mixedMoment B node117 node117Labels + 0)
  ring

theorem reducedTermEval77 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm77 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm77 (originalVector B) := by
  rw [reducedTermArithmetic77, ← sound118 B hB hF]
  change (1118595645017948160000 : ℝ) * mixedMoment B node118 node118Labels =
    (37623398400 : ℝ) * ((29731382400 : ℝ) * mixedMoment B node118 node118Labels + 0)
  ring

theorem reducedTermEval78 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm78 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm78 (originalVector B) := by
  rw [reducedTermArithmetic78, ← sound119 B hB hF]
  change (-13281119832637440000 : ℝ) * mixedMoment B node119 node119Labels =
    (37623398400 : ℝ) * (((-353001600 : ℤ) : ℝ) * mixedMoment B node119 node119Labels + 0)
  ring

theorem reducedTermEval79 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm79 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm79 (originalVector B) := by
  rw [reducedTermArithmetic79, ← sound121 B hB hF]
  change (1118595645017948160000 : ℝ) * mixedMoment B node121 node121Labels =
    (37623398400 : ℝ) * ((29731382400 : ℝ) * mixedMoment B node121 node121Labels + 0)
  ring

theorem reducedTermEval80 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm80 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm80 (originalVector B) := by
  rw [reducedTermArithmetic80, ← sound122 B hB hF]
  change (-5849795392074547200000 : ℝ) * mixedMoment B node122 node122Labels =
    (37623398400 : ℝ) * (((-155482908000 : ℤ) : ℝ) * mixedMoment B node122 node122Labels + 0)
  ring

theorem reducedTermEval81 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm81 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm81 (originalVector B) := by
  rw [reducedTermArithmetic81, ← sound123 B hB hF]
  change (-185267666693652480000 : ℝ) * mixedMoment B node123 node123Labels =
    (37623398400 : ℝ) * (((-4924267200 : ℤ) : ℝ) * mixedMoment B node123 node123Labels + 0)
  ring

theorem reducedTermEval82 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm82 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm82 (originalVector B) := by
  rw [reducedTermArithmetic82, ← sound124 B hB hF]
  change (2068047807947735040000 : ℝ) * mixedMoment B node124 node124Labels =
    (37623398400 : ℝ) * ((54967065600 : ℝ) * mixedMoment B node124 node124Labels + 0)
  ring

theorem reducedTermEval83 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm83 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm83 (originalVector B) := by
  rw [reducedTermArithmetic83, ← sound125 B hB hF]
  change (-273784807984988160000 : ℝ) * mixedMoment B node125 node125Labels =
    (37623398400 : ℝ) * (((-7276982400 : ℤ) : ℝ) * mixedMoment B node125 node125Labels + 0)
  ring

theorem reducedTermEval84 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm84 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm84 (originalVector B) := by
  rw [reducedTermArithmetic84, ← sound126 B hB hF]
  change (273784807984988160000 : ℝ) * mixedMoment B node126 node126Labels =
    (37623398400 : ℝ) * ((7276982400 : ℝ) * mixedMoment B node126 node126Labels + 0)
  ring

theorem reducedTermEval85 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm85 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm85 (originalVector B) := by
  rw [reducedTermArithmetic85, ← sound127 B hB hF]
  change (-4402737275558952960000 : ℝ) * mixedMoment B node127 node127Labels =
    (37623398400 : ℝ) * (((-117021254400 : ℤ) : ℝ) * mixedMoment B node127 node127Labels + 0)
  ring

theorem reducedTermEval86 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm86 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm86 (originalVector B) := by
  rw [reducedTermArithmetic86, ← sound129 B hB hF]
  change (-1100684318889738240000 : ℝ) * mixedMoment B node129 node129Labels =
    (37623398400 : ℝ) * (((-29255313600 : ℤ) : ℝ) * mixedMoment B node129 node129Labels + 0)
  ring

theorem reducedTermEval87 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm87 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm87 (originalVector B) := by
  rw [reducedTermArithmetic87, ← sound130 B hB hF]
  change (5849795392074547200000 : ℝ) * mixedMoment B node130 node130Labels =
    (37623398400 : ℝ) * ((155482908000 : ℝ) * mixedMoment B node130 node130Labels + 0)
  ring

theorem reducedTermEval88 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm88 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm88 (originalVector B) := by
  rw [reducedTermArithmetic88, ← sound131 B hB hF]
  change (-782015458785361920000 : ℝ) * mixedMoment B node131 node131Labels =
    (37623398400 : ℝ) * (((-20785348800 : ℤ) : ℝ) * mixedMoment B node131 node131Labels + 0)
  ring

theorem reducedTermEval89 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm89 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm89 (originalVector B) := by
  rw [reducedTermArithmetic89, ← sound132 B hB hF]
  change (-1118595645017948160000 : ℝ) * mixedMoment B node132 node132Labels =
    (37623398400 : ℝ) * (((-29731382400 : ℤ) : ℝ) * mixedMoment B node132 node132Labels + 0)
  ring

theorem reducedTermEval90 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm90 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm90 (originalVector B) := by
  rw [reducedTermArithmetic90, ← sound133 B hB hF]
  change (-1452979106363473920000 : ℝ) * mixedMoment B node133 node133Labels =
    (37623398400 : ℝ) * (((-38619028800 : ℤ) : ℝ) * mixedMoment B node133 node133Labels + 0)
  ring

theorem reducedTermEval91 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm91 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm91 (originalVector B) := by
  rw [reducedTermArithmetic91, ← sound134 B hB hF]
  change (533261828841799680000 : ℝ) * mixedMoment B node134 node134Labels =
    (37623398400 : ℝ) * ((14173675200 : ℝ) * mixedMoment B node134 node134Labels + 0)
  ring

theorem reducedTermEval92 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm92 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm92 (originalVector B) := by
  rw [reducedTermArithmetic92, ← sound139 B hB hF]
  change (6768212946724454400000 : ℝ) * mixedMoment B node139 node139Labels =
    (37623398400 : ℝ) * ((179893716000 : ℝ) * mixedMoment B node139 node139Labels + 0)
  ring

theorem reducedTermEval93 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm93 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm93 (originalVector B) := by
  rw [reducedTermArithmetic93, ← sound140 B hB hF]
  change (5737333380648468480000 : ℝ) * mixedMoment B node140 node140Labels =
    (37623398400 : ℝ) * ((152493757200 : ℝ) * mixedMoment B node140 node140Labels + 0)
  ring

theorem reducedTermEval94 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm94 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm94 (originalVector B) := by
  rw [reducedTermArithmetic94, ← sound142 B hB hF]
  change (-8525099387879424000000 : ℝ) * mixedMoment B node142 node142Labels =
    (37623398400 : ℝ) * (((-226590360000 : ℤ) : ℝ) * mixedMoment B node142 node142Labels + 0)
  ring

theorem reducedTermEval95 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm95 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm95 (originalVector B) := by
  rw [reducedTermArithmetic95, ← sound143 B hB hF]
  change (704297376586137600000 : ℝ) * mixedMoment B node143 node143Labels =
    (37623398400 : ℝ) * ((18719664000 : ℝ) * mixedMoment B node143 node143Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
