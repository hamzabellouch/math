import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval0 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm0 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm0 (originalVector B) := by
  rw [reducedTermArithmetic0, ← sound0 B hB hF]
  change (16777065463570169856000 : ℝ) * mixedMoment B node0 node0Labels =
    (37623398400 : ℝ) * ((445921053840 : ℝ) * mixedMoment B node0 node0Labels + 0)
  ring

theorem reducedTermEval1 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1 (originalVector B) := by
  rw [reducedTermArithmetic1, ← sound1 B hB hF]
  change (24341526349213925376000 : ℝ) * mixedMoment B node1 node1Labels =
    (37623398400 : ℝ) * ((646978406640 : ℝ) * mixedMoment B node1 node1Labels + 0)
  ring

theorem reducedTermEval2 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm2 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm2 (originalVector B) := by
  rw [reducedTermArithmetic2, ← sound2 B hB hF]
  change (2819849594986561536000 : ℝ) * mixedMoment B node2 node2Labels =
    (37623398400 : ℝ) * ((74949359040 : ℝ) * mixedMoment B node2 node2Labels + 0)
  ring

theorem reducedTermEval3 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm3 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm3 (originalVector B) := by
  rw [reducedTermArithmetic3, ← sound3 B hB hF]
  change (19909918819090169856000 : ℝ) * mixedMoment B node3 node3Labels =
    (37623398400 : ℝ) * ((529189803840 : ℝ) * mixedMoment B node3 node3Labels + 0)
  ring

theorem reducedTermEval4 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm4 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm4 (originalVector B) := by
  rw [reducedTermArithmetic4, ← sound4 B hB hF]
  change (48412391129138921472000 : ℝ) * mixedMoment B node4 node4Labels =
    (37623398400 : ℝ) * ((1286762844080 : ℝ) * mixedMoment B node4 node4Labels + 0)
  ring

theorem reducedTermEval5 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm5 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm5 (originalVector B) := by
  rw [reducedTermArithmetic5, ← sound5 B hB hF]
  change (8123618207333744640000 : ℝ) * mixedMoment B node5 node5Labels =
    (37623398400 : ℝ) * ((215919309600 : ℝ) * mixedMoment B node5 node5Labels + 0)
  ring

theorem reducedTermEval6 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm6 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm6 (originalVector B) := by
  rw [reducedTermArithmetic6, ← sound6 B hB hF]
  change (7901800914030428160000 : ℝ) * mixedMoment B node6 node6Labels =
    (37623398400 : ℝ) * ((210023582400 : ℝ) * mixedMoment B node6 node6Labels + 0)
  ring

theorem reducedTermEval7 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm7 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm7 (originalVector B) := by
  rw [reducedTermArithmetic7, ← sound7 B hB hF]
  change (6584917799562117120000 : ℝ) * mixedMoment B node7 node7Labels =
    (37623398400 : ℝ) * ((175021876800 : ℝ) * mixedMoment B node7 node7Labels + 0)
  ring

theorem reducedTermEval8 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm8 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm8 (originalVector B) := by
  rw [reducedTermArithmetic8, ← sound8 B hB hF]
  change (-436081132551536640000 : ℝ) * mixedMoment B node8 node8Labels =
    (37623398400 : ℝ) * (((-11590689600 : ℤ) : ℝ) * mixedMoment B node8 node8Labels + 0)
  ring

theorem reducedTermEval9 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm9 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm9 (originalVector B) := by
  rw [reducedTermArithmetic9, ← sound9 B hB hF]
  change (436081132551536640000 : ℝ) * mixedMoment B node9 node9Labels =
    (37623398400 : ℝ) * ((11590689600 : ℝ) * mixedMoment B node9 node9Labels + 0)
  ring

theorem reducedTermEval10 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm10 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm10 (originalVector B) := by
  rw [reducedTermArithmetic10, ← sound10 B hB hF]
  change (3375571545237749760000 : ℝ) * mixedMoment B node10 node10Labels =
    (37623398400 : ℝ) * ((89720006400 : ℝ) * mixedMoment B node10 node10Labels + 0)
  ring

theorem reducedTermEval11 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm11 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm11 (originalVector B) := by
  rw [reducedTermArithmetic11, ← sound11 B hB hF]
  change (3375571545237749760000 : ℝ) * mixedMoment B node11 node11Labels =
    (37623398400 : ℝ) * ((89720006400 : ℝ) * mixedMoment B node11 node11Labels + 0)
  ring

theorem reducedTermEval12 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm12 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm12 (originalVector B) := by
  rw [reducedTermArithmetic12, ← sound12 B hB hF]
  change (-2366085260515737600000 : ℝ) * mixedMoment B node12 node12Labels =
    (37623398400 : ℝ) * (((-62888664000 : ℤ) : ℝ) * mixedMoment B node12 node12Labels + 0)
  ring

theorem reducedTermEval13 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm13 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm13 (originalVector B) := by
  rw [reducedTermArithmetic13, ← sound13 B hB hF]
  change (-997380730546421760000 : ℝ) * mixedMoment B node13 node13Labels =
    (37623398400 : ℝ) * (((-26509586400 : ℤ) : ℝ) * mixedMoment B node13 node13Labels + 0)
  ring

theorem reducedTermEval14 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm14 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm14 (originalVector B) := by
  rw [reducedTermArithmetic14, ← sound14 B hB hF]
  change (-2046607888629104640000 : ℝ) * mixedMoment B node14 node14Labels =
    (37623398400 : ℝ) * (((-54397209600 : ℤ) : ℝ) * mixedMoment B node14 node14Labels + 0)
  ring

theorem reducedTermEval15 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm15 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm15 (originalVector B) := by
  rw [reducedTermArithmetic15, ← sound15 B hB hF]
  change (-3375571545237749760000 : ℝ) * mixedMoment B node15 node15Labels =
    (37623398400 : ℝ) * (((-89720006400 : ℤ) : ℝ) * mixedMoment B node15 node15Labels + 0)
  ring

theorem reducedTermEval16 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm16 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm16 (originalVector B) := by
  rw [reducedTermArithmetic16, ← sound16 B hB hF]
  change (2046607888629104640000 : ℝ) * mixedMoment B node16 node16Labels =
    (37623398400 : ℝ) * ((54397209600 : ℝ) * mixedMoment B node16 node16Labels + 0)
  ring

theorem reducedTermEval17 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm17 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm17 (originalVector B) := by
  rw [reducedTermArithmetic17, ← sound17 B hB hF]
  change (-626056931123527680000 : ℝ) * mixedMoment B node17 node17Labels =
    (37623398400 : ℝ) * (((-16640095200 : ℤ) : ℝ) * mixedMoment B node17 node17Labels + 0)
  ring

theorem reducedTermEval18 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm18 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm18 (originalVector B) := by
  rw [reducedTermArithmetic18, ← sound18 B hB hF]
  change (-3375571545237749760000 : ℝ) * mixedMoment B node18 node18Labels =
    (37623398400 : ℝ) * (((-89720006400 : ℤ) : ℝ) * mixedMoment B node18 node18Labels + 0)
  ring

theorem reducedTermEval19 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm19 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm19 (originalVector B) := by
  rw [reducedTermArithmetic19, ← sound19 B hB hF]
  change (-1397522187023155200000 : ℝ) * mixedMoment B node19 node19Labels =
    (37623398400 : ℝ) * (((-37145028000 : ℤ) : ℝ) * mixedMoment B node19 node19Labels + 0)
  ring

theorem reducedTermEval20 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm20 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm20 (originalVector B) := by
  rw [reducedTermArithmetic20, ← sound20 B hB hF]
  change (859856298608885760000 : ℝ) * mixedMoment B node20 node20Labels =
    (37623398400 : ℝ) * ((22854296400 : ℝ) * mixedMoment B node20 node20Labels + 0)
  ring

theorem reducedTermEval21 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm21 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm21 (originalVector B) := by
  rw [reducedTermArithmetic21, ← sound21 B hB hF]
  change (-1867476387523461120000 : ℝ) * mixedMoment B node21 node21Labels =
    (37623398400 : ℝ) * (((-49636036800 : ℤ) : ℝ) * mixedMoment B node21 node21Labels + 0)
  ring

theorem reducedTermEval22 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm22 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm22 (originalVector B) := by
  rw [reducedTermArithmetic22, ← sound22 B hB hF]
  change (-1097981935528181760000 : ℝ) * mixedMoment B node22 node22Labels =
    (37623398400 : ℝ) * (((-29183486400 : ℤ) : ℝ) * mixedMoment B node22 node22Labels + 0)
  ring

theorem reducedTermEval23 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm23 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm23 (originalVector B) := by
  rw [reducedTermArithmetic23, ← sound24 B hB hF]
  change (1867476387523461120000 : ℝ) * mixedMoment B node24 node24Labels =
    (37623398400 : ℝ) * ((49636036800 : ℝ) * mixedMoment B node24 node24Labels + 0)
  ring

theorem reducedTermEval24 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm24 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm24 (originalVector B) := by
  rw [reducedTermArithmetic24, ← sound26 B hB hF]
  change (1388539976889139200000 : ℝ) * mixedMoment B node26 node26Labels =
    (37623398400 : ℝ) * ((36906288000 : ℝ) * mixedMoment B node26 node26Labels + 0)
  ring

theorem reducedTermEval25 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm25 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm25 (originalVector B) := by
  rw [reducedTermArithmetic25, ← sound27 B hB hF]
  change (-568486539952128000000 : ℝ) * mixedMoment B node27 node27Labels =
    (37623398400 : ℝ) * (((-15109920000 : ℤ) : ℝ) * mixedMoment B node27 node27Labels + 0)
  ring

theorem reducedTermEval26 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm26 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm26 (originalVector B) := by
  rw [reducedTermArithmetic26, ← sound28 B hB hF]
  change (790967239114752000000 : ℝ) * mixedMoment B node28 node28Labels =
    (37623398400 : ℝ) * ((21023280000 : ℝ) * mixedMoment B node28 node28Labels + 0)
  ring

theorem reducedTermEval27 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm27 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm27 (originalVector B) := by
  rw [reducedTermArithmetic27, ← sound29 B hB hF]
  change (-801997817551257600000 : ℝ) * mixedMoment B node29 node29Labels =
    (37623398400 : ℝ) * (((-21316464000 : ℤ) : ℝ) * mixedMoment B node29 node29Labels + 0)
  ring

theorem reducedTermEval28 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm28 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm28 (originalVector B) := by
  rw [reducedTermArithmetic28, ← sound30 B hB hF]
  change (249635823389245440000 : ℝ) * mixedMoment B node30 node30Labels =
    (37623398400 : ℝ) * ((6635121600 : ℝ) * mixedMoment B node30 node30Labels + 0)
  ring

theorem reducedTermEval29 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm29 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm29 (originalVector B) := by
  rw [reducedTermArithmetic29, ← sound32 B hB hF]
  change (-1241591289985105920000 : ℝ) * mixedMoment B node32 node32Labels =
    (37623398400 : ℝ) * (((-33000508800 : ℤ) : ℝ) * mixedMoment B node32 node32Labels + 0)
  ring

theorem reducedTermEval30 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm30 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm30 (originalVector B) := by
  rw [reducedTermArithmetic30, ← sound33 B hB hF]
  change (-2581675460001792000000 : ℝ) * mixedMoment B node33 node33Labels =
    (37623398400 : ℝ) * (((-68618880000 : ℤ) : ℝ) * mixedMoment B node33 node33Labels + 0)
  ring

theorem reducedTermEval31 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm31 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm31 (originalVector B) := by
  rw [reducedTermArithmetic31, ← sound34 B hB hF]
  change (-290558041360957440000 : ℝ) * mixedMoment B node34 node34Labels =
    (37623398400 : ℝ) * (((-7722801600 : ℤ) : ℝ) * mixedMoment B node34 node34Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
