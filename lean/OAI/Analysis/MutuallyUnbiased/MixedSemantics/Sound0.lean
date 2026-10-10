import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Single0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Single1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Single2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Single3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Single4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Single5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Single6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Single7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleGroup0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleGroup1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleGroup2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SingleGroup3

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound0 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node0 node0Labels = Sparse.eval nodeValue0 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue0 (familyPairVector B) := singlePair0 B _hB
    _ = _ := by norm_num [singlePairValue0, nodeValue0, Sparse.eval, mixedVector]; ring

theorem sound1 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1 node1Labels = Sparse.eval nodeValue1 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue1 (familyPairVector B) := singlePair1 B _hB
    _ = _ := by norm_num [singlePairValue1, nodeValue1, Sparse.eval, mixedVector]; ring

theorem sound2 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2 node2Labels = Sparse.eval nodeValue2 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue2 (familyPairVector B) := singlePair2 B _hB
    _ = _ := by norm_num [singlePairValue2, nodeValue2, Sparse.eval, mixedVector]

theorem sound3 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3 node3Labels = Sparse.eval nodeValue3 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue3 (familyPairVector B) := singlePair3 B _hB
    _ = _ := by norm_num [singlePairValue3, nodeValue3, Sparse.eval, mixedVector]; ring

theorem sound4 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4 node4Labels = Sparse.eval nodeValue4 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue4 (familyPairVector B) := singlePair4 B _hB
    _ = _ := by norm_num [singlePairValue4, nodeValue4, Sparse.eval, mixedVector]; ring

theorem sound5 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5 node5Labels = Sparse.eval nodeValue5 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue5 (familyPairVector B) := singlePair5 B _hB
    _ = _ := by norm_num [singlePairValue5, nodeValue5, Sparse.eval, mixedVector]

theorem sound6 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node6 node6Labels = Sparse.eval nodeValue6 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue6 (familyPairVector B) := singlePair6 B _hB
    _ = _ := by norm_num [singlePairValue6, nodeValue6, Sparse.eval, mixedVector]

theorem sound7 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node7 node7Labels = Sparse.eval nodeValue7 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue7 (familyPairVector B) := singlePair7 B _hB
    _ = _ := by norm_num [singlePairValue7, nodeValue7, Sparse.eval, mixedVector]

theorem sound8 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node8 node8Labels = Sparse.eval nodeValue8 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue8 (familyPairVector B) := singlePair8 B _hB
    _ = _ := by norm_num [singlePairValue8, nodeValue8, Sparse.eval, mixedVector]; ring

theorem sound9 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node9 node9Labels = Sparse.eval nodeValue9 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue9 (familyPairVector B) := singlePair9 B _hB
    _ = _ := by norm_num [singlePairValue9, nodeValue9, Sparse.eval, mixedVector]; ring

theorem sound10 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node10 node10Labels = Sparse.eval nodeValue10 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue10 (familyPairVector B) := singlePair10 B _hB
    _ = _ := by norm_num [singlePairValue10, nodeValue10, Sparse.eval, mixedVector]; ring

theorem sound11 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node11 node11Labels = Sparse.eval nodeValue11 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue11 (familyPairVector B) := singlePair11 B _hB
    _ = _ := by norm_num [singlePairValue11, nodeValue11, Sparse.eval, mixedVector]; ring

theorem sound12 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node12 node12Labels = Sparse.eval nodeValue12 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue12 (familyPairVector B) := singlePair12 B _hB
    _ = _ := by norm_num [singlePairValue12, nodeValue12, Sparse.eval, mixedVector]; ring

theorem sound13 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node13 node13Labels = Sparse.eval nodeValue13 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue13 (familyPairVector B) := singlePair13 B _hB
    _ = _ := by norm_num [singlePairValue13, nodeValue13, Sparse.eval, mixedVector]; ring

theorem sound14 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node14 node14Labels = Sparse.eval nodeValue14 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue14 (familyPairVector B) := singlePair14 B _hB
    _ = _ := by norm_num [singlePairValue14, nodeValue14, Sparse.eval, mixedVector]; ring

theorem sound15 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node15 node15Labels = Sparse.eval nodeValue15 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue15 (familyPairVector B) := singlePair15 B _hB
    _ = _ := by norm_num [singlePairValue15, nodeValue15, Sparse.eval, mixedVector]; ring

theorem sound16 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node16 node16Labels = Sparse.eval nodeValue16 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue16 (familyPairVector B) := singlePair16 B _hB
    _ = _ := by norm_num [singlePairValue16, nodeValue16, Sparse.eval, mixedVector]; ring

theorem sound17 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node17 node17Labels = Sparse.eval nodeValue17 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue17 (familyPairVector B) := singlePair17 B _hB
    _ = _ := by norm_num [singlePairValue17, nodeValue17, Sparse.eval, mixedVector]; ring

theorem sound18 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node18 node18Labels = Sparse.eval nodeValue18 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue18 (familyPairVector B) := singlePair18 B _hB
    _ = _ := by norm_num [singlePairValue18, nodeValue18, Sparse.eval, mixedVector]; ring

theorem sound19 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node19 node19Labels = Sparse.eval nodeValue19 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue19 (familyPairVector B) := singlePair19 B _hB
    _ = _ := by norm_num [singlePairValue19, nodeValue19, Sparse.eval, mixedVector]; ring

theorem sound20 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node20 node20Labels = Sparse.eval nodeValue20 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue20 (familyPairVector B) := singlePair20 B _hB
    _ = _ := by norm_num [singlePairValue20, nodeValue20, Sparse.eval, mixedVector]; ring

theorem sound21 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node21 node21Labels = Sparse.eval nodeValue21 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue21 (familyPairVector B) := singlePair21 B _hB
    _ = _ := by norm_num [singlePairValue21, nodeValue21, Sparse.eval, mixedVector]; ring

theorem sound22 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node22 node22Labels = Sparse.eval nodeValue22 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue22 (familyPairVector B) := singlePair22 B _hB
    _ = _ := by norm_num [singlePairValue22, nodeValue22, Sparse.eval, mixedVector]; ring

theorem sound23 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node23 node23Labels = Sparse.eval nodeValue23 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue23 (familyPairVector B) := singlePair23 B _hB
    _ = _ := by norm_num [singlePairValue23, nodeValue23, Sparse.eval, mixedVector]; ring

theorem sound24 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node24 node24Labels = Sparse.eval nodeValue24 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue24 (familyPairVector B) := singlePair24 B _hB
    _ = _ := by norm_num [singlePairValue24, nodeValue24, Sparse.eval, mixedVector]; ring

theorem sound25 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node25 node25Labels = Sparse.eval nodeValue25 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue25 (familyPairVector B) := singlePair25 B _hB
    _ = _ := by norm_num [singlePairValue25, nodeValue25, Sparse.eval, mixedVector]; ring

theorem sound26 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node26 node26Labels = Sparse.eval nodeValue26 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue26 (familyPairVector B) := singlePair26 B _hB
    _ = _ := by norm_num [singlePairValue26, nodeValue26, Sparse.eval, mixedVector]; ring

theorem sound27 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node27 node27Labels = Sparse.eval nodeValue27 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue27 (familyPairVector B) := singlePair27 B _hB
    _ = _ := by norm_num [singlePairValue27, nodeValue27, Sparse.eval, mixedVector]; ring

theorem sound28 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node28 node28Labels = Sparse.eval nodeValue28 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue28 (familyPairVector B) := singlePair28 B _hB
    _ = _ := by norm_num [singlePairValue28, nodeValue28, Sparse.eval, mixedVector]; ring

theorem sound29 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node29 node29Labels = Sparse.eval nodeValue29 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue29 (familyPairVector B) := singlePair29 B _hB
    _ = _ := by norm_num [singlePairValue29, nodeValue29, Sparse.eval, mixedVector]; ring

theorem sound30 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node30 node30Labels = Sparse.eval nodeValue30 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue30 (familyPairVector B) := singlePair30 B _hB
    _ = _ := by norm_num [singlePairValue30, nodeValue30, Sparse.eval, mixedVector]; ring

theorem sound31 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node31 node31Labels = Sparse.eval nodeValue31 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue31 (familyPairVector B) := singlePair31 B _hB
    _ = _ := by norm_num [singlePairValue31, nodeValue31, Sparse.eval, mixedVector]; ring

theorem sound32 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node32 node32Labels = Sparse.eval nodeValue32 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue32 (familyPairVector B) := singlePair32 B _hB
    _ = _ := by norm_num [singlePairValue32, nodeValue32, Sparse.eval, mixedVector]; ring

theorem sound33 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node33 node33Labels = Sparse.eval nodeValue33 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue33 (familyPairVector B) := singlePair33 B _hB
    _ = _ := by norm_num [singlePairValue33, nodeValue33, Sparse.eval, mixedVector]; ring

theorem sound34 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node34 node34Labels = Sparse.eval nodeValue34 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue34 (familyPairVector B) := singlePair34 B _hB
    _ = _ := by norm_num [singlePairValue34, nodeValue34, Sparse.eval, mixedVector]; ring

theorem sound35 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node35 node35Labels = Sparse.eval nodeValue35 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue35 (familyPairVector B) := singlePair35 B _hB
    _ = _ := by norm_num [singlePairValue35, nodeValue35, Sparse.eval, mixedVector]; ring

theorem sound36 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node36 node36Labels = Sparse.eval nodeValue36 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue36 (familyPairVector B) := singlePair36 B _hB
    _ = _ := by norm_num [singlePairValue36, nodeValue36, Sparse.eval, mixedVector]; ring

theorem sound37 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node37 node37Labels = Sparse.eval nodeValue37 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue37 (familyPairVector B) := singlePair37 B _hB
    _ = _ := by norm_num [singlePairValue37, nodeValue37, Sparse.eval, mixedVector]; ring

theorem sound38 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node38 node38Labels = Sparse.eval nodeValue38 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue38 (familyPairVector B) := singlePair38 B _hB
    _ = _ := by norm_num [singlePairValue38, nodeValue38, Sparse.eval, mixedVector]; ring

theorem sound39 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node39 node39Labels = Sparse.eval nodeValue39 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue39 (familyPairVector B) := singlePair39 B _hB
    _ = _ := by norm_num [singlePairValue39, nodeValue39, Sparse.eval, mixedVector]; ring

theorem sound40 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node40 node40Labels = Sparse.eval nodeValue40 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue40 (familyPairVector B) := singlePair40 B _hB
    _ = _ := by norm_num [singlePairValue40, nodeValue40, Sparse.eval, mixedVector]; ring

theorem sound41 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node41 node41Labels = Sparse.eval nodeValue41 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue41 (familyPairVector B) := singlePair41 B _hB
    _ = _ := by norm_num [singlePairValue41, nodeValue41, Sparse.eval, mixedVector]; ring

theorem sound42 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node42 node42Labels = Sparse.eval nodeValue42 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue42 (familyPairVector B) := singlePair42 B _hB
    _ = _ := by norm_num [singlePairValue42, nodeValue42, Sparse.eval, mixedVector]; ring

theorem sound43 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node43 node43Labels = Sparse.eval nodeValue43 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue43 (familyPairVector B) := singlePair43 B _hB
    _ = _ := by norm_num [singlePairValue43, nodeValue43, Sparse.eval, mixedVector]; ring

theorem sound44 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node44 node44Labels = Sparse.eval nodeValue44 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue44 (familyPairVector B) := singlePair44 B _hB
    _ = _ := by norm_num [singlePairValue44, nodeValue44, Sparse.eval, mixedVector]; ring

theorem sound45 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node45 node45Labels = Sparse.eval nodeValue45 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue45 (familyPairVector B) := singlePair45 B _hB
    _ = _ := by norm_num [singlePairValue45, nodeValue45, Sparse.eval, mixedVector]; ring

theorem sound46 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node46 node46Labels = Sparse.eval nodeValue46 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue46 (familyPairVector B) := singlePair46 B _hB
    _ = _ := by norm_num [singlePairValue46, nodeValue46, Sparse.eval, mixedVector]; ring

theorem sound47 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node47 node47Labels = Sparse.eval nodeValue47 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue47 (familyPairVector B) := singlePair47 B _hB
    _ = _ := by norm_num [singlePairValue47, nodeValue47, Sparse.eval, mixedVector]; ring

theorem sound48 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node48 node48Labels = Sparse.eval nodeValue48 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue48 (familyPairVector B) := singlePair48 B _hB
    _ = _ := by norm_num [singlePairValue48, nodeValue48, Sparse.eval, mixedVector]; ring

theorem sound49 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node49 node49Labels = Sparse.eval nodeValue49 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue49 (familyPairVector B) := singlePair49 B _hB
    _ = _ := by norm_num [singlePairValue49, nodeValue49, Sparse.eval, mixedVector]; ring

theorem sound50 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node50 node50Labels = Sparse.eval nodeValue50 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue50 (familyPairVector B) := singlePair50 B _hB
    _ = _ := by norm_num [singlePairValue50, nodeValue50, Sparse.eval, mixedVector]; ring

theorem sound51 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node51 node51Labels = Sparse.eval nodeValue51 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue51 (familyPairVector B) := singlePair51 B _hB
    _ = _ := by norm_num [singlePairValue51, nodeValue51, Sparse.eval, mixedVector]; ring

theorem sound52 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node52 node52Labels = Sparse.eval nodeValue52 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue52 (familyPairVector B) := singlePair52 B _hB
    _ = _ := by norm_num [singlePairValue52, nodeValue52, Sparse.eval, mixedVector]; ring

theorem sound53 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node53 node53Labels = Sparse.eval nodeValue53 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue53 (familyPairVector B) := singlePair53 B _hB
    _ = _ := by norm_num [singlePairValue53, nodeValue53, Sparse.eval, mixedVector]; ring

theorem sound54 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node54 node54Labels = Sparse.eval nodeValue54 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue54 (familyPairVector B) := singlePair54 B _hB
    _ = _ := by norm_num [singlePairValue54, nodeValue54, Sparse.eval, mixedVector]; ring

theorem sound55 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node55 node55Labels = Sparse.eval nodeValue55 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue55 (familyPairVector B) := singlePair55 B _hB
    _ = _ := by norm_num [singlePairValue55, nodeValue55, Sparse.eval, mixedVector]; ring

theorem sound56 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node56 node56Labels = Sparse.eval nodeValue56 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue56 (familyPairVector B) := singlePair56 B _hB
    _ = _ := by norm_num [singlePairValue56, nodeValue56, Sparse.eval, mixedVector]; ring

theorem sound57 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node57 node57Labels = Sparse.eval nodeValue57 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue57 (familyPairVector B) := singlePair57 B _hB
    _ = _ := by norm_num [singlePairValue57, nodeValue57, Sparse.eval, mixedVector]; ring

theorem sound58 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node58 node58Labels = Sparse.eval nodeValue58 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue58 (familyPairVector B) := singlePair58 B _hB
    _ = _ := by norm_num [singlePairValue58, nodeValue58, Sparse.eval, mixedVector]; ring

theorem sound59 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node59 node59Labels = Sparse.eval nodeValue59 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue59 (familyPairVector B) := singlePair59 B _hB
    _ = _ := by norm_num [singlePairValue59, nodeValue59, Sparse.eval, mixedVector]; ring

theorem sound60 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node60 node60Labels = Sparse.eval nodeValue60 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue60 (familyPairVector B) := singlePair60 B _hB
    _ = _ := by norm_num [singlePairValue60, nodeValue60, Sparse.eval, mixedVector]; ring

theorem sound61 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node61 node61Labels = Sparse.eval nodeValue61 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue61 (familyPairVector B) := singlePair61 B _hB
    _ = _ := by norm_num [singlePairValue61, nodeValue61, Sparse.eval, mixedVector]; ring

theorem sound62 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node62 node62Labels = Sparse.eval nodeValue62 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue62 (familyPairVector B) := singlePair62 B _hB
    _ = _ := by norm_num [singlePairValue62, nodeValue62, Sparse.eval, mixedVector]; ring

theorem sound63 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node63 node63Labels = Sparse.eval nodeValue63 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue63 (familyPairVector B) := singlePair63 B _hB
    _ = _ := by norm_num [singlePairValue63, nodeValue63, Sparse.eval, mixedVector]; ring

end MUB6.Certificate.MixedSemantics

end OAI
