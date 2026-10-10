import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic93
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources55

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1488 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1488 (mixedVector B) = 0 := by
  have h941 : mixedVector B (Sum.inr 941) = Sparse.eval nodeValue941 (mixedVector B) := by
    change mixedMoment B node941 node941Labels = _
    exact sound941 B hB hF
  have h943 : mixedVector B (Sum.inr 943) = Sparse.eval nodeValue943 (mixedVector B) := by
    change mixedMoment B node943 node943Labels = _
    exact sound943 B hB hF
  have h946 : mixedVector B (Sum.inr 946) = Sparse.eval nodeValue946 (mixedVector B) := by
    change mixedMoment B node946 node946Labels = _
    exact sound946 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1743, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h941, h943, h946, h1040, h2106, h4084, reducedSource1488] using sourceEq1743 B hB

theorem rowSound1488 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1488 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1488, numericCheck1488, reducedZero1488 B hB hF, mul_zero]

theorem reducedZero1489 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1489 (mixedVector B) = 0 := by
  have h577 : mixedVector B (Sum.inr 577) = Sparse.eval nodeValue577 (mixedVector B) := by
    change mixedMoment B node577 node577Labels = _
    exact sound577 B hB hF
  have h941 : mixedVector B (Sum.inr 941) = Sparse.eval nodeValue941 (mixedVector B) := by
    change mixedMoment B node941 node941Labels = _
    exact sound941 B hB hF
  have h1038 : mixedVector B (Sum.inr 1038) = Sparse.eval nodeValue1038 (mixedVector B) := by
    change mixedMoment B node1038 node1038Labels = _
    exact sound1038 B hB hF
  have h1040 : mixedVector B (Sum.inr 1040) = Sparse.eval nodeValue1040 (mixedVector B) := by
    change mixedMoment B node1040 node1040Labels = _
    exact sound1040 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1744, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h577, h941, h1038, h1040, h4084, reducedSource1489] using sourceEq1744 B hB

theorem rowSound1489 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1489 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1489, numericCheck1489, reducedZero1489 B hB hF, mul_zero]

theorem reducedZero1490 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1490 (mixedVector B) = 0 := by
  have h4098 : mixedVector B (Sum.inr 4098) = Sparse.eval nodeValue4098 (mixedVector B) := by
    change mixedMoment B node4098 node4098Labels = _
    exact sound4098 B hB hF
  have h4099 : mixedVector B (Sum.inr 4099) = Sparse.eval nodeValue4099 (mixedVector B) := by
    change mixedMoment B node4099 node4099Labels = _
    exact sound4099 B hB hF
  have h4102 : mixedVector B (Sum.inr 4102) = Sparse.eval nodeValue4102 (mixedVector B) := by
    change mixedMoment B node4102 node4102Labels = _
    exact sound4102 B hB hF
  have h4115 : mixedVector B (Sum.inr 4115) = Sparse.eval nodeValue4115 (mixedVector B) := by
    change mixedMoment B node4115 node4115Labels = _
    exact sound4115 B hB hF
  have h4286 : mixedVector B (Sum.inr 4286) = Sparse.eval nodeValue4286 (mixedVector B) := by
    change mixedMoment B node4286 node4286Labels = _
    exact sound4286 B hB hF
  have h4288 : mixedVector B (Sum.inr 4288) = Sparse.eval nodeValue4288 (mixedVector B) := by
    change mixedMoment B node4288 node4288Labels = _
    exact sound4288 B hB hF
  have h4298 : mixedVector B (Sum.inr 4298) = Sparse.eval nodeValue4298 (mixedVector B) := by
    change mixedMoment B node4298 node4298Labels = _
    exact sound4298 B hB hF
  have h4341 : mixedVector B (Sum.inr 4341) = Sparse.eval nodeValue4341 (mixedVector B) := by
    change mixedMoment B node4341 node4341Labels = _
    exact sound4341 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4349 : mixedVector B (Sum.inr 4349) = Sparse.eval nodeValue4349 (mixedVector B) := by
    change mixedMoment B node4349 node4349Labels = _
    exact sound4349 B hB hF
  have h4396 : mixedVector B (Sum.inr 4396) = Sparse.eval nodeValue4396 (mixedVector B) := by
    change mixedMoment B node4396 node4396Labels = _
    exact sound4396 B hB hF
  have h4398 : mixedVector B (Sum.inr 4398) = Sparse.eval nodeValue4398 (mixedVector B) := by
    change mixedMoment B node4398 node4398Labels = _
    exact sound4398 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4419 : mixedVector B (Sum.inr 4419) = Sparse.eval nodeValue4419 (mixedVector B) := by
    change mixedMoment B node4419 node4419Labels = _
    exact sound4419 B hB hF
  have h4456 : mixedVector B (Sum.inr 4456) = Sparse.eval nodeValue4456 (mixedVector B) := by
    change mixedMoment B node4456 node4456Labels = _
    exact sound4456 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4495 : mixedVector B (Sum.inr 4495) = Sparse.eval nodeValue4495 (mixedVector B) := by
    change mixedMoment B node4495 node4495Labels = _
    exact sound4495 B hB hF
  have h5072 : mixedVector B (Sum.inr 5072) = Sparse.eval nodeValue5072 (mixedVector B) := by
    change mixedMoment B node5072 node5072Labels = _
    exact sound5072 B hB hF
  have h5168 : mixedVector B (Sum.inr 5168) = Sparse.eval nodeValue5168 (mixedVector B) := by
    change mixedMoment B node5168 node5168Labels = _
    exact sound5168 B hB hF
  have h5258 : mixedVector B (Sum.inr 5258) = Sparse.eval nodeValue5258 (mixedVector B) := by
    change mixedMoment B node5258 node5258Labels = _
    exact sound5258 B hB hF
  have h5292 : mixedVector B (Sum.inr 5292) = Sparse.eval nodeValue5292 (mixedVector B) := by
    change mixedMoment B node5292 node5292Labels = _
    exact sound5292 B hB hF
  simpa only [sourceForm1745, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4098, h4099, h4102, h4115, h4286, h4288, h4298, h4341, h4343, h4349, h4396, h4398, h4404, h4419, h4456, h4458, h4495, h5072, h5168, h5258, h5292, reducedSource1490] using sourceEq1745 B hB

theorem rowSound1490 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1490 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1490, numericCheck1490, reducedZero1490 B hB hF, mul_zero]

theorem reducedZero1491 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1491 (mixedVector B) = 0 := by
  have h535 : mixedVector B (Sum.inr 535) = Sparse.eval nodeValue535 (mixedVector B) := by
    change mixedMoment B node535 node535Labels = _
    exact sound535 B hB hF
  have h536 : mixedVector B (Sum.inr 536) = Sparse.eval nodeValue536 (mixedVector B) := by
    change mixedMoment B node536 node536Labels = _
    exact sound536 B hB hF
  have h539 : mixedVector B (Sum.inr 539) = Sparse.eval nodeValue539 (mixedVector B) := by
    change mixedMoment B node539 node539Labels = _
    exact sound539 B hB hF
  have h552 : mixedVector B (Sum.inr 552) = Sparse.eval nodeValue552 (mixedVector B) := by
    change mixedMoment B node552 node552Labels = _
    exact sound552 B hB hF
  have h864 : mixedVector B (Sum.inr 864) = Sparse.eval nodeValue864 (mixedVector B) := by
    change mixedMoment B node864 node864Labels = _
    exact sound864 B hB hF
  have h866 : mixedVector B (Sum.inr 866) = Sparse.eval nodeValue866 (mixedVector B) := by
    change mixedMoment B node866 node866Labels = _
    exact sound866 B hB hF
  have h876 : mixedVector B (Sum.inr 876) = Sparse.eval nodeValue876 (mixedVector B) := by
    change mixedMoment B node876 node876Labels = _
    exact sound876 B hB hF
  have h919 : mixedVector B (Sum.inr 919) = Sparse.eval nodeValue919 (mixedVector B) := by
    change mixedMoment B node919 node919Labels = _
    exact sound919 B hB hF
  have h921 : mixedVector B (Sum.inr 921) = Sparse.eval nodeValue921 (mixedVector B) := by
    change mixedMoment B node921 node921Labels = _
    exact sound921 B hB hF
  have h927 : mixedVector B (Sum.inr 927) = Sparse.eval nodeValue927 (mixedVector B) := by
    change mixedMoment B node927 node927Labels = _
    exact sound927 B hB hF
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1039 : mixedVector B (Sum.inr 1039) = Sparse.eval nodeValue1039 (mixedVector B) := by
    change mixedMoment B node1039 node1039Labels = _
    exact sound1039 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h2594 : mixedVector B (Sum.inr 2594) = Sparse.eval nodeValue2594 (mixedVector B) := by
    change mixedMoment B node2594 node2594Labels = _
    exact sound2594 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2766 : mixedVector B (Sum.inr 2766) = Sparse.eval nodeValue2766 (mixedVector B) := by
    change mixedMoment B node2766 node2766Labels = _
    exact sound2766 B hB hF
  simpa only [sourceForm1746, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h535, h536, h539, h552, h864, h866, h876, h919, h921, h927, h977, h979, h985, h1000, h1039, h1041, h1079, h2479, h2594, h2722, h2766, reducedSource1491] using sourceEq1746 B hB

theorem rowSound1491 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1491 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1491, numericCheck1491, reducedZero1491 B hB hF, mul_zero]

theorem reducedZero1492 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1492 (mixedVector B) = 0 := by
  have h4248 : mixedVector B (Sum.inr 4248) = Sparse.eval nodeValue4248 (mixedVector B) := by
    change mixedMoment B node4248 node4248Labels = _
    exact sound4248 B hB hF
  have h4251 : mixedVector B (Sum.inr 4251) = Sparse.eval nodeValue4251 (mixedVector B) := by
    change mixedMoment B node4251 node4251Labels = _
    exact sound4251 B hB hF
  have h4255 : mixedVector B (Sum.inr 4255) = Sparse.eval nodeValue4255 (mixedVector B) := by
    change mixedMoment B node4255 node4255Labels = _
    exact sound4255 B hB hF
  have h4264 : mixedVector B (Sum.inr 4264) = Sparse.eval nodeValue4264 (mixedVector B) := by
    change mixedMoment B node4264 node4264Labels = _
    exact sound4264 B hB hF
  have h4395 : mixedVector B (Sum.inr 4395) = Sparse.eval nodeValue4395 (mixedVector B) := by
    change mixedMoment B node4395 node4395Labels = _
    exact sound4395 B hB hF
  have h4396 : mixedVector B (Sum.inr 4396) = Sparse.eval nodeValue4396 (mixedVector B) := by
    change mixedMoment B node4396 node4396Labels = _
    exact sound4396 B hB hF
  have h4406 : mixedVector B (Sum.inr 4406) = Sparse.eval nodeValue4406 (mixedVector B) := by
    change mixedMoment B node4406 node4406Labels = _
    exact sound4406 B hB hF
  have h4435 : mixedVector B (Sum.inr 4435) = Sparse.eval nodeValue4435 (mixedVector B) := by
    change mixedMoment B node4435 node4435Labels = _
    exact sound4435 B hB hF
  have h4438 : mixedVector B (Sum.inr 4438) = Sparse.eval nodeValue4438 (mixedVector B) := by
    change mixedMoment B node4438 node4438Labels = _
    exact sound4438 B hB hF
  have h4450 : mixedVector B (Sum.inr 4450) = Sparse.eval nodeValue4450 (mixedVector B) := by
    change mixedMoment B node4450 node4450Labels = _
    exact sound4450 B hB hF
  have h4452 : mixedVector B (Sum.inr 4452) = Sparse.eval nodeValue4452 (mixedVector B) := by
    change mixedMoment B node4452 node4452Labels = _
    exact sound4452 B hB hF
  have h4457 : mixedVector B (Sum.inr 4457) = Sparse.eval nodeValue4457 (mixedVector B) := by
    change mixedMoment B node4457 node4457Labels = _
    exact sound4457 B hB hF
  have h4458 : mixedVector B (Sum.inr 4458) = Sparse.eval nodeValue4458 (mixedVector B) := by
    change mixedMoment B node4458 node4458Labels = _
    exact sound4458 B hB hF
  have h4470 : mixedVector B (Sum.inr 4470) = Sparse.eval nodeValue4470 (mixedVector B) := by
    change mixedMoment B node4470 node4470Labels = _
    exact sound4470 B hB hF
  have h4474 : mixedVector B (Sum.inr 4474) = Sparse.eval nodeValue4474 (mixedVector B) := by
    change mixedMoment B node4474 node4474Labels = _
    exact sound4474 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4589 : mixedVector B (Sum.inr 4589) = Sparse.eval nodeValue4589 (mixedVector B) := by
    change mixedMoment B node4589 node4589Labels = _
    exact sound4589 B hB hF
  have h4606 : mixedVector B (Sum.inr 4606) = Sparse.eval nodeValue4606 (mixedVector B) := by
    change mixedMoment B node4606 node4606Labels = _
    exact sound4606 B hB hF
  have h4607 : mixedVector B (Sum.inr 4607) = Sparse.eval nodeValue4607 (mixedVector B) := by
    change mixedMoment B node4607 node4607Labels = _
    exact sound4607 B hB hF
  have h4623 : mixedVector B (Sum.inr 4623) = Sparse.eval nodeValue4623 (mixedVector B) := by
    change mixedMoment B node4623 node4623Labels = _
    exact sound4623 B hB hF
  simpa only [sourceForm1747, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4248, h4251, h4255, h4264, h4395, h4396, h4406, h4435, h4438, h4450, h4452, h4457, h4458, h4470, h4474, h4496, h4498, h4589, h4606, h4607, h4623, reducedSource1492] using sourceEq1747 B hB

theorem rowSound1492 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1492 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1492, numericCheck1492, reducedZero1492 B hB hF, mul_zero]

theorem reducedZero1493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1493 (mixedVector B) = 0 := by
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h1305 : mixedVector B (Sum.inr 1305) = Sparse.eval nodeValue1305 (mixedVector B) := by
    change mixedMoment B node1305 node1305Labels = _
    exact sound1305 B hB hF
  have h1360 : mixedVector B (Sum.inr 1360) = Sparse.eval nodeValue1360 (mixedVector B) := by
    change mixedMoment B node1360 node1360Labels = _
    exact sound1360 B hB hF
  have h1370 : mixedVector B (Sum.inr 1370) = Sparse.eval nodeValue1370 (mixedVector B) := by
    change mixedMoment B node1370 node1370Labels = _
    exact sound1370 B hB hF
  have h1371 : mixedVector B (Sum.inr 1371) = Sparse.eval nodeValue1371 (mixedVector B) := by
    change mixedMoment B node1371 node1371Labels = _
    exact sound1371 B hB hF
  have h1386 : mixedVector B (Sum.inr 1386) = Sparse.eval nodeValue1386 (mixedVector B) := by
    change mixedMoment B node1386 node1386Labels = _
    exact sound1386 B hB hF
  have h1387 : mixedVector B (Sum.inr 1387) = Sparse.eval nodeValue1387 (mixedVector B) := by
    change mixedMoment B node1387 node1387Labels = _
    exact sound1387 B hB hF
  have h1396 : mixedVector B (Sum.inr 1396) = Sparse.eval nodeValue1396 (mixedVector B) := by
    change mixedMoment B node1396 node1396Labels = _
    exact sound1396 B hB hF
  have h1398 : mixedVector B (Sum.inr 1398) = Sparse.eval nodeValue1398 (mixedVector B) := by
    change mixedMoment B node1398 node1398Labels = _
    exact sound1398 B hB hF
  have h1411 : mixedVector B (Sum.inr 1411) = Sparse.eval nodeValue1411 (mixedVector B) := by
    change mixedMoment B node1411 node1411Labels = _
    exact sound1411 B hB hF
  have h1412 : mixedVector B (Sum.inr 1412) = Sparse.eval nodeValue1412 (mixedVector B) := by
    change mixedMoment B node1412 node1412Labels = _
    exact sound1412 B hB hF
  have h1414 : mixedVector B (Sum.inr 1414) = Sparse.eval nodeValue1414 (mixedVector B) := by
    change mixedMoment B node1414 node1414Labels = _
    exact sound1414 B hB hF
  have h1415 : mixedVector B (Sum.inr 1415) = Sparse.eval nodeValue1415 (mixedVector B) := by
    change mixedMoment B node1415 node1415Labels = _
    exact sound1415 B hB hF
  have h1448 : mixedVector B (Sum.inr 1448) = Sparse.eval nodeValue1448 (mixedVector B) := by
    change mixedMoment B node1448 node1448Labels = _
    exact sound1448 B hB hF
  have h1451 : mixedVector B (Sum.inr 1451) = Sparse.eval nodeValue1451 (mixedVector B) := by
    change mixedMoment B node1451 node1451Labels = _
    exact sound1451 B hB hF
  have h1470 : mixedVector B (Sum.inr 1470) = Sparse.eval nodeValue1470 (mixedVector B) := by
    change mixedMoment B node1470 node1470Labels = _
    exact sound1470 B hB hF
  have h1477 : mixedVector B (Sum.inr 1477) = Sparse.eval nodeValue1477 (mixedVector B) := by
    change mixedMoment B node1477 node1477Labels = _
    exact sound1477 B hB hF
  have h1478 : mixedVector B (Sum.inr 1478) = Sparse.eval nodeValue1478 (mixedVector B) := by
    change mixedMoment B node1478 node1478Labels = _
    exact sound1478 B hB hF
  have h1483 : mixedVector B (Sum.inr 1483) = Sparse.eval nodeValue1483 (mixedVector B) := by
    change mixedMoment B node1483 node1483Labels = _
    exact sound1483 B hB hF
  simpa only [sourceForm1748, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1216, h1240, h1241, h1305, h1360, h1370, h1371, h1386, h1387, h1396, h1398, h1411, h1412, h1414, h1415, h1448, h1451, h1470, h1477, h1478, h1483, reducedSource1493] using sourceEq1748 B hB

theorem rowSound1493 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1493 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1493, numericCheck1493, reducedZero1493 B hB hF, mul_zero]

theorem reducedZero1494 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1494 (mixedVector B) = 0 := by
  have h1033 : mixedVector B (Sum.inr 1033) = Sparse.eval nodeValue1033 (mixedVector B) := by
    change mixedMoment B node1033 node1033Labels = _
    exact sound1033 B hB hF
  have h2015 : mixedVector B (Sum.inr 2015) = Sparse.eval nodeValue2015 (mixedVector B) := by
    change mixedMoment B node2015 node2015Labels = _
    exact sound2015 B hB hF
  have h2099 : mixedVector B (Sum.inr 2099) = Sparse.eval nodeValue2099 (mixedVector B) := by
    change mixedMoment B node2099 node2099Labels = _
    exact sound2099 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2259 : mixedVector B (Sum.inr 2259) = Sparse.eval nodeValue2259 (mixedVector B) := by
    change mixedMoment B node2259 node2259Labels = _
    exact sound2259 B hB hF
  have h2261 : mixedVector B (Sum.inr 2261) = Sparse.eval nodeValue2261 (mixedVector B) := by
    change mixedMoment B node2261 node2261Labels = _
    exact sound2261 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1749, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1033, h2015, h2099, h2203, h2259, h2261, h4081, reducedSource1494] using sourceEq1749 B hB

theorem rowSound1494 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1494 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1494, numericCheck1494, reducedZero1494 B hB hF, mul_zero]

theorem reducedZero1495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1495 (mixedVector B) = 0 := by
  have h981 : mixedVector B (Sum.inr 981) = Sparse.eval nodeValue981 (mixedVector B) := by
    change mixedMoment B node981 node981Labels = _
    exact sound981 B hB hF
  have h1913 : mixedVector B (Sum.inr 1913) = Sparse.eval nodeValue1913 (mixedVector B) := by
    change mixedMoment B node1913 node1913Labels = _
    exact sound1913 B hB hF
  have h2078 : mixedVector B (Sum.inr 2078) = Sparse.eval nodeValue2078 (mixedVector B) := by
    change mixedMoment B node2078 node2078Labels = _
    exact sound2078 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h2196 : mixedVector B (Sum.inr 2196) = Sparse.eval nodeValue2196 (mixedVector B) := by
    change mixedMoment B node2196 node2196Labels = _
    exact sound2196 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1750, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h981, h1913, h2078, h2192, h2196, h2202, h4080, reducedSource1495] using sourceEq1750 B hB

theorem rowSound1495 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1495 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1495, numericCheck1495, reducedZero1495 B hB hF, mul_zero]

theorem reducedZero1496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1496 (mixedVector B) = 0 := by
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h978 : mixedVector B (Sum.inr 978) = Sparse.eval nodeValue978 (mixedVector B) := by
    change mixedMoment B node978 node978Labels = _
    exact sound978 B hB hF
  have h981 : mixedVector B (Sum.inr 981) = Sparse.eval nodeValue981 (mixedVector B) := by
    change mixedMoment B node981 node981Labels = _
    exact sound981 B hB hF
  have h998 : mixedVector B (Sum.inr 998) = Sparse.eval nodeValue998 (mixedVector B) := by
    change mixedMoment B node998 node998Labels = _
    exact sound998 B hB hF
  have h1032 : mixedVector B (Sum.inr 1032) = Sparse.eval nodeValue1032 (mixedVector B) := by
    change mixedMoment B node1032 node1032Labels = _
    exact sound1032 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1751, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h977, h978, h981, h998, h1032, h2202, h4080, reducedSource1496] using sourceEq1751 B hB

theorem rowSound1496 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1496 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1496, numericCheck1496, reducedZero1496 B hB hF, mul_zero]

theorem reducedZero1497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1497 (mixedVector B) = 0 := by
  have h978 : mixedVector B (Sum.inr 978) = Sparse.eval nodeValue978 (mixedVector B) := by
    change mixedMoment B node978 node978Labels = _
    exact sound978 B hB hF
  have h1909 : mixedVector B (Sum.inr 1909) = Sparse.eval nodeValue1909 (mixedVector B) := by
    change mixedMoment B node1909 node1909Labels = _
    exact sound1909 B hB hF
  have h2076 : mixedVector B (Sum.inr 2076) = Sparse.eval nodeValue2076 (mixedVector B) := by
    change mixedMoment B node2076 node2076Labels = _
    exact sound2076 B hB hF
  have h2195 : mixedVector B (Sum.inr 2195) = Sparse.eval nodeValue2195 (mixedVector B) := by
    change mixedMoment B node2195 node2195Labels = _
    exact sound2195 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1752, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h978, h1909, h2076, h2195, h2202, h2206, h4080, reducedSource1497] using sourceEq1752 B hB

theorem rowSound1497 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1497 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1497, numericCheck1497, reducedZero1497 B hB hF, mul_zero]

theorem reducedZero1498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1498 (mixedVector B) = 0 := by
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h1912 : mixedVector B (Sum.inr 1912) = Sparse.eval nodeValue1912 (mixedVector B) := by
    change mixedMoment B node1912 node1912Labels = _
    exact sound1912 B hB hF
  have h2077 : mixedVector B (Sum.inr 2077) = Sparse.eval nodeValue2077 (mixedVector B) := by
    change mixedMoment B node2077 node2077Labels = _
    exact sound2077 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1753, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h980, h1912, h2077, h2191, h2204, h4079, reducedSource1498] using sourceEq1753 B hB

theorem rowSound1498 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1498 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1498, numericCheck1498, reducedZero1498 B hB hF, mul_zero]

theorem reducedZero1499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1499 (mixedVector B) = 0 := by
  have h980 : mixedVector B (Sum.inr 980) = Sparse.eval nodeValue980 (mixedVector B) := by
    change mixedMoment B node980 node980Labels = _
    exact sound980 B hB hF
  have h1003 : mixedVector B (Sum.inr 1003) = Sparse.eval nodeValue1003 (mixedVector B) := by
    change mixedMoment B node1003 node1003Labels = _
    exact sound1003 B hB hF
  have h1034 : mixedVector B (Sum.inr 1034) = Sparse.eval nodeValue1034 (mixedVector B) := by
    change mixedMoment B node1034 node1034Labels = _
    exact sound1034 B hB hF
  have h2204 : mixedVector B (Sum.inr 2204) = Sparse.eval nodeValue2204 (mixedVector B) := by
    change mixedMoment B node2204 node2204Labels = _
    exact sound2204 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1756, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h980, h1003, h1034, h2204, h4079, reducedSource1499] using sourceEq1756 B hB

theorem rowSound1499 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1499 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1499, numericCheck1499, reducedZero1499 B hB hF, mul_zero]

theorem reducedZero1500 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1500 (mixedVector B) = 0 := by
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h1908 : mixedVector B (Sum.inr 1908) = Sparse.eval nodeValue1908 (mixedVector B) := by
    change mixedMoment B node1908 node1908Labels = _
    exact sound1908 B hB hF
  have h2075 : mixedVector B (Sum.inr 2075) = Sparse.eval nodeValue2075 (mixedVector B) := by
    change mixedMoment B node2075 node2075Labels = _
    exact sound2075 B hB hF
  have h2190 : mixedVector B (Sum.inr 2190) = Sparse.eval nodeValue2190 (mixedVector B) := by
    change mixedMoment B node2190 node2190Labels = _
    exact sound2190 B hB hF
  have h2202 : mixedVector B (Sum.inr 2202) = Sparse.eval nodeValue2202 (mixedVector B) := by
    change mixedMoment B node2202 node2202Labels = _
    exact sound2202 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1759, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h977, h1908, h2075, h2190, h2202, h2205, h4080, reducedSource1500] using sourceEq1759 B hB

theorem rowSound1500 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1500 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1500, numericCheck1500, reducedZero1500 B hB hF, mul_zero]

theorem reducedZero1501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1501 (mixedVector B) = 0 := by
  have h865 : mixedVector B (Sum.inr 865) = Sparse.eval nodeValue865 (mixedVector B) := by
    change mixedMoment B node865 node865Labels = _
    exact sound865 B hB hF
  have h866 : mixedVector B (Sum.inr 866) = Sparse.eval nodeValue866 (mixedVector B) := by
    change mixedMoment B node866 node866Labels = _
    exact sound866 B hB hF
  have h869 : mixedVector B (Sum.inr 869) = Sparse.eval nodeValue869 (mixedVector B) := by
    change mixedMoment B node869 node869Labels = _
    exact sound869 B hB hF
  have h878 : mixedVector B (Sum.inr 878) = Sparse.eval nodeValue878 (mixedVector B) := by
    change mixedMoment B node878 node878Labels = _
    exact sound878 B hB hF
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h1908 : mixedVector B (Sum.inr 1908) = Sparse.eval nodeValue1908 (mixedVector B) := by
    change mixedMoment B node1908 node1908Labels = _
    exact sound1908 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1761, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h865, h866, h869, h878, h977, h1908, h4080, reducedSource1501] using sourceEq1761 B hB

theorem rowSound1501 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1501 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1501, numericCheck1501, reducedZero1501 B hB hF, mul_zero]

theorem reducedZero1502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1502 (mixedVector B) = 0 := by
  have h699 : mixedVector B (Sum.inr 699) = Sparse.eval nodeValue699 (mixedVector B) := by
    change mixedMoment B node699 node699Labels = _
    exact sound699 B hB hF
  have h700 : mixedVector B (Sum.inr 700) = Sparse.eval nodeValue700 (mixedVector B) := by
    change mixedMoment B node700 node700Labels = _
    exact sound700 B hB hF
  have h703 : mixedVector B (Sum.inr 703) = Sparse.eval nodeValue703 (mixedVector B) := by
    change mixedMoment B node703 node703Labels = _
    exact sound703 B hB hF
  have h712 : mixedVector B (Sum.inr 712) = Sparse.eval nodeValue712 (mixedVector B) := by
    change mixedMoment B node712 node712Labels = _
    exact sound712 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h1597 : mixedVector B (Sum.inr 1597) = Sparse.eval nodeValue1597 (mixedVector B) := by
    change mixedMoment B node1597 node1597Labels = _
    exact sound1597 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1762, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h699, h700, h703, h712, h806, h1597, h4069, reducedSource1502] using sourceEq1762 B hB

theorem rowSound1502 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1502 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1502, numericCheck1502, reducedZero1502 B hB hF, mul_zero]

theorem reducedZero1503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1503 (mixedVector B) = 0 := by
  have h976 : mixedVector B (Sum.inr 976) = Sparse.eval nodeValue976 (mixedVector B) := by
    change mixedMoment B node976 node976Labels = _
    exact sound976 B hB hF
  have h1907 : mixedVector B (Sum.inr 1907) = Sparse.eval nodeValue1907 (mixedVector B) := by
    change mixedMoment B node1907 node1907Labels = _
    exact sound1907 B hB hF
  have h2074 : mixedVector B (Sum.inr 2074) = Sparse.eval nodeValue2074 (mixedVector B) := by
    change mixedMoment B node2074 node2074Labels = _
    exact sound2074 B hB hF
  have h2201 : mixedVector B (Sum.inr 2201) = Sparse.eval nodeValue2201 (mixedVector B) := by
    change mixedMoment B node2201 node2201Labels = _
    exact sound2201 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1763, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h976, h1907, h2074, h2201, h2203, h4081, reducedSource1503] using sourceEq1763 B hB

theorem rowSound1503 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1503 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1503, numericCheck1503, reducedZero1503 B hB hF, mul_zero]

theorem sourceRowsAt1488 : MixedData.sourceRows (1488 : Fin 2425) =
    MixedData.row1488 := by decide +kernel

theorem sourceRowsAt1489 : MixedData.sourceRows (1489 : Fin 2425) =
    MixedData.row1489 := by decide +kernel

theorem sourceRowsAt1490 : MixedData.sourceRows (1490 : Fin 2425) =
    MixedData.row1490 := by decide +kernel

theorem sourceRowsAt1491 : MixedData.sourceRows (1491 : Fin 2425) =
    MixedData.row1491 := by decide +kernel

theorem sourceRowsAt1492 : MixedData.sourceRows (1492 : Fin 2425) =
    MixedData.row1492 := by decide +kernel

theorem sourceRowsAt1493 : MixedData.sourceRows (1493 : Fin 2425) =
    MixedData.row1493 := by decide +kernel

theorem sourceRowsAt1494 : MixedData.sourceRows (1494 : Fin 2425) =
    MixedData.row1494 := by decide +kernel

theorem sourceRowsAt1495 : MixedData.sourceRows (1495 : Fin 2425) =
    MixedData.row1495 := by decide +kernel

theorem sourceRowsAt1496 : MixedData.sourceRows (1496 : Fin 2425) =
    MixedData.row1496 := by decide +kernel

theorem sourceRowsAt1497 : MixedData.sourceRows (1497 : Fin 2425) =
    MixedData.row1497 := by decide +kernel

theorem sourceRowsAt1498 : MixedData.sourceRows (1498 : Fin 2425) =
    MixedData.row1498 := by decide +kernel

theorem sourceRowsAt1499 : MixedData.sourceRows (1499 : Fin 2425) =
    MixedData.row1499 := by decide +kernel

theorem sourceRowsAt1500 : MixedData.sourceRows (1500 : Fin 2425) =
    MixedData.row1500 := by decide +kernel

theorem sourceRowsAt1501 : MixedData.sourceRows (1501 : Fin 2425) =
    MixedData.row1501 := by decide +kernel

theorem sourceRowsAt1502 : MixedData.sourceRows (1502 : Fin 2425) =
    MixedData.row1502 := by decide +kernel

theorem sourceRowsAt1503 : MixedData.sourceRows (1503 : Fin 2425) =
    MixedData.row1503 := by decide +kernel

theorem chunkSound93 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 93) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1488 ∨ k.val = 1489 ∨ k.val = 1490 ∨ k.val = 1491 ∨ k.val = 1492 ∨ k.val = 1493 ∨ k.val = 1494 ∨ k.val = 1495 ∨ k.val = 1496 ∨ k.val = 1497 ∨ k.val = 1498 ∨ k.val = 1499 ∨ k.val = 1500 ∨ k.val = 1501 ∨ k.val = 1502 ∨ k.val = 1503 := by omega
  rcases heq with h1488 | h1489 | h1490 | h1491 | h1492 | h1493 | h1494 | h1495 | h1496 | h1497 | h1498 | h1499 | h1500 | h1501 | h1502 | h1503
  · have he : k = (1488 : Fin 2425) := Fin.ext h1488
    subst k
    rw [sourceRowsAt1488]
    exact rowSound1488 B hB hF
  · have he : k = (1489 : Fin 2425) := Fin.ext h1489
    subst k
    rw [sourceRowsAt1489]
    exact rowSound1489 B hB hF
  · have he : k = (1490 : Fin 2425) := Fin.ext h1490
    subst k
    rw [sourceRowsAt1490]
    exact rowSound1490 B hB hF
  · have he : k = (1491 : Fin 2425) := Fin.ext h1491
    subst k
    rw [sourceRowsAt1491]
    exact rowSound1491 B hB hF
  · have he : k = (1492 : Fin 2425) := Fin.ext h1492
    subst k
    rw [sourceRowsAt1492]
    exact rowSound1492 B hB hF
  · have he : k = (1493 : Fin 2425) := Fin.ext h1493
    subst k
    rw [sourceRowsAt1493]
    exact rowSound1493 B hB hF
  · have he : k = (1494 : Fin 2425) := Fin.ext h1494
    subst k
    rw [sourceRowsAt1494]
    exact rowSound1494 B hB hF
  · have he : k = (1495 : Fin 2425) := Fin.ext h1495
    subst k
    rw [sourceRowsAt1495]
    exact rowSound1495 B hB hF
  · have he : k = (1496 : Fin 2425) := Fin.ext h1496
    subst k
    rw [sourceRowsAt1496]
    exact rowSound1496 B hB hF
  · have he : k = (1497 : Fin 2425) := Fin.ext h1497
    subst k
    rw [sourceRowsAt1497]
    exact rowSound1497 B hB hF
  · have he : k = (1498 : Fin 2425) := Fin.ext h1498
    subst k
    rw [sourceRowsAt1498]
    exact rowSound1498 B hB hF
  · have he : k = (1499 : Fin 2425) := Fin.ext h1499
    subst k
    rw [sourceRowsAt1499]
    exact rowSound1499 B hB hF
  · have he : k = (1500 : Fin 2425) := Fin.ext h1500
    subst k
    rw [sourceRowsAt1500]
    exact rowSound1500 B hB hF
  · have he : k = (1501 : Fin 2425) := Fin.ext h1501
    subst k
    rw [sourceRowsAt1501]
    exact rowSound1501 B hB hF
  · have he : k = (1502 : Fin 2425) := Fin.ext h1502
    subst k
    rw [sourceRowsAt1502]
    exact rowSound1502 B hB hF
  · have he : k = (1503 : Fin 2425) := Fin.ext h1503
    subst k
    rw [sourceRowsAt1503]
    exact rowSound1503 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
