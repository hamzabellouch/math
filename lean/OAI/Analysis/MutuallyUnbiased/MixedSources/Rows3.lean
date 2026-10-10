import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources2

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero48 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource48 (mixedVector B) = 0 := by
  have h2040 : mixedVector B (Sum.inr 2040) = Sparse.eval nodeValue2040 (mixedVector B) := by
    change mixedMoment B node2040 node2040Labels = _
    exact sound2040 B hB hF
  have h2041 : mixedVector B (Sum.inr 2041) = Sparse.eval nodeValue2041 (mixedVector B) := by
    change mixedMoment B node2041 node2041Labels = _
    exact sound2041 B hB hF
  have h2042 : mixedVector B (Sum.inr 2042) = Sparse.eval nodeValue2042 (mixedVector B) := by
    change mixedMoment B node2042 node2042Labels = _
    exact sound2042 B hB hF
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm54, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2040, h2041, h2042, h2055, h2284, h4085, reducedSource48] using sourceEq54 B hB

theorem rowSound48 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row48 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck48, numericCheck48, reducedZero48 B hB hF, mul_zero]

theorem reducedZero49 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource49 (mixedVector B) = 0 := by
  have h1068 : mixedVector B (Sum.inr 1068) = Sparse.eval nodeValue1068 (mixedVector B) := by
    change mixedMoment B node1068 node1068Labels = _
    exact sound1068 B hB hF
  have h2042 : mixedVector B (Sum.inr 2042) = Sparse.eval nodeValue2042 (mixedVector B) := by
    change mixedMoment B node2042 node2042Labels = _
    exact sound2042 B hB hF
  have h2284 : mixedVector B (Sum.inr 2284) = Sparse.eval nodeValue2284 (mixedVector B) := by
    change mixedMoment B node2284 node2284Labels = _
    exact sound2284 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm55, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1068, h2042, h2284, h4085, reducedSource49] using sourceEq55 B hB

theorem rowSound49 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row49 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck49, numericCheck49, reducedZero49 B hB hF, mul_zero]

theorem reducedZero50 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource50 (mixedVector B) = 0 := by
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h3619 : mixedVector B (Sum.inr 3619) = Sparse.eval nodeValue3619 (mixedVector B) := by
    change mixedMoment B node3619 node3619Labels = _
    exact sound3619 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm59, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2235, h3155, h3158, h3619, h4083, reducedSource50] using sourceEq59 B hB

theorem rowSound50 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row50 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck50, numericCheck50, reducedZero50 B hB hF, mul_zero]

theorem reducedZero51 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource51 (mixedVector B) = 0 := by
  have h1014 : mixedVector B (Sum.inr 1014) = Sparse.eval nodeValue1014 (mixedVector B) := by
    change mixedMoment B node1014 node1014Labels = _
    exact sound1014 B hB hF
  have h1016 : mixedVector B (Sum.inr 1016) = Sparse.eval nodeValue1016 (mixedVector B) := by
    change mixedMoment B node1016 node1016Labels = _
    exact sound1016 B hB hF
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm60, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1014, h1016, h1024, h2235, h4083, reducedSource51] using sourceEq60 B hB

theorem rowSound51 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row51 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck51, numericCheck51, reducedZero51 B hB hF, mul_zero]

theorem reducedZero52 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource52 (mixedVector B) = 0 := by
  have h1014 : mixedVector B (Sum.inr 1014) = Sparse.eval nodeValue1014 (mixedVector B) := by
    change mixedMoment B node1014 node1014Labels = _
    exact sound1014 B hB hF
  have h2083 : mixedVector B (Sum.inr 2083) = Sparse.eval nodeValue2083 (mixedVector B) := by
    change mixedMoment B node2083 node2083Labels = _
    exact sound2083 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm61, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1014, h2083, h2233, h2235, h4083, reducedSource52] using sourceEq61 B hB

theorem rowSound52 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row52 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck52, numericCheck52, reducedZero52 B hB hF, mul_zero]

theorem reducedZero53 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource53 (mixedVector B) = 0 := by
  have h1457 : mixedVector B (Sum.inr 1457) = Sparse.eval nodeValue1457 (mixedVector B) := by
    change mixedMoment B node1457 node1457Labels = _
    exact sound1457 B hB hF
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h3155 : mixedVector B (Sum.inr 3155) = Sparse.eval nodeValue3155 (mixedVector B) := by
    change mixedMoment B node3155 node3155Labels = _
    exact sound3155 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm62, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1457, h2010, h2235, h3155, h4083, reducedSource53] using sourceEq62 B hB

theorem rowSound53 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row53 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck53, numericCheck53, reducedZero53 B hB hF, mul_zero]

theorem reducedZero54 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource54 (mixedVector B) = 0 := by
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h2010 : mixedVector B (Sum.inr 2010) = Sparse.eval nodeValue2010 (mixedVector B) := by
    change mixedMoment B node2010 node2010Labels = _
    exact sound2010 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm63, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1024, h2010, h2092, h2235, h2245, h4083, reducedSource54] using sourceEq63 B hB

theorem rowSound54 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row54 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck54, numericCheck54, reducedZero54 B hB hF, mul_zero]

theorem reducedZero55 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource55 (mixedVector B) = 0 := by
  have h1460 : mixedVector B (Sum.inr 1460) = Sparse.eval nodeValue1460 (mixedVector B) := by
    change mixedMoment B node1460 node1460Labels = _
    exact sound1460 B hB hF
  have h2083 : mixedVector B (Sum.inr 2083) = Sparse.eval nodeValue2083 (mixedVector B) := by
    change mixedMoment B node2083 node2083Labels = _
    exact sound2083 B hB hF
  have h2092 : mixedVector B (Sum.inr 2092) = Sparse.eval nodeValue2092 (mixedVector B) := by
    change mixedMoment B node2092 node2092Labels = _
    exact sound2092 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm64, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1460, h2083, h2092, h2235, h3158, h4083, reducedSource55] using sourceEq64 B hB

theorem rowSound55 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row55 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck55, numericCheck55, reducedZero55 B hB hF, mul_zero]

theorem reducedZero56 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource56 (mixedVector B) = 0 := by
  have h1016 : mixedVector B (Sum.inr 1016) = Sparse.eval nodeValue1016 (mixedVector B) := by
    change mixedMoment B node1016 node1016Labels = _
    exact sound1016 B hB hF
  have h1457 : mixedVector B (Sum.inr 1457) = Sparse.eval nodeValue1457 (mixedVector B) := by
    change mixedMoment B node1457 node1457Labels = _
    exact sound1457 B hB hF
  have h1460 : mixedVector B (Sum.inr 1460) = Sparse.eval nodeValue1460 (mixedVector B) := by
    change mixedMoment B node1460 node1460Labels = _
    exact sound1460 B hB hF
  have h2235 : mixedVector B (Sum.inr 2235) = Sparse.eval nodeValue2235 (mixedVector B) := by
    change mixedMoment B node2235 node2235Labels = _
    exact sound2235 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm65, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1016, h1457, h1460, h2235, h4083, reducedSource56] using sourceEq65 B hB

theorem rowSound56 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row56 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck56, numericCheck56, reducedZero56 B hB hF, mul_zero]

theorem reducedZero57 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource57 (mixedVector B) = 0 := by
  have h1078 : mixedVector B (Sum.inr 1078) = Sparse.eval nodeValue1078 (mixedVector B) := by
    change mixedMoment B node1078 node1078Labels = _
    exact sound1078 B hB hF
  have h2050 : mixedVector B (Sum.inr 2050) = Sparse.eval nodeValue2050 (mixedVector B) := by
    change mixedMoment B node2050 node2050Labels = _
    exact sound2050 B hB hF
  have h2283 : mixedVector B (Sum.inr 2283) = Sparse.eval nodeValue2283 (mixedVector B) := by
    change mixedMoment B node2283 node2283Labels = _
    exact sound2283 B hB hF
  have h2290 : mixedVector B (Sum.inr 2290) = Sparse.eval nodeValue2290 (mixedVector B) := by
    change mixedMoment B node2290 node2290Labels = _
    exact sound2290 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm68, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1078, h2050, h2283, h2290, h4085, reducedSource57] using sourceEq68 B hB

theorem rowSound57 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row57 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck57, numericCheck57, reducedZero57 B hB hF, mul_zero]

theorem reducedZero58 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource58 (mixedVector B) = 0 := by
  have h991 : mixedVector B (Sum.inr 991) = Sparse.eval nodeValue991 (mixedVector B) := by
    change mixedMoment B node991 node991Labels = _
    exact sound991 B hB hF
  have h994 : mixedVector B (Sum.inr 994) = Sparse.eval nodeValue994 (mixedVector B) := by
    change mixedMoment B node994 node994Labels = _
    exact sound994 B hB hF
  have h1010 : mixedVector B (Sum.inr 1010) = Sparse.eval nodeValue1010 (mixedVector B) := by
    change mixedMoment B node1010 node1010Labels = _
    exact sound1010 B hB hF
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h1181 : mixedVector B (Sum.inr 1181) = Sparse.eval nodeValue1181 (mixedVector B) := by
    change mixedMoment B node1181 node1181Labels = _
    exact sound1181 B hB hF
  have h1191 : mixedVector B (Sum.inr 1191) = Sparse.eval nodeValue1191 (mixedVector B) := by
    change mixedMoment B node1191 node1191Labels = _
    exact sound1191 B hB hF
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h2393 : mixedVector B (Sum.inr 2393) = Sparse.eval nodeValue2393 (mixedVector B) := by
    change mixedMoment B node2393 node2393Labels = _
    exact sound2393 B hB hF
  have h2408 : mixedVector B (Sum.inr 2408) = Sparse.eval nodeValue2408 (mixedVector B) := by
    change mixedMoment B node2408 node2408Labels = _
    exact sound2408 B hB hF
  have h2454 : mixedVector B (Sum.inr 2454) = Sparse.eval nodeValue2454 (mixedVector B) := by
    change mixedMoment B node2454 node2454Labels = _
    exact sound2454 B hB hF
  have h2465 : mixedVector B (Sum.inr 2465) = Sparse.eval nodeValue2465 (mixedVector B) := by
    change mixedMoment B node2465 node2465Labels = _
    exact sound2465 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2640 : mixedVector B (Sum.inr 2640) = Sparse.eval nodeValue2640 (mixedVector B) := by
    change mixedMoment B node2640 node2640Labels = _
    exact sound2640 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2776 : mixedVector B (Sum.inr 2776) = Sparse.eval nodeValue2776 (mixedVector B) := by
    change mixedMoment B node2776 node2776Labels = _
    exact sound2776 B hB hF
  have h3039 : mixedVector B (Sum.inr 3039) = Sparse.eval nodeValue3039 (mixedVector B) := by
    change mixedMoment B node3039 node3039Labels = _
    exact sound3039 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3110 : mixedVector B (Sum.inr 3110) = Sparse.eval nodeValue3110 (mixedVector B) := by
    change mixedMoment B node3110 node3110Labels = _
    exact sound3110 B hB hF
  have h3889 : mixedVector B (Sum.inr 3889) = Sparse.eval nodeValue3889 (mixedVector B) := by
    change mixedMoment B node3889 node3889Labels = _
    exact sound3889 B hB hF
  simpa only [sourceForm72, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h991, h994, h1010, h1059, h1181, h1191, h1264, h2393, h2408, h2454, h2465, h2495, h2618, h2640, h2732, h2744, h2776, h3039, h3055, h3110, h3889, reducedSource58] using sourceEq72 B hB

theorem rowSound58 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row58 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck58, numericCheck58, reducedZero58 B hB hF, mul_zero]

theorem reducedZero59 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource59 (mixedVector B) = 0 := by
  have h1624 : mixedVector B (Sum.inr 1624) = Sparse.eval nodeValue1624 (mixedVector B) := by
    change mixedMoment B node1624 node1624Labels = _
    exact sound1624 B hB hF
  have h1628 : mixedVector B (Sum.inr 1628) = Sparse.eval nodeValue1628 (mixedVector B) := by
    change mixedMoment B node1628 node1628Labels = _
    exact sound1628 B hB hF
  have h1629 : mixedVector B (Sum.inr 1629) = Sparse.eval nodeValue1629 (mixedVector B) := by
    change mixedMoment B node1629 node1629Labels = _
    exact sound1629 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h2837 : mixedVector B (Sum.inr 2837) = Sparse.eval nodeValue2837 (mixedVector B) := by
    change mixedMoment B node2837 node2837Labels = _
    exact sound2837 B hB hF
  have h2842 : mixedVector B (Sum.inr 2842) = Sparse.eval nodeValue2842 (mixedVector B) := by
    change mixedMoment B node2842 node2842Labels = _
    exact sound2842 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3242 : mixedVector B (Sum.inr 3242) = Sparse.eval nodeValue3242 (mixedVector B) := by
    change mixedMoment B node3242 node3242Labels = _
    exact sound3242 B hB hF
  have h3247 : mixedVector B (Sum.inr 3247) = Sparse.eval nodeValue3247 (mixedVector B) := by
    change mixedMoment B node3247 node3247Labels = _
    exact sound3247 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h3358 : mixedVector B (Sum.inr 3358) = Sparse.eval nodeValue3358 (mixedVector B) := by
    change mixedMoment B node3358 node3358Labels = _
    exact sound3358 B hB hF
  have h3437 : mixedVector B (Sum.inr 3437) = Sparse.eval nodeValue3437 (mixedVector B) := by
    change mixedMoment B node3437 node3437Labels = _
    exact sound3437 B hB hF
  have h3472 : mixedVector B (Sum.inr 3472) = Sparse.eval nodeValue3472 (mixedVector B) := by
    change mixedMoment B node3472 node3472Labels = _
    exact sound3472 B hB hF
  have h3486 : mixedVector B (Sum.inr 3486) = Sparse.eval nodeValue3486 (mixedVector B) := by
    change mixedMoment B node3486 node3486Labels = _
    exact sound3486 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3862 : mixedVector B (Sum.inr 3862) = Sparse.eval nodeValue3862 (mixedVector B) := by
    change mixedMoment B node3862 node3862Labels = _
    exact sound3862 B hB hF
  simpa only [sourceForm73, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1624, h1628, h1629, h1729, h2837, h2842, h3052, h3242, h3247, h3302, h3358, h3437, h3472, h3486, h3523, h3535, h3541, h3548, h3584, h3626, h3862, reducedSource59] using sourceEq73 B hB

theorem rowSound59 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row59 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck59, numericCheck59, reducedZero59 B hB hF, mul_zero]

theorem reducedZero60 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource60 (mixedVector B) = 0 := by
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm74, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2734, h2777, h3038, h3054, h3907, h4092, reducedSource60] using sourceEq74 B hB

theorem rowSound60 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row60 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck60, numericCheck60, reducedZero60 B hB hF, mul_zero]

theorem reducedZero61 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource61 (mixedVector B) = 0 := by
  have h1224 : mixedVector B (Sum.inr 1224) = Sparse.eval nodeValue1224 (mixedVector B) := by
    change mixedMoment B node1224 node1224Labels = _
    exact sound1224 B hB hF
  have h1227 : mixedVector B (Sum.inr 1227) = Sparse.eval nodeValue1227 (mixedVector B) := by
    change mixedMoment B node1227 node1227Labels = _
    exact sound1227 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1279 : mixedVector B (Sum.inr 1279) = Sparse.eval nodeValue1279 (mixedVector B) := by
    change mixedMoment B node1279 node1279Labels = _
    exact sound1279 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm75, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1224, h1227, h1243, h1279, h2734, h4092, reducedSource61] using sourceEq75 B hB

theorem rowSound61 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row61 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck61, numericCheck61, reducedZero61 B hB hF, mul_zero]

theorem reducedZero62 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource62 (mixedVector B) = 0 := by
  have h1279 : mixedVector B (Sum.inr 1279) = Sparse.eval nodeValue1279 (mixedVector B) := by
    change mixedMoment B node1279 node1279Labels = _
    exact sound1279 B hB hF
  have h2579 : mixedVector B (Sum.inr 2579) = Sparse.eval nodeValue2579 (mixedVector B) := by
    change mixedMoment B node2579 node2579Labels = _
    exact sound2579 B hB hF
  have h2651 : mixedVector B (Sum.inr 2651) = Sparse.eval nodeValue2651 (mixedVector B) := by
    change mixedMoment B node2651 node2651Labels = _
    exact sound2651 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm76, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1279, h2579, h2651, h2734, h2774, h4092, reducedSource62] using sourceEq76 B hB

theorem rowSound62 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row62 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck62, numericCheck62, reducedZero62 B hB hF, mul_zero]

theorem reducedZero63 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource63 (mixedVector B) = 0 := by
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm77, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1372, h2495, h2519, h2734, h3054, h4092, reducedSource63] using sourceEq77 B hB

theorem rowSound63 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row63 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck63, numericCheck63, reducedZero63 B hB hF, mul_zero]

theorem sourceRowsAt48 : MixedData.sourceRows (48 : Fin 2425) =
    MixedData.row48 := by decide +kernel

theorem sourceRowsAt49 : MixedData.sourceRows (49 : Fin 2425) =
    MixedData.row49 := by decide +kernel

theorem sourceRowsAt50 : MixedData.sourceRows (50 : Fin 2425) =
    MixedData.row50 := by decide +kernel

theorem sourceRowsAt51 : MixedData.sourceRows (51 : Fin 2425) =
    MixedData.row51 := by decide +kernel

theorem sourceRowsAt52 : MixedData.sourceRows (52 : Fin 2425) =
    MixedData.row52 := by decide +kernel

theorem sourceRowsAt53 : MixedData.sourceRows (53 : Fin 2425) =
    MixedData.row53 := by decide +kernel

theorem sourceRowsAt54 : MixedData.sourceRows (54 : Fin 2425) =
    MixedData.row54 := by decide +kernel

theorem sourceRowsAt55 : MixedData.sourceRows (55 : Fin 2425) =
    MixedData.row55 := by decide +kernel

theorem sourceRowsAt56 : MixedData.sourceRows (56 : Fin 2425) =
    MixedData.row56 := by decide +kernel

theorem sourceRowsAt57 : MixedData.sourceRows (57 : Fin 2425) =
    MixedData.row57 := by decide +kernel

theorem sourceRowsAt58 : MixedData.sourceRows (58 : Fin 2425) =
    MixedData.row58 := by decide +kernel

theorem sourceRowsAt59 : MixedData.sourceRows (59 : Fin 2425) =
    MixedData.row59 := by decide +kernel

theorem sourceRowsAt60 : MixedData.sourceRows (60 : Fin 2425) =
    MixedData.row60 := by decide +kernel

theorem sourceRowsAt61 : MixedData.sourceRows (61 : Fin 2425) =
    MixedData.row61 := by decide +kernel

theorem sourceRowsAt62 : MixedData.sourceRows (62 : Fin 2425) =
    MixedData.row62 := by decide +kernel

theorem sourceRowsAt63 : MixedData.sourceRows (63 : Fin 2425) =
    MixedData.row63 := by decide +kernel

theorem chunkSound3 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 3) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 48 ∨ k.val = 49 ∨ k.val = 50 ∨ k.val = 51 ∨ k.val = 52 ∨ k.val = 53 ∨ k.val = 54 ∨ k.val = 55 ∨ k.val = 56 ∨ k.val = 57 ∨ k.val = 58 ∨ k.val = 59 ∨ k.val = 60 ∨ k.val = 61 ∨ k.val = 62 ∨ k.val = 63 := by omega
  rcases heq with h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63
  · have he : k = (48 : Fin 2425) := Fin.ext h48
    subst k
    rw [sourceRowsAt48]
    exact rowSound48 B hB hF
  · have he : k = (49 : Fin 2425) := Fin.ext h49
    subst k
    rw [sourceRowsAt49]
    exact rowSound49 B hB hF
  · have he : k = (50 : Fin 2425) := Fin.ext h50
    subst k
    rw [sourceRowsAt50]
    exact rowSound50 B hB hF
  · have he : k = (51 : Fin 2425) := Fin.ext h51
    subst k
    rw [sourceRowsAt51]
    exact rowSound51 B hB hF
  · have he : k = (52 : Fin 2425) := Fin.ext h52
    subst k
    rw [sourceRowsAt52]
    exact rowSound52 B hB hF
  · have he : k = (53 : Fin 2425) := Fin.ext h53
    subst k
    rw [sourceRowsAt53]
    exact rowSound53 B hB hF
  · have he : k = (54 : Fin 2425) := Fin.ext h54
    subst k
    rw [sourceRowsAt54]
    exact rowSound54 B hB hF
  · have he : k = (55 : Fin 2425) := Fin.ext h55
    subst k
    rw [sourceRowsAt55]
    exact rowSound55 B hB hF
  · have he : k = (56 : Fin 2425) := Fin.ext h56
    subst k
    rw [sourceRowsAt56]
    exact rowSound56 B hB hF
  · have he : k = (57 : Fin 2425) := Fin.ext h57
    subst k
    rw [sourceRowsAt57]
    exact rowSound57 B hB hF
  · have he : k = (58 : Fin 2425) := Fin.ext h58
    subst k
    rw [sourceRowsAt58]
    exact rowSound58 B hB hF
  · have he : k = (59 : Fin 2425) := Fin.ext h59
    subst k
    rw [sourceRowsAt59]
    exact rowSound59 B hB hF
  · have he : k = (60 : Fin 2425) := Fin.ext h60
    subst k
    rw [sourceRowsAt60]
    exact rowSound60 B hB hF
  · have he : k = (61 : Fin 2425) := Fin.ext h61
    subst k
    rw [sourceRowsAt61]
    exact rowSound61 B hB hF
  · have he : k = (62 : Fin 2425) := Fin.ext h62
    subst k
    rw [sourceRowsAt62]
    exact rowSound62 B hB hF
  · have he : k = (63 : Fin 2425) := Fin.ext h63
    subst k
    rw [sourceRowsAt63]
    exact rowSound63 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
