import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources43

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1184 (mixedVector B) = 0 := by
  have h978 : mixedVector B (Sum.inr 978) = Sparse.eval nodeValue978 (mixedVector B) := by
    change mixedMoment B node978 node978Labels = _
    exact sound978 B hB hF
  have h983 : mixedVector B (Sum.inr 983) = Sparse.eval nodeValue983 (mixedVector B) := by
    change mixedMoment B node983 node983Labels = _
    exact sound983 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1005 : mixedVector B (Sum.inr 1005) = Sparse.eval nodeValue1005 (mixedVector B) := by
    change mixedMoment B node1005 node1005Labels = _
    exact sound1005 B hB hF
  have h1036 : mixedVector B (Sum.inr 1036) = Sparse.eval nodeValue1036 (mixedVector B) := by
    change mixedMoment B node1036 node1036Labels = _
    exact sound1036 B hB hF
  have h2206 : mixedVector B (Sum.inr 2206) = Sparse.eval nodeValue2206 (mixedVector B) := by
    change mixedMoment B node2206 node2206Labels = _
    exact sound2206 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1366, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h978, h983, h985, h1005, h1036, h2206, h4080, reducedSource1184] using sourceEq1366 B hB

theorem rowSound1184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1184 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1184, numericCheck1184, reducedZero1184 B hB hF, mul_zero]

theorem reducedZero1185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1185 (mixedVector B) = 0 := by
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h1914 : mixedVector B (Sum.inr 1914) = Sparse.eval nodeValue1914 (mixedVector B) := by
    change mixedMoment B node1914 node1914Labels = _
    exact sound1914 B hB hF
  have h1987 : mixedVector B (Sum.inr 1987) = Sparse.eval nodeValue1987 (mixedVector B) := by
    change mixedMoment B node1987 node1987Labels = _
    exact sound1987 B hB hF
  have h2079 : mixedVector B (Sum.inr 2079) = Sparse.eval nodeValue2079 (mixedVector B) := by
    change mixedMoment B node2079 node2079Labels = _
    exact sound2079 B hB hF
  have h2193 : mixedVector B (Sum.inr 2193) = Sparse.eval nodeValue2193 (mixedVector B) := by
    change mixedMoment B node2193 node2193Labels = _
    exact sound2193 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1367, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h982, h1914, h1987, h2079, h2193, h2205, h4080, reducedSource1185] using sourceEq1367 B hB

theorem rowSound1185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1185 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1185, numericCheck1185, reducedZero1185 B hB hF, mul_zero]

theorem reducedZero1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1186 (mixedVector B) = 0 := by
  have h977 : mixedVector B (Sum.inr 977) = Sparse.eval nodeValue977 (mixedVector B) := by
    change mixedMoment B node977 node977Labels = _
    exact sound977 B hB hF
  have h982 : mixedVector B (Sum.inr 982) = Sparse.eval nodeValue982 (mixedVector B) := by
    change mixedMoment B node982 node982Labels = _
    exact sound982 B hB hF
  have h985 : mixedVector B (Sum.inr 985) = Sparse.eval nodeValue985 (mixedVector B) := by
    change mixedMoment B node985 node985Labels = _
    exact sound985 B hB hF
  have h1004 : mixedVector B (Sum.inr 1004) = Sparse.eval nodeValue1004 (mixedVector B) := by
    change mixedMoment B node1004 node1004Labels = _
    exact sound1004 B hB hF
  have h1035 : mixedVector B (Sum.inr 1035) = Sparse.eval nodeValue1035 (mixedVector B) := by
    change mixedMoment B node1035 node1035Labels = _
    exact sound1035 B hB hF
  have h2205 : mixedVector B (Sum.inr 2205) = Sparse.eval nodeValue2205 (mixedVector B) := by
    change mixedMoment B node2205 node2205Labels = _
    exact sound2205 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1370, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h977, h982, h985, h1004, h1035, h2205, h4080, reducedSource1186] using sourceEq1370 B hB

theorem rowSound1186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1186 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1186, numericCheck1186, reducedZero1186 B hB hF, mul_zero]

theorem reducedZero1187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1187 (mixedVector B) = 0 := by
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h1986 : mixedVector B (Sum.inr 1986) = Sparse.eval nodeValue1986 (mixedVector B) := by
    change mixedMoment B node1986 node1986Labels = _
    exact sound1986 B hB hF
  have h2018 : mixedVector B (Sum.inr 2018) = Sparse.eval nodeValue2018 (mixedVector B) := by
    change mixedMoment B node2018 node2018Labels = _
    exact sound2018 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1373, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h979, h1911, h1986, h2018, h2203, h2208, h4081, reducedSource1187] using sourceEq1373 B hB

theorem rowSound1187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1187 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1187, numericCheck1187, reducedZero1187 B hB hF, mul_zero]

theorem reducedZero1188 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1188 (mixedVector B) = 0 := by
  have h864 : mixedVector B (Sum.inr 864) = Sparse.eval nodeValue864 (mixedVector B) := by
    change mixedMoment B node864 node864Labels = _
    exact sound864 B hB hF
  have h867 : mixedVector B (Sum.inr 867) = Sparse.eval nodeValue867 (mixedVector B) := by
    change mixedMoment B node867 node867Labels = _
    exact sound867 B hB hF
  have h872 : mixedVector B (Sum.inr 872) = Sparse.eval nodeValue872 (mixedVector B) := by
    change mixedMoment B node872 node872Labels = _
    exact sound872 B hB hF
  have h880 : mixedVector B (Sum.inr 880) = Sparse.eval nodeValue880 (mixedVector B) := by
    change mixedMoment B node880 node880Labels = _
    exact sound880 B hB hF
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h1911 : mixedVector B (Sum.inr 1911) = Sparse.eval nodeValue1911 (mixedVector B) := by
    change mixedMoment B node1911 node1911Labels = _
    exact sound1911 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1375, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h864, h867, h872, h880, h979, h1911, h4081, reducedSource1188] using sourceEq1375 B hB

theorem rowSound1188 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1188 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1188, numericCheck1188, reducedZero1188 B hB hF, mul_zero]

theorem reducedZero1189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1189 (mixedVector B) = 0 := by
  have h976 : mixedVector B (Sum.inr 976) = Sparse.eval nodeValue976 (mixedVector B) := by
    change mixedMoment B node976 node976Labels = _
    exact sound976 B hB hF
  have h979 : mixedVector B (Sum.inr 979) = Sparse.eval nodeValue979 (mixedVector B) := by
    change mixedMoment B node979 node979Labels = _
    exact sound979 B hB hF
  have h984 : mixedVector B (Sum.inr 984) = Sparse.eval nodeValue984 (mixedVector B) := by
    change mixedMoment B node984 node984Labels = _
    exact sound984 B hB hF
  have h999 : mixedVector B (Sum.inr 999) = Sparse.eval nodeValue999 (mixedVector B) := by
    change mixedMoment B node999 node999Labels = _
    exact sound999 B hB hF
  have h1033 : mixedVector B (Sum.inr 1033) = Sparse.eval nodeValue1033 (mixedVector B) := by
    change mixedMoment B node1033 node1033Labels = _
    exact sound1033 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1376, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h976, h979, h984, h999, h1033, h2203, h4081, reducedSource1189] using sourceEq1376 B hB

theorem rowSound1189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1189 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1189, numericCheck1189, reducedZero1189 B hB hF, mul_zero]

theorem reducedZero1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1190 (mixedVector B) = 0 := by
  have h698 : mixedVector B (Sum.inr 698) = Sparse.eval nodeValue698 (mixedVector B) := by
    change mixedMoment B node698 node698Labels = _
    exact sound698 B hB hF
  have h701 : mixedVector B (Sum.inr 701) = Sparse.eval nodeValue701 (mixedVector B) := by
    change mixedMoment B node701 node701Labels = _
    exact sound701 B hB hF
  have h706 : mixedVector B (Sum.inr 706) = Sparse.eval nodeValue706 (mixedVector B) := by
    change mixedMoment B node706 node706Labels = _
    exact sound706 B hB hF
  have h714 : mixedVector B (Sum.inr 714) = Sparse.eval nodeValue714 (mixedVector B) := by
    change mixedMoment B node714 node714Labels = _
    exact sound714 B hB hF
  have h809 : mixedVector B (Sum.inr 809) = Sparse.eval nodeValue809 (mixedVector B) := by
    change mixedMoment B node809 node809Labels = _
    exact sound809 B hB hF
  have h1599 : mixedVector B (Sum.inr 1599) = Sparse.eval nodeValue1599 (mixedVector B) := by
    change mixedMoment B node1599 node1599Labels = _
    exact sound1599 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1377, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h698, h701, h706, h714, h809, h1599, h4070, reducedSource1190] using sourceEq1377 B hB

theorem rowSound1190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1190 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1190, numericCheck1190, reducedZero1190 B hB hF, mul_zero]

theorem reducedZero1191 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1191 (mixedVector B) = 0 := by
  have h4178 : mixedVector B (Sum.inr 4178) = Sparse.eval nodeValue4178 (mixedVector B) := by
    change mixedMoment B node4178 node4178Labels = _
    exact sound4178 B hB hF
  have h4189 : mixedVector B (Sum.inr 4189) = Sparse.eval nodeValue4189 (mixedVector B) := by
    change mixedMoment B node4189 node4189Labels = _
    exact sound4189 B hB hF
  have h4192 : mixedVector B (Sum.inr 4192) = Sparse.eval nodeValue4192 (mixedVector B) := by
    change mixedMoment B node4192 node4192Labels = _
    exact sound4192 B hB hF
  have h4347 : mixedVector B (Sum.inr 4347) = Sparse.eval nodeValue4347 (mixedVector B) := by
    change mixedMoment B node4347 node4347Labels = _
    exact sound4347 B hB hF
  have h4358 : mixedVector B (Sum.inr 4358) = Sparse.eval nodeValue4358 (mixedVector B) := by
    change mixedMoment B node4358 node4358Labels = _
    exact sound4358 B hB hF
  have h4361 : mixedVector B (Sum.inr 4361) = Sparse.eval nodeValue4361 (mixedVector B) := by
    change mixedMoment B node4361 node4361Labels = _
    exact sound4361 B hB hF
  have h4476 : mixedVector B (Sum.inr 4476) = Sparse.eval nodeValue4476 (mixedVector B) := by
    change mixedMoment B node4476 node4476Labels = _
    exact sound4476 B hB hF
  have h4481 : mixedVector B (Sum.inr 4481) = Sparse.eval nodeValue4481 (mixedVector B) := by
    change mixedMoment B node4481 node4481Labels = _
    exact sound4481 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4843 : mixedVector B (Sum.inr 4843) = Sparse.eval nodeValue4843 (mixedVector B) := by
    change mixedMoment B node4843 node4843Labels = _
    exact sound4843 B hB hF
  have h4899 : mixedVector B (Sum.inr 4899) = Sparse.eval nodeValue4899 (mixedVector B) := by
    change mixedMoment B node4899 node4899Labels = _
    exact sound4899 B hB hF
  have h4901 : mixedVector B (Sum.inr 4901) = Sparse.eval nodeValue4901 (mixedVector B) := by
    change mixedMoment B node4901 node4901Labels = _
    exact sound4901 B hB hF
  simpa only [sourceForm1378, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4178, h4189, h4192, h4347, h4358, h4361, h4476, h4481, h4499, h4511, h4843, h4899, h4901, reducedSource1191] using sourceEq1378 B hB

theorem rowSound1191 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1191 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1191, numericCheck1191, reducedZero1191 B hB hF, mul_zero]

theorem reducedZero1192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1192 (mixedVector B) = 0 := by
  have h1520 : mixedVector B (Sum.inr 1520) = Sparse.eval nodeValue1520 (mixedVector B) := by
    change mixedMoment B node1520 node1520Labels = _
    exact sound1520 B hB hF
  have h1539 : mixedVector B (Sum.inr 1539) = Sparse.eval nodeValue1539 (mixedVector B) := by
    change mixedMoment B node1539 node1539Labels = _
    exact sound1539 B hB hF
  have h1540 : mixedVector B (Sum.inr 1540) = Sparse.eval nodeValue1540 (mixedVector B) := by
    change mixedMoment B node1540 node1540Labels = _
    exact sound1540 B hB hF
  have h1676 : mixedVector B (Sum.inr 1676) = Sparse.eval nodeValue1676 (mixedVector B) := by
    change mixedMoment B node1676 node1676Labels = _
    exact sound1676 B hB hF
  have h1694 : mixedVector B (Sum.inr 1694) = Sparse.eval nodeValue1694 (mixedVector B) := by
    change mixedMoment B node1694 node1694Labels = _
    exact sound1694 B hB hF
  have h1695 : mixedVector B (Sum.inr 1695) = Sparse.eval nodeValue1695 (mixedVector B) := by
    change mixedMoment B node1695 node1695Labels = _
    exact sound1695 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h1757 : mixedVector B (Sum.inr 1757) = Sparse.eval nodeValue1757 (mixedVector B) := by
    change mixedMoment B node1757 node1757Labels = _
    exact sound1757 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h2293 : mixedVector B (Sum.inr 2293) = Sparse.eval nodeValue2293 (mixedVector B) := by
    change mixedMoment B node2293 node2293Labels = _
    exact sound2293 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  simpa only [sourceForm1379, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1520, h1539, h1540, h1676, h1694, h1695, h1728, h1729, h1755, h1757, h2230, h2293, h2294, reducedSource1192] using sourceEq1379 B hB

theorem rowSound1192 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1192 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1192, numericCheck1192, reducedZero1192 B hB hF, mul_zero]

theorem reducedZero1193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1193 (mixedVector B) = 0 := by
  have h925 : mixedVector B (Sum.inr 925) = Sparse.eval nodeValue925 (mixedVector B) := by
    change mixedMoment B node925 node925Labels = _
    exact sound925 B hB hF
  have h936 : mixedVector B (Sum.inr 936) = Sparse.eval nodeValue936 (mixedVector B) := by
    change mixedMoment B node936 node936Labels = _
    exact sound936 B hB hF
  have h939 : mixedVector B (Sum.inr 939) = Sparse.eval nodeValue939 (mixedVector B) := by
    change mixedMoment B node939 node939Labels = _
    exact sound939 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1380, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h925, h936, h939, h1091, h2062, h4084, reducedSource1193] using sourceEq1380 B hB

theorem rowSound1193 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1193 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1193, numericCheck1193, reducedZero1193 B hB hF, mul_zero]

theorem reducedZero1194 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1194 (mixedVector B) = 0 := by
  have h4128 : mixedVector B (Sum.inr 4128) = Sparse.eval nodeValue4128 (mixedVector B) := by
    change mixedMoment B node4128 node4128Labels = _
    exact sound4128 B hB hF
  have h4134 : mixedVector B (Sum.inr 4134) = Sparse.eval nodeValue4134 (mixedVector B) := by
    change mixedMoment B node4134 node4134Labels = _
    exact sound4134 B hB hF
  have h4138 : mixedVector B (Sum.inr 4138) = Sparse.eval nodeValue4138 (mixedVector B) := by
    change mixedMoment B node4138 node4138Labels = _
    exact sound4138 B hB hF
  have h4309 : mixedVector B (Sum.inr 4309) = Sparse.eval nodeValue4309 (mixedVector B) := by
    change mixedMoment B node4309 node4309Labels = _
    exact sound4309 B hB hF
  have h4315 : mixedVector B (Sum.inr 4315) = Sparse.eval nodeValue4315 (mixedVector B) := by
    change mixedMoment B node4315 node4315Labels = _
    exact sound4315 B hB hF
  have h4319 : mixedVector B (Sum.inr 4319) = Sparse.eval nodeValue4319 (mixedVector B) := by
    change mixedMoment B node4319 node4319Labels = _
    exact sound4319 B hB hF
  have h4463 : mixedVector B (Sum.inr 4463) = Sparse.eval nodeValue4463 (mixedVector B) := by
    change mixedMoment B node4463 node4463Labels = _
    exact sound4463 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4503 : mixedVector B (Sum.inr 4503) = Sparse.eval nodeValue4503 (mixedVector B) := by
    change mixedMoment B node4503 node4503Labels = _
    exact sound4503 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h5109 : mixedVector B (Sum.inr 5109) = Sparse.eval nodeValue5109 (mixedVector B) := by
    change mixedMoment B node5109 node5109Labels = _
    exact sound5109 B hB hF
  have h5296 : mixedVector B (Sum.inr 5296) = Sparse.eval nodeValue5296 (mixedVector B) := by
    change mixedMoment B node5296 node5296Labels = _
    exact sound5296 B hB hF
  have h5310 : mixedVector B (Sum.inr 5310) = Sparse.eval nodeValue5310 (mixedVector B) := by
    change mixedMoment B node5310 node5310Labels = _
    exact sound5310 B hB hF
  simpa only [sourceForm1381, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4128, h4134, h4138, h4309, h4315, h4319, h4463, h4468, h4503, h4510, h5109, h5296, h5310, reducedSource1194] using sourceEq1381 B hB

theorem rowSound1194 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1194 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1194, numericCheck1194, reducedZero1194 B hB hF, mul_zero]

theorem reducedZero1195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1195 (mixedVector B) = 0 := by
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  have h4177 : mixedVector B (Sum.inr 4177) = Sparse.eval nodeValue4177 (mixedVector B) := by
    change mixedMoment B node4177 node4177Labels = _
    exact sound4177 B hB hF
  have h4187 : mixedVector B (Sum.inr 4187) = Sparse.eval nodeValue4187 (mixedVector B) := by
    change mixedMoment B node4187 node4187Labels = _
    exact sound4187 B hB hF
  have h4191 : mixedVector B (Sum.inr 4191) = Sparse.eval nodeValue4191 (mixedVector B) := by
    change mixedMoment B node4191 node4191Labels = _
    exact sound4191 B hB hF
  have h4346 : mixedVector B (Sum.inr 4346) = Sparse.eval nodeValue4346 (mixedVector B) := by
    change mixedMoment B node4346 node4346Labels = _
    exact sound4346 B hB hF
  have h4356 : mixedVector B (Sum.inr 4356) = Sparse.eval nodeValue4356 (mixedVector B) := by
    change mixedMoment B node4356 node4356Labels = _
    exact sound4356 B hB hF
  have h4360 : mixedVector B (Sum.inr 4360) = Sparse.eval nodeValue4360 (mixedVector B) := by
    change mixedMoment B node4360 node4360Labels = _
    exact sound4360 B hB hF
  have h4460 : mixedVector B (Sum.inr 4460) = Sparse.eval nodeValue4460 (mixedVector B) := by
    change mixedMoment B node4460 node4460Labels = _
    exact sound4460 B hB hF
  have h4468 : mixedVector B (Sum.inr 4468) = Sparse.eval nodeValue4468 (mixedVector B) := by
    change mixedMoment B node4468 node4468Labels = _
    exact sound4468 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  have h4841 : mixedVector B (Sum.inr 4841) = Sparse.eval nodeValue4841 (mixedVector B) := by
    change mixedMoment B node4841 node4841Labels = _
    exact sound4841 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  simpa only [sourceForm1385, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4084, h4177, h4187, h4191, h4346, h4356, h4360, h4460, h4468, h4498, h4511, h4841, h4897, reducedSource1195] using sourceEq1385 B hB

theorem rowSound1195 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1195 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1195, numericCheck1195, reducedZero1195 B hB hF, mul_zero]

theorem reducedZero1196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1196 (mixedVector B) = 0 := by
  have h1518 : mixedVector B (Sum.inr 1518) = Sparse.eval nodeValue1518 (mixedVector B) := by
    change mixedMoment B node1518 node1518Labels = _
    exact sound1518 B hB hF
  have h1537 : mixedVector B (Sum.inr 1537) = Sparse.eval nodeValue1537 (mixedVector B) := by
    change mixedMoment B node1537 node1537Labels = _
    exact sound1537 B hB hF
  have h1538 : mixedVector B (Sum.inr 1538) = Sparse.eval nodeValue1538 (mixedVector B) := by
    change mixedMoment B node1538 node1538Labels = _
    exact sound1538 B hB hF
  have h1674 : mixedVector B (Sum.inr 1674) = Sparse.eval nodeValue1674 (mixedVector B) := by
    change mixedMoment B node1674 node1674Labels = _
    exact sound1674 B hB hF
  have h1692 : mixedVector B (Sum.inr 1692) = Sparse.eval nodeValue1692 (mixedVector B) := by
    change mixedMoment B node1692 node1692Labels = _
    exact sound1692 B hB hF
  have h1693 : mixedVector B (Sum.inr 1693) = Sparse.eval nodeValue1693 (mixedVector B) := by
    change mixedMoment B node1693 node1693Labels = _
    exact sound1693 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1752 : mixedVector B (Sum.inr 1752) = Sparse.eval nodeValue1752 (mixedVector B) := by
    change mixedMoment B node1752 node1752Labels = _
    exact sound1752 B hB hF
  have h1755 : mixedVector B (Sum.inr 1755) = Sparse.eval nodeValue1755 (mixedVector B) := by
    change mixedMoment B node1755 node1755Labels = _
    exact sound1755 B hB hF
  have h2228 : mixedVector B (Sum.inr 2228) = Sparse.eval nodeValue2228 (mixedVector B) := by
    change mixedMoment B node2228 node2228Labels = _
    exact sound2228 B hB hF
  have h2292 : mixedVector B (Sum.inr 2292) = Sparse.eval nodeValue2292 (mixedVector B) := by
    change mixedMoment B node2292 node2292Labels = _
    exact sound2292 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1386, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1518, h1537, h1538, h1674, h1692, h1693, h1725, h1727, h1752, h1755, h2228, h2292, h4084, reducedSource1196] using sourceEq1386 B hB

theorem rowSound1196 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1196 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1196, numericCheck1196, reducedZero1196 B hB hF, mul_zero]

theorem reducedZero1197 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1197 (mixedVector B) = 0 := by
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  have h4174 : mixedVector B (Sum.inr 4174) = Sparse.eval nodeValue4174 (mixedVector B) := by
    change mixedMoment B node4174 node4174Labels = _
    exact sound4174 B hB hF
  have h4181 : mixedVector B (Sum.inr 4181) = Sparse.eval nodeValue4181 (mixedVector B) := by
    change mixedMoment B node4181 node4181Labels = _
    exact sound4181 B hB hF
  have h4190 : mixedVector B (Sum.inr 4190) = Sparse.eval nodeValue4190 (mixedVector B) := by
    change mixedMoment B node4190 node4190Labels = _
    exact sound4190 B hB hF
  have h4343 : mixedVector B (Sum.inr 4343) = Sparse.eval nodeValue4343 (mixedVector B) := by
    change mixedMoment B node4343 node4343Labels = _
    exact sound4343 B hB hF
  have h4350 : mixedVector B (Sum.inr 4350) = Sparse.eval nodeValue4350 (mixedVector B) := by
    change mixedMoment B node4350 node4350Labels = _
    exact sound4350 B hB hF
  have h4359 : mixedVector B (Sum.inr 4359) = Sparse.eval nodeValue4359 (mixedVector B) := by
    change mixedMoment B node4359 node4359Labels = _
    exact sound4359 B hB hF
  have h4496 : mixedVector B (Sum.inr 4496) = Sparse.eval nodeValue4496 (mixedVector B) := by
    change mixedMoment B node4496 node4496Labels = _
    exact sound4496 B hB hF
  have h4501 : mixedVector B (Sum.inr 4501) = Sparse.eval nodeValue4501 (mixedVector B) := by
    change mixedMoment B node4501 node4501Labels = _
    exact sound4501 B hB hF
  have h4510 : mixedVector B (Sum.inr 4510) = Sparse.eval nodeValue4510 (mixedVector B) := by
    change mixedMoment B node4510 node4510Labels = _
    exact sound4510 B hB hF
  have h4512 : mixedVector B (Sum.inr 4512) = Sparse.eval nodeValue4512 (mixedVector B) := by
    change mixedMoment B node4512 node4512Labels = _
    exact sound4512 B hB hF
  have h4837 : mixedVector B (Sum.inr 4837) = Sparse.eval nodeValue4837 (mixedVector B) := by
    change mixedMoment B node4837 node4837Labels = _
    exact sound4837 B hB hF
  have h4897 : mixedVector B (Sum.inr 4897) = Sparse.eval nodeValue4897 (mixedVector B) := by
    change mixedMoment B node4897 node4897Labels = _
    exact sound4897 B hB hF
  simpa only [sourceForm1387, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4085, h4174, h4181, h4190, h4343, h4350, h4359, h4496, h4501, h4510, h4512, h4837, h4897, reducedSource1197] using sourceEq1387 B hB

theorem rowSound1197 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1197 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1197, numericCheck1197, reducedZero1197 B hB hF, mul_zero]

theorem reducedZero1198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1198 (mixedVector B) = 0 := by
  have h1509 : mixedVector B (Sum.inr 1509) = Sparse.eval nodeValue1509 (mixedVector B) := by
    change mixedMoment B node1509 node1509Labels = _
    exact sound1509 B hB hF
  have h1521 : mixedVector B (Sum.inr 1521) = Sparse.eval nodeValue1521 (mixedVector B) := by
    change mixedMoment B node1521 node1521Labels = _
    exact sound1521 B hB hF
  have h1527 : mixedVector B (Sum.inr 1527) = Sparse.eval nodeValue1527 (mixedVector B) := by
    change mixedMoment B node1527 node1527Labels = _
    exact sound1527 B hB hF
  have h1666 : mixedVector B (Sum.inr 1666) = Sparse.eval nodeValue1666 (mixedVector B) := by
    change mixedMoment B node1666 node1666Labels = _
    exact sound1666 B hB hF
  have h1677 : mixedVector B (Sum.inr 1677) = Sparse.eval nodeValue1677 (mixedVector B) := by
    change mixedMoment B node1677 node1677Labels = _
    exact sound1677 B hB hF
  have h1683 : mixedVector B (Sum.inr 1683) = Sparse.eval nodeValue1683 (mixedVector B) := by
    change mixedMoment B node1683 node1683Labels = _
    exact sound1683 B hB hF
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h1730 : mixedVector B (Sum.inr 1730) = Sparse.eval nodeValue1730 (mixedVector B) := by
    change mixedMoment B node1730 node1730Labels = _
    exact sound1730 B hB hF
  have h1741 : mixedVector B (Sum.inr 1741) = Sparse.eval nodeValue1741 (mixedVector B) := by
    change mixedMoment B node1741 node1741Labels = _
    exact sound1741 B hB hF
  have h1758 : mixedVector B (Sum.inr 1758) = Sparse.eval nodeValue1758 (mixedVector B) := by
    change mixedMoment B node1758 node1758Labels = _
    exact sound1758 B hB hF
  have h2208 : mixedVector B (Sum.inr 2208) = Sparse.eval nodeValue2208 (mixedVector B) := by
    change mixedMoment B node2208 node2208Labels = _
    exact sound2208 B hB hF
  have h2268 : mixedVector B (Sum.inr 2268) = Sparse.eval nodeValue2268 (mixedVector B) := by
    change mixedMoment B node2268 node2268Labels = _
    exact sound2268 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1388, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1509, h1521, h1527, h1666, h1677, h1683, h1710, h1730, h1741, h1758, h2208, h2268, h4085, reducedSource1198] using sourceEq1388 B hB

theorem rowSound1198 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1198 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1198, numericCheck1198, reducedZero1198 B hB hF, mul_zero]

theorem reducedZero1199 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1199 (mixedVector B) = 0 := by
  have h602 : mixedVector B (Sum.inr 602) = Sparse.eval nodeValue602 (mixedVector B) := by
    change mixedMoment B node602 node602Labels = _
    exact sound602 B hB hF
  have h609 : mixedVector B (Sum.inr 609) = Sparse.eval nodeValue609 (mixedVector B) := by
    change mixedMoment B node609 node609Labels = _
    exact sound609 B hB hF
  have h618 : mixedVector B (Sum.inr 618) = Sparse.eval nodeValue618 (mixedVector B) := by
    change mixedMoment B node618 node618Labels = _
    exact sound618 B hB hF
  have h1085 : mixedVector B (Sum.inr 1085) = Sparse.eval nodeValue1085 (mixedVector B) := by
    change mixedMoment B node1085 node1085Labels = _
    exact sound1085 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1389, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h602, h609, h618, h1085, h4085, reducedSource1199] using sourceEq1389 B hB

theorem rowSound1199 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1199 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1199, numericCheck1199, reducedZero1199 B hB hF, mul_zero]

theorem sourceRowsAt1184 : MixedData.sourceRows (1184 : Fin 2425) =
    MixedData.row1184 := by decide +kernel

theorem sourceRowsAt1185 : MixedData.sourceRows (1185 : Fin 2425) =
    MixedData.row1185 := by decide +kernel

theorem sourceRowsAt1186 : MixedData.sourceRows (1186 : Fin 2425) =
    MixedData.row1186 := by decide +kernel

theorem sourceRowsAt1187 : MixedData.sourceRows (1187 : Fin 2425) =
    MixedData.row1187 := by decide +kernel

theorem sourceRowsAt1188 : MixedData.sourceRows (1188 : Fin 2425) =
    MixedData.row1188 := by decide +kernel

theorem sourceRowsAt1189 : MixedData.sourceRows (1189 : Fin 2425) =
    MixedData.row1189 := by decide +kernel

theorem sourceRowsAt1190 : MixedData.sourceRows (1190 : Fin 2425) =
    MixedData.row1190 := by decide +kernel

theorem sourceRowsAt1191 : MixedData.sourceRows (1191 : Fin 2425) =
    MixedData.row1191 := by decide +kernel

theorem sourceRowsAt1192 : MixedData.sourceRows (1192 : Fin 2425) =
    MixedData.row1192 := by decide +kernel

theorem sourceRowsAt1193 : MixedData.sourceRows (1193 : Fin 2425) =
    MixedData.row1193 := by decide +kernel

theorem sourceRowsAt1194 : MixedData.sourceRows (1194 : Fin 2425) =
    MixedData.row1194 := by decide +kernel

theorem sourceRowsAt1195 : MixedData.sourceRows (1195 : Fin 2425) =
    MixedData.row1195 := by decide +kernel

theorem sourceRowsAt1196 : MixedData.sourceRows (1196 : Fin 2425) =
    MixedData.row1196 := by decide +kernel

theorem sourceRowsAt1197 : MixedData.sourceRows (1197 : Fin 2425) =
    MixedData.row1197 := by decide +kernel

theorem sourceRowsAt1198 : MixedData.sourceRows (1198 : Fin 2425) =
    MixedData.row1198 := by decide +kernel

theorem sourceRowsAt1199 : MixedData.sourceRows (1199 : Fin 2425) =
    MixedData.row1199 := by decide +kernel

theorem chunkSound74 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 74) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1184 ∨ k.val = 1185 ∨ k.val = 1186 ∨ k.val = 1187 ∨ k.val = 1188 ∨ k.val = 1189 ∨ k.val = 1190 ∨ k.val = 1191 ∨ k.val = 1192 ∨ k.val = 1193 ∨ k.val = 1194 ∨ k.val = 1195 ∨ k.val = 1196 ∨ k.val = 1197 ∨ k.val = 1198 ∨ k.val = 1199 := by omega
  rcases heq with h1184 | h1185 | h1186 | h1187 | h1188 | h1189 | h1190 | h1191 | h1192 | h1193 | h1194 | h1195 | h1196 | h1197 | h1198 | h1199
  · have he : k = (1184 : Fin 2425) := Fin.ext h1184
    subst k
    rw [sourceRowsAt1184]
    exact rowSound1184 B hB hF
  · have he : k = (1185 : Fin 2425) := Fin.ext h1185
    subst k
    rw [sourceRowsAt1185]
    exact rowSound1185 B hB hF
  · have he : k = (1186 : Fin 2425) := Fin.ext h1186
    subst k
    rw [sourceRowsAt1186]
    exact rowSound1186 B hB hF
  · have he : k = (1187 : Fin 2425) := Fin.ext h1187
    subst k
    rw [sourceRowsAt1187]
    exact rowSound1187 B hB hF
  · have he : k = (1188 : Fin 2425) := Fin.ext h1188
    subst k
    rw [sourceRowsAt1188]
    exact rowSound1188 B hB hF
  · have he : k = (1189 : Fin 2425) := Fin.ext h1189
    subst k
    rw [sourceRowsAt1189]
    exact rowSound1189 B hB hF
  · have he : k = (1190 : Fin 2425) := Fin.ext h1190
    subst k
    rw [sourceRowsAt1190]
    exact rowSound1190 B hB hF
  · have he : k = (1191 : Fin 2425) := Fin.ext h1191
    subst k
    rw [sourceRowsAt1191]
    exact rowSound1191 B hB hF
  · have he : k = (1192 : Fin 2425) := Fin.ext h1192
    subst k
    rw [sourceRowsAt1192]
    exact rowSound1192 B hB hF
  · have he : k = (1193 : Fin 2425) := Fin.ext h1193
    subst k
    rw [sourceRowsAt1193]
    exact rowSound1193 B hB hF
  · have he : k = (1194 : Fin 2425) := Fin.ext h1194
    subst k
    rw [sourceRowsAt1194]
    exact rowSound1194 B hB hF
  · have he : k = (1195 : Fin 2425) := Fin.ext h1195
    subst k
    rw [sourceRowsAt1195]
    exact rowSound1195 B hB hF
  · have he : k = (1196 : Fin 2425) := Fin.ext h1196
    subst k
    rw [sourceRowsAt1196]
    exact rowSound1196 B hB hF
  · have he : k = (1197 : Fin 2425) := Fin.ext h1197
    subst k
    rw [sourceRowsAt1197]
    exact rowSound1197 B hB hF
  · have he : k = (1198 : Fin 2425) := Fin.ext h1198
    subst k
    rw [sourceRowsAt1198]
    exact rowSound1198 B hB hF
  · have he : k = (1199 : Fin 2425) := Fin.ext h1199
    subst k
    rw [sourceRowsAt1199]
    exact rowSound1199 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
