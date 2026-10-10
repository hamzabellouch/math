import OAI.Analysis.MutuallyUnbiased.MixedData.Sources
import OAI.Analysis.MutuallyUnbiased.MixedSources.Arithmetic83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sources49

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1328 (mixedVector B) = 0 := by
  have h562 : mixedVector B (Sum.inr 562) = Sparse.eval nodeValue562 (mixedVector B) := by
    change mixedMoment B node562 node562Labels = _
    exact sound562 B hB hF
  have h724 : mixedVector B (Sum.inr 724) = Sparse.eval nodeValue724 (mixedVector B) := by
    change mixedMoment B node724 node724Labels = _
    exact sound724 B hB hF
  have h830 : mixedVector B (Sum.inr 830) = Sparse.eval nodeValue830 (mixedVector B) := by
    change mixedMoment B node830 node830Labels = _
    exact sound830 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h858 : mixedVector B (Sum.inr 858) = Sparse.eval nodeValue858 (mixedVector B) := by
    change mixedMoment B node858 node858Labels = _
    exact sound858 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1561, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h562, h724, h830, h852, h858, h4071, reducedSource1328] using sourceEq1561 B hB

theorem rowSound1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1328 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1328, numericCheck1328, reducedZero1328 B hB hF, mul_zero]

theorem reducedZero1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1329 (mixedVector B) = 0 := by
  have h831 : mixedVector B (Sum.inr 831) = Sparse.eval nodeValue831 (mixedVector B) := by
    change mixedMoment B node831 node831Labels = _
    exact sound831 B hB hF
  have h1612 : mixedVector B (Sum.inr 1612) = Sparse.eval nodeValue1612 (mixedVector B) := by
    change mixedMoment B node1612 node1612Labels = _
    exact sound1612 B hB hF
  have h1661 : mixedVector B (Sum.inr 1661) = Sparse.eval nodeValue1661 (mixedVector B) := by
    change mixedMoment B node1661 node1661Labels = _
    exact sound1661 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1562, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h831, h1612, h1661, h1739, h4069, reducedSource1329] using sourceEq1562 B hB

theorem rowSound1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1329 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1329, numericCheck1329, reducedZero1329 B hB hF, mul_zero]

theorem reducedZero1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1330 (mixedVector B) = 0 := by
  have h789 : mixedVector B (Sum.inr 789) = Sparse.eval nodeValue789 (mixedVector B) := by
    change mixedMoment B node789 node789Labels = _
    exact sound789 B hB hF
  have h1594 : mixedVector B (Sum.inr 1594) = Sparse.eval nodeValue1594 (mixedVector B) := by
    change mixedMoment B node1594 node1594Labels = _
    exact sound1594 B hB hF
  have h1640 : mixedVector B (Sum.inr 1640) = Sparse.eval nodeValue1640 (mixedVector B) := by
    change mixedMoment B node1640 node1640Labels = _
    exact sound1640 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1564, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h789, h1594, h1640, h1707, h1709, h4069, reducedSource1330] using sourceEq1564 B hB

theorem rowSound1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1330 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1330, numericCheck1330, reducedZero1330 B hB hF, mul_zero]

theorem reducedZero1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1331 (mixedVector B) = 0 := by
  have h543 : mixedVector B (Sum.inr 543) = Sparse.eval nodeValue543 (mixedVector B) := by
    change mixedMoment B node543 node543Labels = _
    exact sound543 B hB hF
  have h703 : mixedVector B (Sum.inr 703) = Sparse.eval nodeValue703 (mixedVector B) := by
    change mixedMoment B node703 node703Labels = _
    exact sound703 B hB hF
  have h738 : mixedVector B (Sum.inr 738) = Sparse.eval nodeValue738 (mixedVector B) := by
    change mixedMoment B node738 node738Labels = _
    exact sound738 B hB hF
  have h789 : mixedVector B (Sum.inr 789) = Sparse.eval nodeValue789 (mixedVector B) := by
    change mixedMoment B node789 node789Labels = _
    exact sound789 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h811 : mixedVector B (Sum.inr 811) = Sparse.eval nodeValue811 (mixedVector B) := by
    change mixedMoment B node811 node811Labels = _
    exact sound811 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1565, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h543, h703, h738, h789, h806, h811, h4069, reducedSource1331] using sourceEq1565 B hB

theorem rowSound1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1331 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1331, numericCheck1331, reducedZero1331 B hB hF, mul_zero]

theorem reducedZero1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1332 (mixedVector B) = 0 := by
  have h552 : mixedVector B (Sum.inr 552) = Sparse.eval nodeValue552 (mixedVector B) := by
    change mixedMoment B node552 node552Labels = _
    exact sound552 B hB hF
  have h710 : mixedVector B (Sum.inr 710) = Sparse.eval nodeValue710 (mixedVector B) := by
    change mixedMoment B node710 node710Labels = _
    exact sound710 B hB hF
  have h823 : mixedVector B (Sum.inr 823) = Sparse.eval nodeValue823 (mixedVector B) := by
    change mixedMoment B node823 node823Labels = _
    exact sound823 B hB hF
  have h848 : mixedVector B (Sum.inr 848) = Sparse.eval nodeValue848 (mixedVector B) := by
    change mixedMoment B node848 node848Labels = _
    exact sound848 B hB hF
  have h852 : mixedVector B (Sum.inr 852) = Sparse.eval nodeValue852 (mixedVector B) := by
    change mixedMoment B node852 node852Labels = _
    exact sound852 B hB hF
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  simpa only [sourceForm1566, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h552, h710, h823, h848, h852, h4071, reducedSource1332] using sourceEq1566 B hB

theorem rowSound1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1332 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1332, numericCheck1332, reducedZero1332 B hB hF, mul_zero]

theorem reducedZero1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1333 (mixedVector B) = 0 := by
  have h790 : mixedVector B (Sum.inr 790) = Sparse.eval nodeValue790 (mixedVector B) := by
    change mixedMoment B node790 node790Labels = _
    exact sound790 B hB hF
  have h1595 : mixedVector B (Sum.inr 1595) = Sparse.eval nodeValue1595 (mixedVector B) := by
    change mixedMoment B node1595 node1595Labels = _
    exact sound1595 B hB hF
  have h1641 : mixedVector B (Sum.inr 1641) = Sparse.eval nodeValue1641 (mixedVector B) := by
    change mixedMoment B node1641 node1641Labels = _
    exact sound1641 B hB hF
  have h1708 : mixedVector B (Sum.inr 1708) = Sparse.eval nodeValue1708 (mixedVector B) := by
    change mixedMoment B node1708 node1708Labels = _
    exact sound1708 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1567, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h790, h1595, h1641, h1708, h4068, reducedSource1333] using sourceEq1567 B hB

theorem rowSound1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1333 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1333, numericCheck1333, reducedZero1333 B hB hF, mul_zero]

theorem reducedZero1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1334 (mixedVector B) = 0 := by
  have h544 : mixedVector B (Sum.inr 544) = Sparse.eval nodeValue544 (mixedVector B) := by
    change mixedMoment B node544 node544Labels = _
    exact sound544 B hB hF
  have h704 : mixedVector B (Sum.inr 704) = Sparse.eval nodeValue704 (mixedVector B) := by
    change mixedMoment B node704 node704Labels = _
    exact sound704 B hB hF
  have h739 : mixedVector B (Sum.inr 739) = Sparse.eval nodeValue739 (mixedVector B) := by
    change mixedMoment B node739 node739Labels = _
    exact sound739 B hB hF
  have h790 : mixedVector B (Sum.inr 790) = Sparse.eval nodeValue790 (mixedVector B) := by
    change mixedMoment B node790 node790Labels = _
    exact sound790 B hB hF
  have h810 : mixedVector B (Sum.inr 810) = Sparse.eval nodeValue810 (mixedVector B) := by
    change mixedMoment B node810 node810Labels = _
    exact sound810 B hB hF
  have h4068 : mixedVector B (Sum.inr 4068) = Sparse.eval nodeValue4068 (mixedVector B) := by
    change mixedMoment B node4068 node4068Labels = _
    exact sound4068 B hB hF
  simpa only [sourceForm1568, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h544, h704, h739, h790, h810, h4068, reducedSource1334] using sourceEq1568 B hB

theorem rowSound1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1334 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1334, numericCheck1334, reducedZero1334 B hB hF, mul_zero]

theorem reducedZero1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1335 (mixedVector B) = 0 := by
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4102 : mixedVector B (Sum.inr 4102) = Sparse.eval nodeValue4102 (mixedVector B) := by
    change mixedMoment B node4102 node4102Labels = _
    exact sound4102 B hB hF
  have h4110 : mixedVector B (Sum.inr 4110) = Sparse.eval nodeValue4110 (mixedVector B) := by
    change mixedMoment B node4110 node4110Labels = _
    exact sound4110 B hB hF
  have h4111 : mixedVector B (Sum.inr 4111) = Sparse.eval nodeValue4111 (mixedVector B) := by
    change mixedMoment B node4111 node4111Labels = _
    exact sound4111 B hB hF
  have h4130 : mixedVector B (Sum.inr 4130) = Sparse.eval nodeValue4130 (mixedVector B) := by
    change mixedMoment B node4130 node4130Labels = _
    exact sound4130 B hB hF
  have h4197 : mixedVector B (Sum.inr 4197) = Sparse.eval nodeValue4197 (mixedVector B) := by
    change mixedMoment B node4197 node4197Labels = _
    exact sound4197 B hB hF
  have h4204 : mixedVector B (Sum.inr 4204) = Sparse.eval nodeValue4204 (mixedVector B) := by
    change mixedMoment B node4204 node4204Labels = _
    exact sound4204 B hB hF
  have h4205 : mixedVector B (Sum.inr 4205) = Sparse.eval nodeValue4205 (mixedVector B) := by
    change mixedMoment B node4205 node4205Labels = _
    exact sound4205 B hB hF
  have h4221 : mixedVector B (Sum.inr 4221) = Sparse.eval nodeValue4221 (mixedVector B) := by
    change mixedMoment B node4221 node4221Labels = _
    exact sound4221 B hB hF
  have h4234 : mixedVector B (Sum.inr 4234) = Sparse.eval nodeValue4234 (mixedVector B) := by
    change mixedMoment B node4234 node4234Labels = _
    exact sound4234 B hB hF
  have h4242 : mixedVector B (Sum.inr 4242) = Sparse.eval nodeValue4242 (mixedVector B) := by
    change mixedMoment B node4242 node4242Labels = _
    exact sound4242 B hB hF
  have h4243 : mixedVector B (Sum.inr 4243) = Sparse.eval nodeValue4243 (mixedVector B) := by
    change mixedMoment B node4243 node4243Labels = _
    exact sound4243 B hB hF
  have h4264 : mixedVector B (Sum.inr 4264) = Sparse.eval nodeValue4264 (mixedVector B) := by
    change mixedMoment B node4264 node4264Labels = _
    exact sound4264 B hB hF
  have h4265 : mixedVector B (Sum.inr 4265) = Sparse.eval nodeValue4265 (mixedVector B) := by
    change mixedMoment B node4265 node4265Labels = _
    exact sound4265 B hB hF
  have h4269 : mixedVector B (Sum.inr 4269) = Sparse.eval nodeValue4269 (mixedVector B) := by
    change mixedMoment B node4269 node4269Labels = _
    exact sound4269 B hB hF
  have h4270 : mixedVector B (Sum.inr 4270) = Sparse.eval nodeValue4270 (mixedVector B) := by
    change mixedMoment B node4270 node4270Labels = _
    exact sound4270 B hB hF
  have h4283 : mixedVector B (Sum.inr 4283) = Sparse.eval nodeValue4283 (mixedVector B) := by
    change mixedMoment B node4283 node4283Labels = _
    exact sound4283 B hB hF
  have h4419 : mixedVector B (Sum.inr 4419) = Sparse.eval nodeValue4419 (mixedVector B) := by
    change mixedMoment B node4419 node4419Labels = _
    exact sound4419 B hB hF
  have h4491 : mixedVector B (Sum.inr 4491) = Sparse.eval nodeValue4491 (mixedVector B) := by
    change mixedMoment B node4491 node4491Labels = _
    exact sound4491 B hB hF
  have h4498 : mixedVector B (Sum.inr 4498) = Sparse.eval nodeValue4498 (mixedVector B) := by
    change mixedMoment B node4498 node4498Labels = _
    exact sound4498 B hB hF
  have h4499 : mixedVector B (Sum.inr 4499) = Sparse.eval nodeValue4499 (mixedVector B) := by
    change mixedMoment B node4499 node4499Labels = _
    exact sound4499 B hB hF
  simpa only [sourceForm1569, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4069, h4102, h4110, h4111, h4130, h4197, h4204, h4205, h4221, h4234, h4242, h4243, h4264, h4265, h4269, h4270, h4283, h4419, h4491, h4498, h4499, reducedSource1335] using sourceEq1569 B hB

theorem rowSound1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1335 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1335, numericCheck1335, reducedZero1335 B hB hF, mul_zero]

theorem reducedZero1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1336 (mixedVector B) = 0 := by
  have h664 : mixedVector B (Sum.inr 664) = Sparse.eval nodeValue664 (mixedVector B) := by
    change mixedMoment B node664 node664Labels = _
    exact sound664 B hB hF
  have h684 : mixedVector B (Sum.inr 684) = Sparse.eval nodeValue684 (mixedVector B) := by
    change mixedMoment B node684 node684Labels = _
    exact sound684 B hB hF
  have h685 : mixedVector B (Sum.inr 685) = Sparse.eval nodeValue685 (mixedVector B) := by
    change mixedMoment B node685 node685Labels = _
    exact sound685 B hB hF
  have h689 : mixedVector B (Sum.inr 689) = Sparse.eval nodeValue689 (mixedVector B) := by
    change mixedMoment B node689 node689Labels = _
    exact sound689 B hB hF
  have h749 : mixedVector B (Sum.inr 749) = Sparse.eval nodeValue749 (mixedVector B) := by
    change mixedMoment B node749 node749Labels = _
    exact sound749 B hB hF
  have h763 : mixedVector B (Sum.inr 763) = Sparse.eval nodeValue763 (mixedVector B) := by
    change mixedMoment B node763 node763Labels = _
    exact sound763 B hB hF
  have h764 : mixedVector B (Sum.inr 764) = Sparse.eval nodeValue764 (mixedVector B) := by
    change mixedMoment B node764 node764Labels = _
    exact sound764 B hB hF
  have h768 : mixedVector B (Sum.inr 768) = Sparse.eval nodeValue768 (mixedVector B) := by
    change mixedMoment B node768 node768Labels = _
    exact sound768 B hB hF
  have h800 : mixedVector B (Sum.inr 800) = Sparse.eval nodeValue800 (mixedVector B) := by
    change mixedMoment B node800 node800Labels = _
    exact sound800 B hB hF
  have h806 : mixedVector B (Sum.inr 806) = Sparse.eval nodeValue806 (mixedVector B) := by
    change mixedMoment B node806 node806Labels = _
    exact sound806 B hB hF
  have h807 : mixedVector B (Sum.inr 807) = Sparse.eval nodeValue807 (mixedVector B) := by
    change mixedMoment B node807 node807Labels = _
    exact sound807 B hB hF
  have h843 : mixedVector B (Sum.inr 843) = Sparse.eval nodeValue843 (mixedVector B) := by
    change mixedMoment B node843 node843Labels = _
    exact sound843 B hB hF
  have h844 : mixedVector B (Sum.inr 844) = Sparse.eval nodeValue844 (mixedVector B) := by
    change mixedMoment B node844 node844Labels = _
    exact sound844 B hB hF
  have h851 : mixedVector B (Sum.inr 851) = Sparse.eval nodeValue851 (mixedVector B) := by
    change mixedMoment B node851 node851Labels = _
    exact sound851 B hB hF
  have h853 : mixedVector B (Sum.inr 853) = Sparse.eval nodeValue853 (mixedVector B) := by
    change mixedMoment B node853 node853Labels = _
    exact sound853 B hB hF
  have h856 : mixedVector B (Sum.inr 856) = Sparse.eval nodeValue856 (mixedVector B) := by
    change mixedMoment B node856 node856Labels = _
    exact sound856 B hB hF
  have h1000 : mixedVector B (Sum.inr 1000) = Sparse.eval nodeValue1000 (mixedVector B) := by
    change mixedMoment B node1000 node1000Labels = _
    exact sound1000 B hB hF
  have h1075 : mixedVector B (Sum.inr 1075) = Sparse.eval nodeValue1075 (mixedVector B) := by
    change mixedMoment B node1075 node1075Labels = _
    exact sound1075 B hB hF
  have h1082 : mixedVector B (Sum.inr 1082) = Sparse.eval nodeValue1082 (mixedVector B) := by
    change mixedMoment B node1082 node1082Labels = _
    exact sound1082 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1570, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h664, h684, h685, h689, h749, h763, h764, h768, h800, h806, h807, h843, h844, h851, h853, h856, h1000, h1075, h1082, h1083, h4069, reducedSource1336] using sourceEq1570 B hB

theorem rowSound1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1336 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1336, numericCheck1336, reducedZero1336 B hB hF, mul_zero]

theorem reducedZero1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1337 (mixedVector B) = 0 := by
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h1605 : mixedVector B (Sum.inr 1605) = Sparse.eval nodeValue1605 (mixedVector B) := by
    change mixedMoment B node1605 node1605Labels = _
    exact sound1605 B hB hF
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h1727 : mixedVector B (Sum.inr 1727) = Sparse.eval nodeValue1727 (mixedVector B) := by
    change mixedMoment B node1727 node1727Labels = _
    exact sound1727 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1571, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h816, h1605, h1653, h1727, h1728, h4069, reducedSource1337] using sourceEq1571 B hB

theorem rowSound1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1337 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1337, numericCheck1337, reducedZero1337 B hB hF, mul_zero]

theorem reducedZero1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1338 (mixedVector B) = 0 := by
  have h539 : mixedVector B (Sum.inr 539) = Sparse.eval nodeValue539 (mixedVector B) := by
    change mixedMoment B node539 node539Labels = _
    exact sound539 B hB hF
  have h547 : mixedVector B (Sum.inr 547) = Sparse.eval nodeValue547 (mixedVector B) := by
    change mixedMoment B node547 node547Labels = _
    exact sound547 B hB hF
  have h548 : mixedVector B (Sum.inr 548) = Sparse.eval nodeValue548 (mixedVector B) := by
    change mixedMoment B node548 node548Labels = _
    exact sound548 B hB hF
  have h561 : mixedVector B (Sum.inr 561) = Sparse.eval nodeValue561 (mixedVector B) := by
    change mixedMoment B node561 node561Labels = _
    exact sound561 B hB hF
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1572, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h539, h547, h548, h561, h816, h4069, reducedSource1338] using sourceEq1572 B hB

theorem rowSound1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1338 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1338, numericCheck1338, reducedZero1338 B hB hF, mul_zero]

theorem reducedZero1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1339 (mixedVector B) = 0 := by
  have h734 : mixedVector B (Sum.inr 734) = Sparse.eval nodeValue734 (mixedVector B) := by
    change mixedMoment B node734 node734Labels = _
    exact sound734 B hB hF
  have h742 : mixedVector B (Sum.inr 742) = Sparse.eval nodeValue742 (mixedVector B) := by
    change mixedMoment B node742 node742Labels = _
    exact sound742 B hB hF
  have h743 : mixedVector B (Sum.inr 743) = Sparse.eval nodeValue743 (mixedVector B) := by
    change mixedMoment B node743 node743Labels = _
    exact sound743 B hB hF
  have h816 : mixedVector B (Sum.inr 816) = Sparse.eval nodeValue816 (mixedVector B) := by
    change mixedMoment B node816 node816Labels = _
    exact sound816 B hB hF
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1573, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h734, h742, h743, h816, h1653, h4069, reducedSource1339] using sourceEq1573 B hB

theorem rowSound1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1339 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1339, numericCheck1339, reducedZero1339 B hB hF, mul_zero]

theorem reducedZero1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1340 (mixedVector B) = 0 := by
  have h4071 : mixedVector B (Sum.inr 4071) = Sparse.eval nodeValue4071 (mixedVector B) := by
    change mixedMoment B node4071 node4071Labels = _
    exact sound4071 B hB hF
  have h4115 : mixedVector B (Sum.inr 4115) = Sparse.eval nodeValue4115 (mixedVector B) := by
    change mixedMoment B node4115 node4115Labels = _
    exact sound4115 B hB hF
  have h4121 : mixedVector B (Sum.inr 4121) = Sparse.eval nodeValue4121 (mixedVector B) := by
    change mixedMoment B node4121 node4121Labels = _
    exact sound4121 B hB hF
  have h4123 : mixedVector B (Sum.inr 4123) = Sparse.eval nodeValue4123 (mixedVector B) := by
    change mixedMoment B node4123 node4123Labels = _
    exact sound4123 B hB hF
  have h4132 : mixedVector B (Sum.inr 4132) = Sparse.eval nodeValue4132 (mixedVector B) := by
    change mixedMoment B node4132 node4132Labels = _
    exact sound4132 B hB hF
  have h4207 : mixedVector B (Sum.inr 4207) = Sparse.eval nodeValue4207 (mixedVector B) := by
    change mixedMoment B node4207 node4207Labels = _
    exact sound4207 B hB hF
  have h4212 : mixedVector B (Sum.inr 4212) = Sparse.eval nodeValue4212 (mixedVector B) := by
    change mixedMoment B node4212 node4212Labels = _
    exact sound4212 B hB hF
  have h4214 : mixedVector B (Sum.inr 4214) = Sparse.eval nodeValue4214 (mixedVector B) := by
    change mixedMoment B node4214 node4214Labels = _
    exact sound4214 B hB hF
  have h4223 : mixedVector B (Sum.inr 4223) = Sparse.eval nodeValue4223 (mixedVector B) := by
    change mixedMoment B node4223 node4223Labels = _
    exact sound4223 B hB hF
  have h4255 : mixedVector B (Sum.inr 4255) = Sparse.eval nodeValue4255 (mixedVector B) := by
    change mixedMoment B node4255 node4255Labels = _
    exact sound4255 B hB hF
  have h4256 : mixedVector B (Sum.inr 4256) = Sparse.eval nodeValue4256 (mixedVector B) := by
    change mixedMoment B node4256 node4256Labels = _
    exact sound4256 B hB hF
  have h4272 : mixedVector B (Sum.inr 4272) = Sparse.eval nodeValue4272 (mixedVector B) := by
    change mixedMoment B node4272 node4272Labels = _
    exact sound4272 B hB hF
  have h4273 : mixedVector B (Sum.inr 4273) = Sparse.eval nodeValue4273 (mixedVector B) := by
    change mixedMoment B node4273 node4273Labels = _
    exact sound4273 B hB hF
  have h4278 : mixedVector B (Sum.inr 4278) = Sparse.eval nodeValue4278 (mixedVector B) := by
    change mixedMoment B node4278 node4278Labels = _
    exact sound4278 B hB hF
  have h4279 : mixedVector B (Sum.inr 4279) = Sparse.eval nodeValue4279 (mixedVector B) := by
    change mixedMoment B node4279 node4279Labels = _
    exact sound4279 B hB hF
  have h4284 : mixedVector B (Sum.inr 4284) = Sparse.eval nodeValue4284 (mixedVector B) := by
    change mixedMoment B node4284 node4284Labels = _
    exact sound4284 B hB hF
  have h4404 : mixedVector B (Sum.inr 4404) = Sparse.eval nodeValue4404 (mixedVector B) := by
    change mixedMoment B node4404 node4404Labels = _
    exact sound4404 B hB hF
  have h4466 : mixedVector B (Sum.inr 4466) = Sparse.eval nodeValue4466 (mixedVector B) := by
    change mixedMoment B node4466 node4466Labels = _
    exact sound4466 B hB hF
  have h4467 : mixedVector B (Sum.inr 4467) = Sparse.eval nodeValue4467 (mixedVector B) := by
    change mixedMoment B node4467 node4467Labels = _
    exact sound4467 B hB hF
  have h4511 : mixedVector B (Sum.inr 4511) = Sparse.eval nodeValue4511 (mixedVector B) := by
    change mixedMoment B node4511 node4511Labels = _
    exact sound4511 B hB hF
  simpa only [sourceForm1574, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4071, h4115, h4121, h4123, h4132, h4207, h4212, h4214, h4223, h4255, h4256, h4272, h4273, h4278, h4279, h4284, h4404, h4466, h4467, h4511, reducedSource1340] using sourceEq1574 B hB

theorem rowSound1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1340 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1340, numericCheck1340, reducedZero1340 B hB hF, mul_zero]

theorem reducedZero1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1341 (mixedVector B) = 0 := by
  have h4059 : mixedVector B (Sum.inr 4059) = Sparse.eval nodeValue4059 (mixedVector B) := by
    change mixedMoment B node4059 node4059Labels = _
    exact sound4059 B hB hF
  have h4061 : mixedVector B (Sum.inr 4061) = Sparse.eval nodeValue4061 (mixedVector B) := by
    change mixedMoment B node4061 node4061Labels = _
    exact sound4061 B hB hF
  have h4065 : mixedVector B (Sum.inr 4065) = Sparse.eval nodeValue4065 (mixedVector B) := by
    change mixedMoment B node4065 node4065Labels = _
    exact sound4065 B hB hF
  have h4067 : mixedVector B (Sum.inr 4067) = Sparse.eval nodeValue4067 (mixedVector B) := by
    change mixedMoment B node4067 node4067Labels = _
    exact sound4067 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1575, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h4059, h4061, h4065, h4067, h4069, h4070, h4082, h4084, reducedSource1341] using sourceEq1575 B hB

theorem rowSound1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1341 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1341, numericCheck1341, reducedZero1341 B hB hF, mul_zero]

theorem reducedZero1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1342 (mixedVector B) = 0 := by
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h2521 : mixedVector B (Sum.inr 2521) = Sparse.eval nodeValue2521 (mixedVector B) := by
    change mixedMoment B node2521 node2521Labels = _
    exact sound2521 B hB hF
  have h3022 : mixedVector B (Sum.inr 3022) = Sparse.eval nodeValue3022 (mixedVector B) := by
    change mixedMoment B node3022 node3022Labels = _
    exact sound3022 B hB hF
  have h3049 : mixedVector B (Sum.inr 3049) = Sparse.eval nodeValue3049 (mixedVector B) := by
    change mixedMoment B node3049 node3049Labels = _
    exact sound3049 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1576, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1716, h2521, h3022, h3049, h3305, h4069, reducedSource1342] using sourceEq1576 B hB

theorem rowSound1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1342 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1342, numericCheck1342, reducedZero1342 B hB hF, mul_zero]

theorem reducedZero1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1343 (mixedVector B) = 0 := by
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1716 : mixedVector B (Sum.inr 1716) = Sparse.eval nodeValue1716 (mixedVector B) := by
    change mixedMoment B node1716 node1716Labels = _
    exact sound1716 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1577, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1714, h1716, h1728, h1739, h3305, h4069, reducedSource1343] using sourceEq1577 B hB

theorem rowSound1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1343 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1343, numericCheck1343, reducedZero1343 B hB hF, mul_zero]

theorem sourceRowsAt1328 : MixedData.sourceRows (1328 : Fin 2425) =
    MixedData.row1328 := by decide +kernel

theorem sourceRowsAt1329 : MixedData.sourceRows (1329 : Fin 2425) =
    MixedData.row1329 := by decide +kernel

theorem sourceRowsAt1330 : MixedData.sourceRows (1330 : Fin 2425) =
    MixedData.row1330 := by decide +kernel

theorem sourceRowsAt1331 : MixedData.sourceRows (1331 : Fin 2425) =
    MixedData.row1331 := by decide +kernel

theorem sourceRowsAt1332 : MixedData.sourceRows (1332 : Fin 2425) =
    MixedData.row1332 := by decide +kernel

theorem sourceRowsAt1333 : MixedData.sourceRows (1333 : Fin 2425) =
    MixedData.row1333 := by decide +kernel

theorem sourceRowsAt1334 : MixedData.sourceRows (1334 : Fin 2425) =
    MixedData.row1334 := by decide +kernel

theorem sourceRowsAt1335 : MixedData.sourceRows (1335 : Fin 2425) =
    MixedData.row1335 := by decide +kernel

theorem sourceRowsAt1336 : MixedData.sourceRows (1336 : Fin 2425) =
    MixedData.row1336 := by decide +kernel

theorem sourceRowsAt1337 : MixedData.sourceRows (1337 : Fin 2425) =
    MixedData.row1337 := by decide +kernel

theorem sourceRowsAt1338 : MixedData.sourceRows (1338 : Fin 2425) =
    MixedData.row1338 := by decide +kernel

theorem sourceRowsAt1339 : MixedData.sourceRows (1339 : Fin 2425) =
    MixedData.row1339 := by decide +kernel

theorem sourceRowsAt1340 : MixedData.sourceRows (1340 : Fin 2425) =
    MixedData.row1340 := by decide +kernel

theorem sourceRowsAt1341 : MixedData.sourceRows (1341 : Fin 2425) =
    MixedData.row1341 := by decide +kernel

theorem sourceRowsAt1342 : MixedData.sourceRows (1342 : Fin 2425) =
    MixedData.row1342 := by decide +kernel

theorem sourceRowsAt1343 : MixedData.sourceRows (1343 : Fin 2425) =
    MixedData.row1343 := by decide +kernel

theorem chunkSound83 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 83) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1328 ∨ k.val = 1329 ∨ k.val = 1330 ∨ k.val = 1331 ∨ k.val = 1332 ∨ k.val = 1333 ∨ k.val = 1334 ∨ k.val = 1335 ∨ k.val = 1336 ∨ k.val = 1337 ∨ k.val = 1338 ∨ k.val = 1339 ∨ k.val = 1340 ∨ k.val = 1341 ∨ k.val = 1342 ∨ k.val = 1343 := by omega
  rcases heq with h1328 | h1329 | h1330 | h1331 | h1332 | h1333 | h1334 | h1335 | h1336 | h1337 | h1338 | h1339 | h1340 | h1341 | h1342 | h1343
  · have he : k = (1328 : Fin 2425) := Fin.ext h1328
    subst k
    rw [sourceRowsAt1328]
    exact rowSound1328 B hB hF
  · have he : k = (1329 : Fin 2425) := Fin.ext h1329
    subst k
    rw [sourceRowsAt1329]
    exact rowSound1329 B hB hF
  · have he : k = (1330 : Fin 2425) := Fin.ext h1330
    subst k
    rw [sourceRowsAt1330]
    exact rowSound1330 B hB hF
  · have he : k = (1331 : Fin 2425) := Fin.ext h1331
    subst k
    rw [sourceRowsAt1331]
    exact rowSound1331 B hB hF
  · have he : k = (1332 : Fin 2425) := Fin.ext h1332
    subst k
    rw [sourceRowsAt1332]
    exact rowSound1332 B hB hF
  · have he : k = (1333 : Fin 2425) := Fin.ext h1333
    subst k
    rw [sourceRowsAt1333]
    exact rowSound1333 B hB hF
  · have he : k = (1334 : Fin 2425) := Fin.ext h1334
    subst k
    rw [sourceRowsAt1334]
    exact rowSound1334 B hB hF
  · have he : k = (1335 : Fin 2425) := Fin.ext h1335
    subst k
    rw [sourceRowsAt1335]
    exact rowSound1335 B hB hF
  · have he : k = (1336 : Fin 2425) := Fin.ext h1336
    subst k
    rw [sourceRowsAt1336]
    exact rowSound1336 B hB hF
  · have he : k = (1337 : Fin 2425) := Fin.ext h1337
    subst k
    rw [sourceRowsAt1337]
    exact rowSound1337 B hB hF
  · have he : k = (1338 : Fin 2425) := Fin.ext h1338
    subst k
    rw [sourceRowsAt1338]
    exact rowSound1338 B hB hF
  · have he : k = (1339 : Fin 2425) := Fin.ext h1339
    subst k
    rw [sourceRowsAt1339]
    exact rowSound1339 B hB hF
  · have he : k = (1340 : Fin 2425) := Fin.ext h1340
    subst k
    rw [sourceRowsAt1340]
    exact rowSound1340 B hB hF
  · have he : k = (1341 : Fin 2425) := Fin.ext h1341
    subst k
    rw [sourceRowsAt1341]
    exact rowSound1341 B hB hF
  · have he : k = (1342 : Fin 2425) := Fin.ext h1342
    subst k
    rw [sourceRowsAt1342]
    exact rowSound1342 B hB hF
  · have he : k = (1343 : Fin 2425) := Fin.ext h1343
    subst k
    rw [sourceRowsAt1343]
    exact rowSound1343 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
