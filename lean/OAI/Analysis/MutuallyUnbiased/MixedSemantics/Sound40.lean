import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons40

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2560 node2560Labels = Sparse.eval nodeValue2560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2560) = mixedMoment B node2560 node2560Labels := rfl
  simpa [nodeValue2560, Sparse.eval] using hc.symm

theorem sound2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2561 node2561Labels = Sparse.eval nodeValue2561 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2561) = mixedMoment B node2561 node2561Labels := rfl
  simpa [nodeValue2561, Sparse.eval] using hc.symm

theorem sound2562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2562 node2562Labels = Sparse.eval nodeValue2562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2562) = mixedMoment B node2562 node2562Labels := rfl
  simpa [nodeValue2562, Sparse.eval] using hc.symm

theorem sound2563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2563 node2563Labels = Sparse.eval nodeValue2563 (mixedVector B) := by
  have h := singleton2563 B _hB
  rw [sound199 B _hB _hF] at h
  norm_num [nodeValue2563, nodeValue199, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2564 node2564Labels = Sparse.eval nodeValue2564 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2564) = mixedMoment B node2564 node2564Labels := rfl
  simpa [nodeValue2564, Sparse.eval] using hc.symm

theorem sound2565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2565 node2565Labels = Sparse.eval nodeValue2565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2565) = mixedMoment B node2565 node2565Labels := rfl
  simpa [nodeValue2565, Sparse.eval] using hc.symm

theorem sound2566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2566 node2566Labels = Sparse.eval nodeValue2566 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2566) = mixedMoment B node2566 node2566Labels := rfl
  simpa [nodeValue2566, Sparse.eval] using hc.symm

theorem sound2567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2567 node2567Labels = Sparse.eval nodeValue2567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2567) = mixedMoment B node2567 node2567Labels := rfl
  simpa [nodeValue2567, Sparse.eval] using hc.symm

theorem sound2568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2568 node2568Labels = Sparse.eval nodeValue2568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2568) = mixedMoment B node2568 node2568Labels := rfl
  simpa [nodeValue2568, Sparse.eval] using hc.symm

theorem sound2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2569 node2569Labels = Sparse.eval nodeValue2569 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2569) = mixedMoment B node2569 node2569Labels := rfl
  simpa [nodeValue2569, Sparse.eval] using hc.symm

theorem sound2570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2570 node2570Labels = Sparse.eval nodeValue2570 (mixedVector B) := by
  have h := singleton2570 B _hB
  rw [sound326 B _hB _hF] at h
  norm_num [nodeValue2570, nodeValue326, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2571 node2571Labels = Sparse.eval nodeValue2571 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2571) = mixedMoment B node2571 node2571Labels := rfl
  simpa [nodeValue2571, Sparse.eval] using hc.symm

theorem sound2572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2572 node2572Labels = Sparse.eval nodeValue2572 (mixedVector B) := by
  have h := singleton2572 B _hB
  rw [sound305 B _hB _hF] at h
  norm_num [nodeValue2572, nodeValue305, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2573 node2573Labels = Sparse.eval nodeValue2573 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2573) = mixedMoment B node2573 node2573Labels := rfl
  simpa [nodeValue2573, Sparse.eval] using hc.symm

theorem sound2574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2574 node2574Labels = Sparse.eval nodeValue2574 (mixedVector B) := by
  have h := singleton2574 B _hB
  rw [sound224 B _hB _hF] at h
  norm_num [nodeValue2574, nodeValue224, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2575 node2575Labels = Sparse.eval nodeValue2575 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2575) = mixedMoment B node2575 node2575Labels := rfl
  simpa [nodeValue2575, Sparse.eval] using hc.symm

theorem sound2576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2576 node2576Labels = Sparse.eval nodeValue2576 (mixedVector B) := by
  have h := singleton2576 B _hB
  rw [sound329 B _hB _hF] at h
  norm_num [nodeValue2576, nodeValue329, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2577 node2577Labels = Sparse.eval nodeValue2577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2577) = mixedMoment B node2577 node2577Labels := rfl
  simpa [nodeValue2577, Sparse.eval] using hc.symm

theorem sound2578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2578 node2578Labels = Sparse.eval nodeValue2578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2578) = mixedMoment B node2578 node2578Labels := rfl
  simpa [nodeValue2578, Sparse.eval] using hc.symm

theorem sound2579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2579 node2579Labels = Sparse.eval nodeValue2579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2579) = mixedMoment B node2579 node2579Labels := rfl
  simpa [nodeValue2579, Sparse.eval] using hc.symm

theorem sound2580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2580 node2580Labels = Sparse.eval nodeValue2580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2580) = mixedMoment B node2580 node2580Labels := rfl
  simpa [nodeValue2580, Sparse.eval] using hc.symm

theorem sound2581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2581 node2581Labels = Sparse.eval nodeValue2581 (mixedVector B) := by
  have h := singleton2581 B _hB
  rw [sound203 B _hB _hF] at h
  norm_num [nodeValue2581, nodeValue203, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2582 node2582Labels = Sparse.eval nodeValue2582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2582) = mixedMoment B node2582 node2582Labels := rfl
  simpa [nodeValue2582, Sparse.eval] using hc.symm

theorem sound2583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2583 node2583Labels = Sparse.eval nodeValue2583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2583) = mixedMoment B node2583 node2583Labels := rfl
  simpa [nodeValue2583, Sparse.eval] using hc.symm

theorem sound2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2584 node2584Labels = Sparse.eval nodeValue2584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2584) = mixedMoment B node2584 node2584Labels := rfl
  simpa [nodeValue2584, Sparse.eval] using hc.symm

theorem sound2585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2585 node2585Labels = Sparse.eval nodeValue2585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2585) = mixedMoment B node2585 node2585Labels := rfl
  simpa [nodeValue2585, Sparse.eval] using hc.symm

theorem sound2586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2586 node2586Labels = Sparse.eval nodeValue2586 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2586) = mixedMoment B node2586 node2586Labels := rfl
  simpa [nodeValue2586, Sparse.eval] using hc.symm

theorem sound2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2587 node2587Labels = Sparse.eval nodeValue2587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2587) = mixedMoment B node2587 node2587Labels := rfl
  simpa [nodeValue2587, Sparse.eval] using hc.symm

theorem sound2588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2588 node2588Labels = Sparse.eval nodeValue2588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2588) = mixedMoment B node2588 node2588Labels := rfl
  simpa [nodeValue2588, Sparse.eval] using hc.symm

theorem sound2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2589 node2589Labels = Sparse.eval nodeValue2589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2589) = mixedMoment B node2589 node2589Labels := rfl
  simpa [nodeValue2589, Sparse.eval] using hc.symm

theorem sound2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2590 node2590Labels = Sparse.eval nodeValue2590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2590) = mixedMoment B node2590 node2590Labels := rfl
  simpa [nodeValue2590, Sparse.eval] using hc.symm

theorem sound2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2591 node2591Labels = Sparse.eval nodeValue2591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2591) = mixedMoment B node2591 node2591Labels := rfl
  simpa [nodeValue2591, Sparse.eval] using hc.symm

theorem sound2592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2592 node2592Labels = Sparse.eval nodeValue2592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2592) = mixedMoment B node2592 node2592Labels := rfl
  simpa [nodeValue2592, Sparse.eval] using hc.symm

theorem sound2593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2593 node2593Labels = Sparse.eval nodeValue2593 (mixedVector B) := by
  have h := singleton2593 B _hB
  rw [sound334 B _hB _hF] at h
  norm_num [nodeValue2593, nodeValue334, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2594 node2594Labels = Sparse.eval nodeValue2594 (mixedVector B) := by
  have h := singleton2594 B _hB
  rw [sound335 B _hB _hF] at h
  norm_num [nodeValue2594, nodeValue335, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2595 node2595Labels = Sparse.eval nodeValue2595 (mixedVector B) := by
  have h := singleton2595 B _hB
  rw [sound336 B _hB _hF] at h
  norm_num [nodeValue2595, nodeValue336, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2596 node2596Labels = Sparse.eval nodeValue2596 (mixedVector B) := by
  have h := singleton2596 B _hB
  rw [sound337 B _hB _hF] at h
  norm_num [nodeValue2596, nodeValue337, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2597 node2597Labels = Sparse.eval nodeValue2597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2597) = mixedMoment B node2597 node2597Labels := rfl
  simpa [nodeValue2597, Sparse.eval] using hc.symm

theorem sound2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2598 node2598Labels = Sparse.eval nodeValue2598 (mixedVector B) := by
  have h := singleton2598 B _hB
  rw [sound338 B _hB _hF] at h
  norm_num [nodeValue2598, nodeValue338, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2599 node2599Labels = Sparse.eval nodeValue2599 (mixedVector B) := by
  have h := singleton2599 B _hB
  rw [sound339 B _hB _hF] at h
  norm_num [nodeValue2599, nodeValue339, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2600 node2600Labels = Sparse.eval nodeValue2600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2600) = mixedMoment B node2600 node2600Labels := rfl
  simpa [nodeValue2600, Sparse.eval] using hc.symm

theorem sound2601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2601 node2601Labels = Sparse.eval nodeValue2601 (mixedVector B) := by
  have h := singleton2601 B _hB
  rw [sound341 B _hB _hF] at h
  norm_num [nodeValue2601, nodeValue341, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2602 node2602Labels = Sparse.eval nodeValue2602 (mixedVector B) := by
  have h := singleton2602 B _hB
  rw [sound249 B _hB _hF] at h
  norm_num [nodeValue2602, nodeValue249, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2603 node2603Labels = Sparse.eval nodeValue2603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2603) = mixedMoment B node2603 node2603Labels := rfl
  simpa [nodeValue2603, Sparse.eval] using hc.symm

theorem sound2604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2604 node2604Labels = Sparse.eval nodeValue2604 (mixedVector B) := by
  have h := singleton2604 B _hB
  rw [sound343 B _hB _hF] at h
  norm_num [nodeValue2604, nodeValue343, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2605 node2605Labels = Sparse.eval nodeValue2605 (mixedVector B) := by
  have h := singleton2605 B _hB
  rw [sound344 B _hB _hF] at h
  norm_num [nodeValue2605, nodeValue344, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound2606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2606 node2606Labels = Sparse.eval nodeValue2606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2606) = mixedMoment B node2606 node2606Labels := rfl
  simpa [nodeValue2606, Sparse.eval] using hc.symm

theorem sound2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2607 node2607Labels = Sparse.eval nodeValue2607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2607) = mixedMoment B node2607 node2607Labels := rfl
  simpa [nodeValue2607, Sparse.eval] using hc.symm

theorem sound2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2608 node2608Labels = Sparse.eval nodeValue2608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2608) = mixedMoment B node2608 node2608Labels := rfl
  simpa [nodeValue2608, Sparse.eval] using hc.symm

theorem sound2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2609 node2609Labels = Sparse.eval nodeValue2609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2609) = mixedMoment B node2609 node2609Labels := rfl
  simpa [nodeValue2609, Sparse.eval] using hc.symm

theorem sound2610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2610 node2610Labels = Sparse.eval nodeValue2610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2610) = mixedMoment B node2610 node2610Labels := rfl
  simpa [nodeValue2610, Sparse.eval] using hc.symm

theorem sound2611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2611 node2611Labels = Sparse.eval nodeValue2611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2611) = mixedMoment B node2611 node2611Labels := rfl
  simpa [nodeValue2611, Sparse.eval] using hc.symm

theorem sound2612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2612 node2612Labels = Sparse.eval nodeValue2612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2612) = mixedMoment B node2612 node2612Labels := rfl
  simpa [nodeValue2612, Sparse.eval] using hc.symm

theorem sound2613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2613 node2613Labels = Sparse.eval nodeValue2613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2613) = mixedMoment B node2613 node2613Labels := rfl
  simpa [nodeValue2613, Sparse.eval] using hc.symm

theorem sound2614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2614 node2614Labels = Sparse.eval nodeValue2614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2614) = mixedMoment B node2614 node2614Labels := rfl
  simpa [nodeValue2614, Sparse.eval] using hc.symm

theorem sound2615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2615 node2615Labels = Sparse.eval nodeValue2615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2615) = mixedMoment B node2615 node2615Labels := rfl
  simpa [nodeValue2615, Sparse.eval] using hc.symm

theorem sound2616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2616 node2616Labels = Sparse.eval nodeValue2616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2616) = mixedMoment B node2616 node2616Labels := rfl
  simpa [nodeValue2616, Sparse.eval] using hc.symm

theorem sound2617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2617 node2617Labels = Sparse.eval nodeValue2617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2617) = mixedMoment B node2617 node2617Labels := rfl
  simpa [nodeValue2617, Sparse.eval] using hc.symm

theorem sound2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2618 node2618Labels = Sparse.eval nodeValue2618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2618) = mixedMoment B node2618 node2618Labels := rfl
  simpa [nodeValue2618, Sparse.eval] using hc.symm

theorem sound2619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2619 node2619Labels = Sparse.eval nodeValue2619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2619) = mixedMoment B node2619 node2619Labels := rfl
  simpa [nodeValue2619, Sparse.eval] using hc.symm

theorem sound2620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2620 node2620Labels = Sparse.eval nodeValue2620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2620) = mixedMoment B node2620 node2620Labels := rfl
  simpa [nodeValue2620, Sparse.eval] using hc.symm

theorem sound2621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2621 node2621Labels = Sparse.eval nodeValue2621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2621) = mixedMoment B node2621 node2621Labels := rfl
  simpa [nodeValue2621, Sparse.eval] using hc.symm

theorem sound2622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2622 node2622Labels = Sparse.eval nodeValue2622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2622) = mixedMoment B node2622 node2622Labels := rfl
  simpa [nodeValue2622, Sparse.eval] using hc.symm

theorem sound2623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2623 node2623Labels = Sparse.eval nodeValue2623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2623) = mixedMoment B node2623 node2623Labels := rfl
  simpa [nodeValue2623, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
