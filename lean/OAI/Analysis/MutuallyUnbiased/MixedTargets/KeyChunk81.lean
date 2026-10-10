import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound81
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2592 : keyMomentRows (2592 : Fin 2886) =
    keyMomentRow2592 := by decide +kernel

theorem keyMomentRowsAt2593 : keyMomentRows (2593 : Fin 2886) =
    keyMomentRow2593 := by decide +kernel

theorem keyMomentRowsAt2594 : keyMomentRows (2594 : Fin 2886) =
    keyMomentRow2594 := by decide +kernel

theorem keyMomentRowsAt2595 : keyMomentRows (2595 : Fin 2886) =
    keyMomentRow2595 := by decide +kernel

theorem keyMomentRowsAt2596 : keyMomentRows (2596 : Fin 2886) =
    keyMomentRow2596 := by decide +kernel

theorem keyMomentRowsAt2597 : keyMomentRows (2597 : Fin 2886) =
    keyMomentRow2597 := by decide +kernel

theorem keyMomentRowsAt2598 : keyMomentRows (2598 : Fin 2886) =
    keyMomentRow2598 := by decide +kernel

theorem keyMomentRowsAt2599 : keyMomentRows (2599 : Fin 2886) =
    keyMomentRow2599 := by decide +kernel

theorem keyMomentRowsAt2600 : keyMomentRows (2600 : Fin 2886) =
    keyMomentRow2600 := by decide +kernel

theorem keyMomentRowsAt2601 : keyMomentRows (2601 : Fin 2886) =
    keyMomentRow2601 := by decide +kernel

theorem keyMomentRowsAt2602 : keyMomentRows (2602 : Fin 2886) =
    keyMomentRow2602 := by decide +kernel

theorem keyMomentRowsAt2603 : keyMomentRows (2603 : Fin 2886) =
    keyMomentRow2603 := by decide +kernel

theorem keyMomentRowsAt2604 : keyMomentRows (2604 : Fin 2886) =
    keyMomentRow2604 := by decide +kernel

theorem keyMomentRowsAt2605 : keyMomentRows (2605 : Fin 2886) =
    keyMomentRow2605 := by decide +kernel

theorem keyMomentRowsAt2606 : keyMomentRows (2606 : Fin 2886) =
    keyMomentRow2606 := by decide +kernel

theorem keyMomentRowsAt2607 : keyMomentRows (2607 : Fin 2886) =
    keyMomentRow2607 := by decide +kernel

theorem keyMomentRowsAt2608 : keyMomentRows (2608 : Fin 2886) =
    keyMomentRow2608 := by decide +kernel

theorem keyMomentRowsAt2609 : keyMomentRows (2609 : Fin 2886) =
    keyMomentRow2609 := by decide +kernel

theorem keyMomentRowsAt2610 : keyMomentRows (2610 : Fin 2886) =
    keyMomentRow2610 := by decide +kernel

theorem keyMomentRowsAt2611 : keyMomentRows (2611 : Fin 2886) =
    keyMomentRow2611 := by decide +kernel

theorem keyMomentRowsAt2612 : keyMomentRows (2612 : Fin 2886) =
    keyMomentRow2612 := by decide +kernel

theorem keyMomentRowsAt2613 : keyMomentRows (2613 : Fin 2886) =
    keyMomentRow2613 := by decide +kernel

theorem keyMomentRowsAt2614 : keyMomentRows (2614 : Fin 2886) =
    keyMomentRow2614 := by decide +kernel

theorem keyMomentRowsAt2615 : keyMomentRows (2615 : Fin 2886) =
    keyMomentRow2615 := by decide +kernel

theorem keyMomentRowsAt2616 : keyMomentRows (2616 : Fin 2886) =
    keyMomentRow2616 := by decide +kernel

theorem keyMomentRowsAt2617 : keyMomentRows (2617 : Fin 2886) =
    keyMomentRow2617 := by decide +kernel

theorem keyMomentRowsAt2618 : keyMomentRows (2618 : Fin 2886) =
    keyMomentRow2618 := by decide +kernel

theorem keyMomentRowsAt2619 : keyMomentRows (2619 : Fin 2886) =
    keyMomentRow2619 := by decide +kernel

theorem keyMomentRowsAt2620 : keyMomentRows (2620 : Fin 2886) =
    keyMomentRow2620 := by decide +kernel

theorem keyMomentRowsAt2621 : keyMomentRows (2621 : Fin 2886) =
    keyMomentRow2621 := by decide +kernel

theorem keyMomentRowsAt2622 : keyMomentRows (2622 : Fin 2886) =
    keyMomentRow2622 := by decide +kernel

theorem keyMomentRowsAt2623 : keyMomentRows (2623 : Fin 2886) =
    keyMomentRow2623 := by decide +kernel

theorem keyMomentChunkSound81 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 81) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2592 ∨ k.val = 2593 ∨ k.val = 2594 ∨ k.val = 2595 ∨ k.val = 2596 ∨ k.val = 2597 ∨ k.val = 2598 ∨ k.val = 2599 ∨ k.val = 2600 ∨ k.val = 2601 ∨ k.val = 2602 ∨ k.val = 2603 ∨ k.val = 2604 ∨ k.val = 2605 ∨ k.val = 2606 ∨ k.val = 2607 ∨ k.val = 2608 ∨ k.val = 2609 ∨ k.val = 2610 ∨ k.val = 2611 ∨ k.val = 2612 ∨ k.val = 2613 ∨ k.val = 2614 ∨ k.val = 2615 ∨ k.val = 2616 ∨ k.val = 2617 ∨ k.val = 2618 ∨ k.val = 2619 ∨ k.val = 2620 ∨ k.val = 2621 ∨ k.val = 2622 ∨ k.val = 2623 := by omega
  rcases heq with h2592 | h2593 | h2594 | h2595 | h2596 | h2597 | h2598 | h2599 | h2600 | h2601 | h2602 | h2603 | h2604 | h2605 | h2606 | h2607 | h2608 | h2609 | h2610 | h2611 | h2612 | h2613 | h2614 | h2615 | h2616 | h2617 | h2618 | h2619 | h2620 | h2621 | h2622 | h2623
  · have he : k = (2592 : Fin 2886) := Fin.ext h2592
    subst k
    rw [keyMomentRowsAt2592]
    exact keyMoment2592 B hB
  · have he : k = (2593 : Fin 2886) := Fin.ext h2593
    subst k
    rw [keyMomentRowsAt2593]
    exact keyMoment2593 B hB
  · have he : k = (2594 : Fin 2886) := Fin.ext h2594
    subst k
    rw [keyMomentRowsAt2594]
    exact keyMoment2594 B hB
  · have he : k = (2595 : Fin 2886) := Fin.ext h2595
    subst k
    rw [keyMomentRowsAt2595]
    exact keyMoment2595 B hB
  · have he : k = (2596 : Fin 2886) := Fin.ext h2596
    subst k
    rw [keyMomentRowsAt2596]
    exact keyMoment2596 B hB
  · have he : k = (2597 : Fin 2886) := Fin.ext h2597
    subst k
    rw [keyMomentRowsAt2597]
    exact keyMoment2597 B hB
  · have he : k = (2598 : Fin 2886) := Fin.ext h2598
    subst k
    rw [keyMomentRowsAt2598]
    exact keyMoment2598 B hB
  · have he : k = (2599 : Fin 2886) := Fin.ext h2599
    subst k
    rw [keyMomentRowsAt2599]
    exact keyMoment2599 B hB
  · have he : k = (2600 : Fin 2886) := Fin.ext h2600
    subst k
    rw [keyMomentRowsAt2600]
    exact keyMoment2600 B hB
  · have he : k = (2601 : Fin 2886) := Fin.ext h2601
    subst k
    rw [keyMomentRowsAt2601]
    exact keyMoment2601 B hB
  · have he : k = (2602 : Fin 2886) := Fin.ext h2602
    subst k
    rw [keyMomentRowsAt2602]
    exact keyMoment2602 B hB
  · have he : k = (2603 : Fin 2886) := Fin.ext h2603
    subst k
    rw [keyMomentRowsAt2603]
    exact keyMoment2603 B hB
  · have he : k = (2604 : Fin 2886) := Fin.ext h2604
    subst k
    rw [keyMomentRowsAt2604]
    exact keyMoment2604 B hB
  · have he : k = (2605 : Fin 2886) := Fin.ext h2605
    subst k
    rw [keyMomentRowsAt2605]
    exact keyMoment2605 B hB
  · have he : k = (2606 : Fin 2886) := Fin.ext h2606
    subst k
    rw [keyMomentRowsAt2606]
    exact keyMoment2606 B hB
  · have he : k = (2607 : Fin 2886) := Fin.ext h2607
    subst k
    rw [keyMomentRowsAt2607]
    exact keyMoment2607 B hB
  · have he : k = (2608 : Fin 2886) := Fin.ext h2608
    subst k
    rw [keyMomentRowsAt2608]
    exact keyMoment2608 B hB
  · have he : k = (2609 : Fin 2886) := Fin.ext h2609
    subst k
    rw [keyMomentRowsAt2609]
    exact keyMoment2609 B hB
  · have he : k = (2610 : Fin 2886) := Fin.ext h2610
    subst k
    rw [keyMomentRowsAt2610]
    exact keyMoment2610 B hB
  · have he : k = (2611 : Fin 2886) := Fin.ext h2611
    subst k
    rw [keyMomentRowsAt2611]
    exact keyMoment2611 B hB
  · have he : k = (2612 : Fin 2886) := Fin.ext h2612
    subst k
    rw [keyMomentRowsAt2612]
    exact keyMoment2612 B hB
  · have he : k = (2613 : Fin 2886) := Fin.ext h2613
    subst k
    rw [keyMomentRowsAt2613]
    exact keyMoment2613 B hB
  · have he : k = (2614 : Fin 2886) := Fin.ext h2614
    subst k
    rw [keyMomentRowsAt2614]
    exact keyMoment2614 B hB
  · have he : k = (2615 : Fin 2886) := Fin.ext h2615
    subst k
    rw [keyMomentRowsAt2615]
    exact keyMoment2615 B hB
  · have he : k = (2616 : Fin 2886) := Fin.ext h2616
    subst k
    rw [keyMomentRowsAt2616]
    exact keyMoment2616 B hB
  · have he : k = (2617 : Fin 2886) := Fin.ext h2617
    subst k
    rw [keyMomentRowsAt2617]
    exact keyMoment2617 B hB
  · have he : k = (2618 : Fin 2886) := Fin.ext h2618
    subst k
    rw [keyMomentRowsAt2618]
    exact keyMoment2618 B hB
  · have he : k = (2619 : Fin 2886) := Fin.ext h2619
    subst k
    rw [keyMomentRowsAt2619]
    exact keyMoment2619 B hB
  · have he : k = (2620 : Fin 2886) := Fin.ext h2620
    subst k
    rw [keyMomentRowsAt2620]
    exact keyMoment2620 B hB
  · have he : k = (2621 : Fin 2886) := Fin.ext h2621
    subst k
    rw [keyMomentRowsAt2621]
    exact keyMoment2621 B hB
  · have he : k = (2622 : Fin 2886) := Fin.ext h2622
    subst k
    rw [keyMomentRowsAt2622]
    exact keyMoment2622 B hB
  · have he : k = (2623 : Fin 2886) := Fin.ext h2623
    subst k
    rw [keyMomentRowsAt2623]
    exact keyMoment2623 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
