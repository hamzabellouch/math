import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound80
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2560 : keyMomentRows (2560 : Fin 2886) =
    keyMomentRow2560 := by decide +kernel

theorem keyMomentRowsAt2561 : keyMomentRows (2561 : Fin 2886) =
    keyMomentRow2561 := by decide +kernel

theorem keyMomentRowsAt2562 : keyMomentRows (2562 : Fin 2886) =
    keyMomentRow2562 := by decide +kernel

theorem keyMomentRowsAt2563 : keyMomentRows (2563 : Fin 2886) =
    keyMomentRow2563 := by decide +kernel

theorem keyMomentRowsAt2564 : keyMomentRows (2564 : Fin 2886) =
    keyMomentRow2564 := by decide +kernel

theorem keyMomentRowsAt2565 : keyMomentRows (2565 : Fin 2886) =
    keyMomentRow2565 := by decide +kernel

theorem keyMomentRowsAt2566 : keyMomentRows (2566 : Fin 2886) =
    keyMomentRow2566 := by decide +kernel

theorem keyMomentRowsAt2567 : keyMomentRows (2567 : Fin 2886) =
    keyMomentRow2567 := by decide +kernel

theorem keyMomentRowsAt2568 : keyMomentRows (2568 : Fin 2886) =
    keyMomentRow2568 := by decide +kernel

theorem keyMomentRowsAt2569 : keyMomentRows (2569 : Fin 2886) =
    keyMomentRow2569 := by decide +kernel

theorem keyMomentRowsAt2570 : keyMomentRows (2570 : Fin 2886) =
    keyMomentRow2570 := by decide +kernel

theorem keyMomentRowsAt2571 : keyMomentRows (2571 : Fin 2886) =
    keyMomentRow2571 := by decide +kernel

theorem keyMomentRowsAt2572 : keyMomentRows (2572 : Fin 2886) =
    keyMomentRow2572 := by decide +kernel

theorem keyMomentRowsAt2573 : keyMomentRows (2573 : Fin 2886) =
    keyMomentRow2573 := by decide +kernel

theorem keyMomentRowsAt2574 : keyMomentRows (2574 : Fin 2886) =
    keyMomentRow2574 := by decide +kernel

theorem keyMomentRowsAt2575 : keyMomentRows (2575 : Fin 2886) =
    keyMomentRow2575 := by decide +kernel

theorem keyMomentRowsAt2576 : keyMomentRows (2576 : Fin 2886) =
    keyMomentRow2576 := by decide +kernel

theorem keyMomentRowsAt2577 : keyMomentRows (2577 : Fin 2886) =
    keyMomentRow2577 := by decide +kernel

theorem keyMomentRowsAt2578 : keyMomentRows (2578 : Fin 2886) =
    keyMomentRow2578 := by decide +kernel

theorem keyMomentRowsAt2579 : keyMomentRows (2579 : Fin 2886) =
    keyMomentRow2579 := by decide +kernel

theorem keyMomentRowsAt2580 : keyMomentRows (2580 : Fin 2886) =
    keyMomentRow2580 := by decide +kernel

theorem keyMomentRowsAt2581 : keyMomentRows (2581 : Fin 2886) =
    keyMomentRow2581 := by decide +kernel

theorem keyMomentRowsAt2582 : keyMomentRows (2582 : Fin 2886) =
    keyMomentRow2582 := by decide +kernel

theorem keyMomentRowsAt2583 : keyMomentRows (2583 : Fin 2886) =
    keyMomentRow2583 := by decide +kernel

theorem keyMomentRowsAt2584 : keyMomentRows (2584 : Fin 2886) =
    keyMomentRow2584 := by decide +kernel

theorem keyMomentRowsAt2585 : keyMomentRows (2585 : Fin 2886) =
    keyMomentRow2585 := by decide +kernel

theorem keyMomentRowsAt2586 : keyMomentRows (2586 : Fin 2886) =
    keyMomentRow2586 := by decide +kernel

theorem keyMomentRowsAt2587 : keyMomentRows (2587 : Fin 2886) =
    keyMomentRow2587 := by decide +kernel

theorem keyMomentRowsAt2588 : keyMomentRows (2588 : Fin 2886) =
    keyMomentRow2588 := by decide +kernel

theorem keyMomentRowsAt2589 : keyMomentRows (2589 : Fin 2886) =
    keyMomentRow2589 := by decide +kernel

theorem keyMomentRowsAt2590 : keyMomentRows (2590 : Fin 2886) =
    keyMomentRow2590 := by decide +kernel

theorem keyMomentRowsAt2591 : keyMomentRows (2591 : Fin 2886) =
    keyMomentRow2591 := by decide +kernel

theorem keyMomentChunkSound80 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 80) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2560 ∨ k.val = 2561 ∨ k.val = 2562 ∨ k.val = 2563 ∨ k.val = 2564 ∨ k.val = 2565 ∨ k.val = 2566 ∨ k.val = 2567 ∨ k.val = 2568 ∨ k.val = 2569 ∨ k.val = 2570 ∨ k.val = 2571 ∨ k.val = 2572 ∨ k.val = 2573 ∨ k.val = 2574 ∨ k.val = 2575 ∨ k.val = 2576 ∨ k.val = 2577 ∨ k.val = 2578 ∨ k.val = 2579 ∨ k.val = 2580 ∨ k.val = 2581 ∨ k.val = 2582 ∨ k.val = 2583 ∨ k.val = 2584 ∨ k.val = 2585 ∨ k.val = 2586 ∨ k.val = 2587 ∨ k.val = 2588 ∨ k.val = 2589 ∨ k.val = 2590 ∨ k.val = 2591 := by omega
  rcases heq with h2560 | h2561 | h2562 | h2563 | h2564 | h2565 | h2566 | h2567 | h2568 | h2569 | h2570 | h2571 | h2572 | h2573 | h2574 | h2575 | h2576 | h2577 | h2578 | h2579 | h2580 | h2581 | h2582 | h2583 | h2584 | h2585 | h2586 | h2587 | h2588 | h2589 | h2590 | h2591
  · have he : k = (2560 : Fin 2886) := Fin.ext h2560
    subst k
    rw [keyMomentRowsAt2560]
    exact keyMoment2560 B hB
  · have he : k = (2561 : Fin 2886) := Fin.ext h2561
    subst k
    rw [keyMomentRowsAt2561]
    exact keyMoment2561 B hB
  · have he : k = (2562 : Fin 2886) := Fin.ext h2562
    subst k
    rw [keyMomentRowsAt2562]
    exact keyMoment2562 B hB
  · have he : k = (2563 : Fin 2886) := Fin.ext h2563
    subst k
    rw [keyMomentRowsAt2563]
    exact keyMoment2563 B hB
  · have he : k = (2564 : Fin 2886) := Fin.ext h2564
    subst k
    rw [keyMomentRowsAt2564]
    exact keyMoment2564 B hB
  · have he : k = (2565 : Fin 2886) := Fin.ext h2565
    subst k
    rw [keyMomentRowsAt2565]
    exact keyMoment2565 B hB
  · have he : k = (2566 : Fin 2886) := Fin.ext h2566
    subst k
    rw [keyMomentRowsAt2566]
    exact keyMoment2566 B hB
  · have he : k = (2567 : Fin 2886) := Fin.ext h2567
    subst k
    rw [keyMomentRowsAt2567]
    exact keyMoment2567 B hB
  · have he : k = (2568 : Fin 2886) := Fin.ext h2568
    subst k
    rw [keyMomentRowsAt2568]
    exact keyMoment2568 B hB
  · have he : k = (2569 : Fin 2886) := Fin.ext h2569
    subst k
    rw [keyMomentRowsAt2569]
    exact keyMoment2569 B hB
  · have he : k = (2570 : Fin 2886) := Fin.ext h2570
    subst k
    rw [keyMomentRowsAt2570]
    exact keyMoment2570 B hB
  · have he : k = (2571 : Fin 2886) := Fin.ext h2571
    subst k
    rw [keyMomentRowsAt2571]
    exact keyMoment2571 B hB
  · have he : k = (2572 : Fin 2886) := Fin.ext h2572
    subst k
    rw [keyMomentRowsAt2572]
    exact keyMoment2572 B hB
  · have he : k = (2573 : Fin 2886) := Fin.ext h2573
    subst k
    rw [keyMomentRowsAt2573]
    exact keyMoment2573 B hB
  · have he : k = (2574 : Fin 2886) := Fin.ext h2574
    subst k
    rw [keyMomentRowsAt2574]
    exact keyMoment2574 B hB
  · have he : k = (2575 : Fin 2886) := Fin.ext h2575
    subst k
    rw [keyMomentRowsAt2575]
    exact keyMoment2575 B hB
  · have he : k = (2576 : Fin 2886) := Fin.ext h2576
    subst k
    rw [keyMomentRowsAt2576]
    exact keyMoment2576 B hB
  · have he : k = (2577 : Fin 2886) := Fin.ext h2577
    subst k
    rw [keyMomentRowsAt2577]
    exact keyMoment2577 B hB
  · have he : k = (2578 : Fin 2886) := Fin.ext h2578
    subst k
    rw [keyMomentRowsAt2578]
    exact keyMoment2578 B hB
  · have he : k = (2579 : Fin 2886) := Fin.ext h2579
    subst k
    rw [keyMomentRowsAt2579]
    exact keyMoment2579 B hB
  · have he : k = (2580 : Fin 2886) := Fin.ext h2580
    subst k
    rw [keyMomentRowsAt2580]
    exact keyMoment2580 B hB
  · have he : k = (2581 : Fin 2886) := Fin.ext h2581
    subst k
    rw [keyMomentRowsAt2581]
    exact keyMoment2581 B hB
  · have he : k = (2582 : Fin 2886) := Fin.ext h2582
    subst k
    rw [keyMomentRowsAt2582]
    exact keyMoment2582 B hB
  · have he : k = (2583 : Fin 2886) := Fin.ext h2583
    subst k
    rw [keyMomentRowsAt2583]
    exact keyMoment2583 B hB
  · have he : k = (2584 : Fin 2886) := Fin.ext h2584
    subst k
    rw [keyMomentRowsAt2584]
    exact keyMoment2584 B hB
  · have he : k = (2585 : Fin 2886) := Fin.ext h2585
    subst k
    rw [keyMomentRowsAt2585]
    exact keyMoment2585 B hB
  · have he : k = (2586 : Fin 2886) := Fin.ext h2586
    subst k
    rw [keyMomentRowsAt2586]
    exact keyMoment2586 B hB
  · have he : k = (2587 : Fin 2886) := Fin.ext h2587
    subst k
    rw [keyMomentRowsAt2587]
    exact keyMoment2587 B hB
  · have he : k = (2588 : Fin 2886) := Fin.ext h2588
    subst k
    rw [keyMomentRowsAt2588]
    exact keyMoment2588 B hB
  · have he : k = (2589 : Fin 2886) := Fin.ext h2589
    subst k
    rw [keyMomentRowsAt2589]
    exact keyMoment2589 B hB
  · have he : k = (2590 : Fin 2886) := Fin.ext h2590
    subst k
    rw [keyMomentRowsAt2590]
    exact keyMoment2590 B hB
  · have he : k = (2591 : Fin 2886) := Fin.ext h2591
    subst k
    rw [keyMomentRowsAt2591]
    exact keyMoment2591 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
