import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound17
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt544 : keyMomentRows (544 : Fin 2886) =
    keyMomentRow544 := by decide +kernel

theorem keyMomentRowsAt545 : keyMomentRows (545 : Fin 2886) =
    keyMomentRow545 := by decide +kernel

theorem keyMomentRowsAt546 : keyMomentRows (546 : Fin 2886) =
    keyMomentRow546 := by decide +kernel

theorem keyMomentRowsAt547 : keyMomentRows (547 : Fin 2886) =
    keyMomentRow547 := by decide +kernel

theorem keyMomentRowsAt548 : keyMomentRows (548 : Fin 2886) =
    keyMomentRow548 := by decide +kernel

theorem keyMomentRowsAt549 : keyMomentRows (549 : Fin 2886) =
    keyMomentRow549 := by decide +kernel

theorem keyMomentRowsAt550 : keyMomentRows (550 : Fin 2886) =
    keyMomentRow550 := by decide +kernel

theorem keyMomentRowsAt551 : keyMomentRows (551 : Fin 2886) =
    keyMomentRow551 := by decide +kernel

theorem keyMomentRowsAt552 : keyMomentRows (552 : Fin 2886) =
    keyMomentRow552 := by decide +kernel

theorem keyMomentRowsAt553 : keyMomentRows (553 : Fin 2886) =
    keyMomentRow553 := by decide +kernel

theorem keyMomentRowsAt554 : keyMomentRows (554 : Fin 2886) =
    keyMomentRow554 := by decide +kernel

theorem keyMomentRowsAt555 : keyMomentRows (555 : Fin 2886) =
    keyMomentRow555 := by decide +kernel

theorem keyMomentRowsAt556 : keyMomentRows (556 : Fin 2886) =
    keyMomentRow556 := by decide +kernel

theorem keyMomentRowsAt557 : keyMomentRows (557 : Fin 2886) =
    keyMomentRow557 := by decide +kernel

theorem keyMomentRowsAt558 : keyMomentRows (558 : Fin 2886) =
    keyMomentRow558 := by decide +kernel

theorem keyMomentRowsAt559 : keyMomentRows (559 : Fin 2886) =
    keyMomentRow559 := by decide +kernel

theorem keyMomentRowsAt560 : keyMomentRows (560 : Fin 2886) =
    keyMomentRow560 := by decide +kernel

theorem keyMomentRowsAt561 : keyMomentRows (561 : Fin 2886) =
    keyMomentRow561 := by decide +kernel

theorem keyMomentRowsAt562 : keyMomentRows (562 : Fin 2886) =
    keyMomentRow562 := by decide +kernel

theorem keyMomentRowsAt563 : keyMomentRows (563 : Fin 2886) =
    keyMomentRow563 := by decide +kernel

theorem keyMomentRowsAt564 : keyMomentRows (564 : Fin 2886) =
    keyMomentRow564 := by decide +kernel

theorem keyMomentRowsAt565 : keyMomentRows (565 : Fin 2886) =
    keyMomentRow565 := by decide +kernel

theorem keyMomentRowsAt566 : keyMomentRows (566 : Fin 2886) =
    keyMomentRow566 := by decide +kernel

theorem keyMomentRowsAt567 : keyMomentRows (567 : Fin 2886) =
    keyMomentRow567 := by decide +kernel

theorem keyMomentRowsAt568 : keyMomentRows (568 : Fin 2886) =
    keyMomentRow568 := by decide +kernel

theorem keyMomentRowsAt569 : keyMomentRows (569 : Fin 2886) =
    keyMomentRow569 := by decide +kernel

theorem keyMomentRowsAt570 : keyMomentRows (570 : Fin 2886) =
    keyMomentRow570 := by decide +kernel

theorem keyMomentRowsAt571 : keyMomentRows (571 : Fin 2886) =
    keyMomentRow571 := by decide +kernel

theorem keyMomentRowsAt572 : keyMomentRows (572 : Fin 2886) =
    keyMomentRow572 := by decide +kernel

theorem keyMomentRowsAt573 : keyMomentRows (573 : Fin 2886) =
    keyMomentRow573 := by decide +kernel

theorem keyMomentRowsAt574 : keyMomentRows (574 : Fin 2886) =
    keyMomentRow574 := by decide +kernel

theorem keyMomentRowsAt575 : keyMomentRows (575 : Fin 2886) =
    keyMomentRow575 := by decide +kernel

theorem keyMomentChunkSound17 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 17) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 544 ∨ k.val = 545 ∨ k.val = 546 ∨ k.val = 547 ∨ k.val = 548 ∨ k.val = 549 ∨ k.val = 550 ∨ k.val = 551 ∨ k.val = 552 ∨ k.val = 553 ∨ k.val = 554 ∨ k.val = 555 ∨ k.val = 556 ∨ k.val = 557 ∨ k.val = 558 ∨ k.val = 559 ∨ k.val = 560 ∨ k.val = 561 ∨ k.val = 562 ∨ k.val = 563 ∨ k.val = 564 ∨ k.val = 565 ∨ k.val = 566 ∨ k.val = 567 ∨ k.val = 568 ∨ k.val = 569 ∨ k.val = 570 ∨ k.val = 571 ∨ k.val = 572 ∨ k.val = 573 ∨ k.val = 574 ∨ k.val = 575 := by omega
  rcases heq with h544 | h545 | h546 | h547 | h548 | h549 | h550 | h551 | h552 | h553 | h554 | h555 | h556 | h557 | h558 | h559 | h560 | h561 | h562 | h563 | h564 | h565 | h566 | h567 | h568 | h569 | h570 | h571 | h572 | h573 | h574 | h575
  · have he : k = (544 : Fin 2886) := Fin.ext h544
    subst k
    rw [keyMomentRowsAt544]
    exact keyMoment544 B hB
  · have he : k = (545 : Fin 2886) := Fin.ext h545
    subst k
    rw [keyMomentRowsAt545]
    exact keyMoment545 B hB
  · have he : k = (546 : Fin 2886) := Fin.ext h546
    subst k
    rw [keyMomentRowsAt546]
    exact keyMoment546 B hB
  · have he : k = (547 : Fin 2886) := Fin.ext h547
    subst k
    rw [keyMomentRowsAt547]
    exact keyMoment547 B hB
  · have he : k = (548 : Fin 2886) := Fin.ext h548
    subst k
    rw [keyMomentRowsAt548]
    exact keyMoment548 B hB
  · have he : k = (549 : Fin 2886) := Fin.ext h549
    subst k
    rw [keyMomentRowsAt549]
    exact keyMoment549 B hB
  · have he : k = (550 : Fin 2886) := Fin.ext h550
    subst k
    rw [keyMomentRowsAt550]
    exact keyMoment550 B hB
  · have he : k = (551 : Fin 2886) := Fin.ext h551
    subst k
    rw [keyMomentRowsAt551]
    exact keyMoment551 B hB
  · have he : k = (552 : Fin 2886) := Fin.ext h552
    subst k
    rw [keyMomentRowsAt552]
    exact keyMoment552 B hB
  · have he : k = (553 : Fin 2886) := Fin.ext h553
    subst k
    rw [keyMomentRowsAt553]
    exact keyMoment553 B hB
  · have he : k = (554 : Fin 2886) := Fin.ext h554
    subst k
    rw [keyMomentRowsAt554]
    exact keyMoment554 B hB
  · have he : k = (555 : Fin 2886) := Fin.ext h555
    subst k
    rw [keyMomentRowsAt555]
    exact keyMoment555 B hB
  · have he : k = (556 : Fin 2886) := Fin.ext h556
    subst k
    rw [keyMomentRowsAt556]
    exact keyMoment556 B hB
  · have he : k = (557 : Fin 2886) := Fin.ext h557
    subst k
    rw [keyMomentRowsAt557]
    exact keyMoment557 B hB
  · have he : k = (558 : Fin 2886) := Fin.ext h558
    subst k
    rw [keyMomentRowsAt558]
    exact keyMoment558 B hB
  · have he : k = (559 : Fin 2886) := Fin.ext h559
    subst k
    rw [keyMomentRowsAt559]
    exact keyMoment559 B hB
  · have he : k = (560 : Fin 2886) := Fin.ext h560
    subst k
    rw [keyMomentRowsAt560]
    exact keyMoment560 B hB
  · have he : k = (561 : Fin 2886) := Fin.ext h561
    subst k
    rw [keyMomentRowsAt561]
    exact keyMoment561 B hB
  · have he : k = (562 : Fin 2886) := Fin.ext h562
    subst k
    rw [keyMomentRowsAt562]
    exact keyMoment562 B hB
  · have he : k = (563 : Fin 2886) := Fin.ext h563
    subst k
    rw [keyMomentRowsAt563]
    exact keyMoment563 B hB
  · have he : k = (564 : Fin 2886) := Fin.ext h564
    subst k
    rw [keyMomentRowsAt564]
    exact keyMoment564 B hB
  · have he : k = (565 : Fin 2886) := Fin.ext h565
    subst k
    rw [keyMomentRowsAt565]
    exact keyMoment565 B hB
  · have he : k = (566 : Fin 2886) := Fin.ext h566
    subst k
    rw [keyMomentRowsAt566]
    exact keyMoment566 B hB
  · have he : k = (567 : Fin 2886) := Fin.ext h567
    subst k
    rw [keyMomentRowsAt567]
    exact keyMoment567 B hB
  · have he : k = (568 : Fin 2886) := Fin.ext h568
    subst k
    rw [keyMomentRowsAt568]
    exact keyMoment568 B hB
  · have he : k = (569 : Fin 2886) := Fin.ext h569
    subst k
    rw [keyMomentRowsAt569]
    exact keyMoment569 B hB
  · have he : k = (570 : Fin 2886) := Fin.ext h570
    subst k
    rw [keyMomentRowsAt570]
    exact keyMoment570 B hB
  · have he : k = (571 : Fin 2886) := Fin.ext h571
    subst k
    rw [keyMomentRowsAt571]
    exact keyMoment571 B hB
  · have he : k = (572 : Fin 2886) := Fin.ext h572
    subst k
    rw [keyMomentRowsAt572]
    exact keyMoment572 B hB
  · have he : k = (573 : Fin 2886) := Fin.ext h573
    subst k
    rw [keyMomentRowsAt573]
    exact keyMoment573 B hB
  · have he : k = (574 : Fin 2886) := Fin.ext h574
    subst k
    rw [keyMomentRowsAt574]
    exact keyMoment574 B hB
  · have he : k = (575 : Fin 2886) := Fin.ext h575
    subst k
    rw [keyMomentRowsAt575]
    exact keyMoment575 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
