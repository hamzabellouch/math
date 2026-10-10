import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound78
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2496 : keyMomentRows (2496 : Fin 2886) =
    keyMomentRow2496 := by decide +kernel

theorem keyMomentRowsAt2497 : keyMomentRows (2497 : Fin 2886) =
    keyMomentRow2497 := by decide +kernel

theorem keyMomentRowsAt2498 : keyMomentRows (2498 : Fin 2886) =
    keyMomentRow2498 := by decide +kernel

theorem keyMomentRowsAt2499 : keyMomentRows (2499 : Fin 2886) =
    keyMomentRow2499 := by decide +kernel

theorem keyMomentRowsAt2500 : keyMomentRows (2500 : Fin 2886) =
    keyMomentRow2500 := by decide +kernel

theorem keyMomentRowsAt2501 : keyMomentRows (2501 : Fin 2886) =
    keyMomentRow2501 := by decide +kernel

theorem keyMomentRowsAt2502 : keyMomentRows (2502 : Fin 2886) =
    keyMomentRow2502 := by decide +kernel

theorem keyMomentRowsAt2503 : keyMomentRows (2503 : Fin 2886) =
    keyMomentRow2503 := by decide +kernel

theorem keyMomentRowsAt2504 : keyMomentRows (2504 : Fin 2886) =
    keyMomentRow2504 := by decide +kernel

theorem keyMomentRowsAt2505 : keyMomentRows (2505 : Fin 2886) =
    keyMomentRow2505 := by decide +kernel

theorem keyMomentRowsAt2506 : keyMomentRows (2506 : Fin 2886) =
    keyMomentRow2506 := by decide +kernel

theorem keyMomentRowsAt2507 : keyMomentRows (2507 : Fin 2886) =
    keyMomentRow2507 := by decide +kernel

theorem keyMomentRowsAt2508 : keyMomentRows (2508 : Fin 2886) =
    keyMomentRow2508 := by decide +kernel

theorem keyMomentRowsAt2509 : keyMomentRows (2509 : Fin 2886) =
    keyMomentRow2509 := by decide +kernel

theorem keyMomentRowsAt2510 : keyMomentRows (2510 : Fin 2886) =
    keyMomentRow2510 := by decide +kernel

theorem keyMomentRowsAt2511 : keyMomentRows (2511 : Fin 2886) =
    keyMomentRow2511 := by decide +kernel

theorem keyMomentRowsAt2512 : keyMomentRows (2512 : Fin 2886) =
    keyMomentRow2512 := by decide +kernel

theorem keyMomentRowsAt2513 : keyMomentRows (2513 : Fin 2886) =
    keyMomentRow2513 := by decide +kernel

theorem keyMomentRowsAt2514 : keyMomentRows (2514 : Fin 2886) =
    keyMomentRow2514 := by decide +kernel

theorem keyMomentRowsAt2515 : keyMomentRows (2515 : Fin 2886) =
    keyMomentRow2515 := by decide +kernel

theorem keyMomentRowsAt2516 : keyMomentRows (2516 : Fin 2886) =
    keyMomentRow2516 := by decide +kernel

theorem keyMomentRowsAt2517 : keyMomentRows (2517 : Fin 2886) =
    keyMomentRow2517 := by decide +kernel

theorem keyMomentRowsAt2518 : keyMomentRows (2518 : Fin 2886) =
    keyMomentRow2518 := by decide +kernel

theorem keyMomentRowsAt2519 : keyMomentRows (2519 : Fin 2886) =
    keyMomentRow2519 := by decide +kernel

theorem keyMomentRowsAt2520 : keyMomentRows (2520 : Fin 2886) =
    keyMomentRow2520 := by decide +kernel

theorem keyMomentRowsAt2521 : keyMomentRows (2521 : Fin 2886) =
    keyMomentRow2521 := by decide +kernel

theorem keyMomentRowsAt2522 : keyMomentRows (2522 : Fin 2886) =
    keyMomentRow2522 := by decide +kernel

theorem keyMomentRowsAt2523 : keyMomentRows (2523 : Fin 2886) =
    keyMomentRow2523 := by decide +kernel

theorem keyMomentRowsAt2524 : keyMomentRows (2524 : Fin 2886) =
    keyMomentRow2524 := by decide +kernel

theorem keyMomentRowsAt2525 : keyMomentRows (2525 : Fin 2886) =
    keyMomentRow2525 := by decide +kernel

theorem keyMomentRowsAt2526 : keyMomentRows (2526 : Fin 2886) =
    keyMomentRow2526 := by decide +kernel

theorem keyMomentRowsAt2527 : keyMomentRows (2527 : Fin 2886) =
    keyMomentRow2527 := by decide +kernel

theorem keyMomentChunkSound78 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 78) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2496 ∨ k.val = 2497 ∨ k.val = 2498 ∨ k.val = 2499 ∨ k.val = 2500 ∨ k.val = 2501 ∨ k.val = 2502 ∨ k.val = 2503 ∨ k.val = 2504 ∨ k.val = 2505 ∨ k.val = 2506 ∨ k.val = 2507 ∨ k.val = 2508 ∨ k.val = 2509 ∨ k.val = 2510 ∨ k.val = 2511 ∨ k.val = 2512 ∨ k.val = 2513 ∨ k.val = 2514 ∨ k.val = 2515 ∨ k.val = 2516 ∨ k.val = 2517 ∨ k.val = 2518 ∨ k.val = 2519 ∨ k.val = 2520 ∨ k.val = 2521 ∨ k.val = 2522 ∨ k.val = 2523 ∨ k.val = 2524 ∨ k.val = 2525 ∨ k.val = 2526 ∨ k.val = 2527 := by omega
  rcases heq with h2496 | h2497 | h2498 | h2499 | h2500 | h2501 | h2502 | h2503 | h2504 | h2505 | h2506 | h2507 | h2508 | h2509 | h2510 | h2511 | h2512 | h2513 | h2514 | h2515 | h2516 | h2517 | h2518 | h2519 | h2520 | h2521 | h2522 | h2523 | h2524 | h2525 | h2526 | h2527
  · have he : k = (2496 : Fin 2886) := Fin.ext h2496
    subst k
    rw [keyMomentRowsAt2496]
    exact keyMoment2496 B hB
  · have he : k = (2497 : Fin 2886) := Fin.ext h2497
    subst k
    rw [keyMomentRowsAt2497]
    exact keyMoment2497 B hB
  · have he : k = (2498 : Fin 2886) := Fin.ext h2498
    subst k
    rw [keyMomentRowsAt2498]
    exact keyMoment2498 B hB
  · have he : k = (2499 : Fin 2886) := Fin.ext h2499
    subst k
    rw [keyMomentRowsAt2499]
    exact keyMoment2499 B hB
  · have he : k = (2500 : Fin 2886) := Fin.ext h2500
    subst k
    rw [keyMomentRowsAt2500]
    exact keyMoment2500 B hB
  · have he : k = (2501 : Fin 2886) := Fin.ext h2501
    subst k
    rw [keyMomentRowsAt2501]
    exact keyMoment2501 B hB
  · have he : k = (2502 : Fin 2886) := Fin.ext h2502
    subst k
    rw [keyMomentRowsAt2502]
    exact keyMoment2502 B hB
  · have he : k = (2503 : Fin 2886) := Fin.ext h2503
    subst k
    rw [keyMomentRowsAt2503]
    exact keyMoment2503 B hB
  · have he : k = (2504 : Fin 2886) := Fin.ext h2504
    subst k
    rw [keyMomentRowsAt2504]
    exact keyMoment2504 B hB
  · have he : k = (2505 : Fin 2886) := Fin.ext h2505
    subst k
    rw [keyMomentRowsAt2505]
    exact keyMoment2505 B hB
  · have he : k = (2506 : Fin 2886) := Fin.ext h2506
    subst k
    rw [keyMomentRowsAt2506]
    exact keyMoment2506 B hB
  · have he : k = (2507 : Fin 2886) := Fin.ext h2507
    subst k
    rw [keyMomentRowsAt2507]
    exact keyMoment2507 B hB
  · have he : k = (2508 : Fin 2886) := Fin.ext h2508
    subst k
    rw [keyMomentRowsAt2508]
    exact keyMoment2508 B hB
  · have he : k = (2509 : Fin 2886) := Fin.ext h2509
    subst k
    rw [keyMomentRowsAt2509]
    exact keyMoment2509 B hB
  · have he : k = (2510 : Fin 2886) := Fin.ext h2510
    subst k
    rw [keyMomentRowsAt2510]
    exact keyMoment2510 B hB
  · have he : k = (2511 : Fin 2886) := Fin.ext h2511
    subst k
    rw [keyMomentRowsAt2511]
    exact keyMoment2511 B hB
  · have he : k = (2512 : Fin 2886) := Fin.ext h2512
    subst k
    rw [keyMomentRowsAt2512]
    exact keyMoment2512 B hB
  · have he : k = (2513 : Fin 2886) := Fin.ext h2513
    subst k
    rw [keyMomentRowsAt2513]
    exact keyMoment2513 B hB
  · have he : k = (2514 : Fin 2886) := Fin.ext h2514
    subst k
    rw [keyMomentRowsAt2514]
    exact keyMoment2514 B hB
  · have he : k = (2515 : Fin 2886) := Fin.ext h2515
    subst k
    rw [keyMomentRowsAt2515]
    exact keyMoment2515 B hB
  · have he : k = (2516 : Fin 2886) := Fin.ext h2516
    subst k
    rw [keyMomentRowsAt2516]
    exact keyMoment2516 B hB
  · have he : k = (2517 : Fin 2886) := Fin.ext h2517
    subst k
    rw [keyMomentRowsAt2517]
    exact keyMoment2517 B hB
  · have he : k = (2518 : Fin 2886) := Fin.ext h2518
    subst k
    rw [keyMomentRowsAt2518]
    exact keyMoment2518 B hB
  · have he : k = (2519 : Fin 2886) := Fin.ext h2519
    subst k
    rw [keyMomentRowsAt2519]
    exact keyMoment2519 B hB
  · have he : k = (2520 : Fin 2886) := Fin.ext h2520
    subst k
    rw [keyMomentRowsAt2520]
    exact keyMoment2520 B hB
  · have he : k = (2521 : Fin 2886) := Fin.ext h2521
    subst k
    rw [keyMomentRowsAt2521]
    exact keyMoment2521 B hB
  · have he : k = (2522 : Fin 2886) := Fin.ext h2522
    subst k
    rw [keyMomentRowsAt2522]
    exact keyMoment2522 B hB
  · have he : k = (2523 : Fin 2886) := Fin.ext h2523
    subst k
    rw [keyMomentRowsAt2523]
    exact keyMoment2523 B hB
  · have he : k = (2524 : Fin 2886) := Fin.ext h2524
    subst k
    rw [keyMomentRowsAt2524]
    exact keyMoment2524 B hB
  · have he : k = (2525 : Fin 2886) := Fin.ext h2525
    subst k
    rw [keyMomentRowsAt2525]
    exact keyMoment2525 B hB
  · have he : k = (2526 : Fin 2886) := Fin.ext h2526
    subst k
    rw [keyMomentRowsAt2526]
    exact keyMoment2526 B hB
  · have he : k = (2527 : Fin 2886) := Fin.ext h2527
    subst k
    rw [keyMomentRowsAt2527]
    exact keyMoment2527 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
