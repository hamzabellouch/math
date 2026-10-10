import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound76
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2432 : keyMomentRows (2432 : Fin 2886) =
    keyMomentRow2432 := by decide +kernel

theorem keyMomentRowsAt2433 : keyMomentRows (2433 : Fin 2886) =
    keyMomentRow2433 := by decide +kernel

theorem keyMomentRowsAt2434 : keyMomentRows (2434 : Fin 2886) =
    keyMomentRow2434 := by decide +kernel

theorem keyMomentRowsAt2435 : keyMomentRows (2435 : Fin 2886) =
    keyMomentRow2435 := by decide +kernel

theorem keyMomentRowsAt2436 : keyMomentRows (2436 : Fin 2886) =
    keyMomentRow2436 := by decide +kernel

theorem keyMomentRowsAt2437 : keyMomentRows (2437 : Fin 2886) =
    keyMomentRow2437 := by decide +kernel

theorem keyMomentRowsAt2438 : keyMomentRows (2438 : Fin 2886) =
    keyMomentRow2438 := by decide +kernel

theorem keyMomentRowsAt2439 : keyMomentRows (2439 : Fin 2886) =
    keyMomentRow2439 := by decide +kernel

theorem keyMomentRowsAt2440 : keyMomentRows (2440 : Fin 2886) =
    keyMomentRow2440 := by decide +kernel

theorem keyMomentRowsAt2441 : keyMomentRows (2441 : Fin 2886) =
    keyMomentRow2441 := by decide +kernel

theorem keyMomentRowsAt2442 : keyMomentRows (2442 : Fin 2886) =
    keyMomentRow2442 := by decide +kernel

theorem keyMomentRowsAt2443 : keyMomentRows (2443 : Fin 2886) =
    keyMomentRow2443 := by decide +kernel

theorem keyMomentRowsAt2444 : keyMomentRows (2444 : Fin 2886) =
    keyMomentRow2444 := by decide +kernel

theorem keyMomentRowsAt2445 : keyMomentRows (2445 : Fin 2886) =
    keyMomentRow2445 := by decide +kernel

theorem keyMomentRowsAt2446 : keyMomentRows (2446 : Fin 2886) =
    keyMomentRow2446 := by decide +kernel

theorem keyMomentRowsAt2447 : keyMomentRows (2447 : Fin 2886) =
    keyMomentRow2447 := by decide +kernel

theorem keyMomentRowsAt2448 : keyMomentRows (2448 : Fin 2886) =
    keyMomentRow2448 := by decide +kernel

theorem keyMomentRowsAt2449 : keyMomentRows (2449 : Fin 2886) =
    keyMomentRow2449 := by decide +kernel

theorem keyMomentRowsAt2450 : keyMomentRows (2450 : Fin 2886) =
    keyMomentRow2450 := by decide +kernel

theorem keyMomentRowsAt2451 : keyMomentRows (2451 : Fin 2886) =
    keyMomentRow2451 := by decide +kernel

theorem keyMomentRowsAt2452 : keyMomentRows (2452 : Fin 2886) =
    keyMomentRow2452 := by decide +kernel

theorem keyMomentRowsAt2453 : keyMomentRows (2453 : Fin 2886) =
    keyMomentRow2453 := by decide +kernel

theorem keyMomentRowsAt2454 : keyMomentRows (2454 : Fin 2886) =
    keyMomentRow2454 := by decide +kernel

theorem keyMomentRowsAt2455 : keyMomentRows (2455 : Fin 2886) =
    keyMomentRow2455 := by decide +kernel

theorem keyMomentRowsAt2456 : keyMomentRows (2456 : Fin 2886) =
    keyMomentRow2456 := by decide +kernel

theorem keyMomentRowsAt2457 : keyMomentRows (2457 : Fin 2886) =
    keyMomentRow2457 := by decide +kernel

theorem keyMomentRowsAt2458 : keyMomentRows (2458 : Fin 2886) =
    keyMomentRow2458 := by decide +kernel

theorem keyMomentRowsAt2459 : keyMomentRows (2459 : Fin 2886) =
    keyMomentRow2459 := by decide +kernel

theorem keyMomentRowsAt2460 : keyMomentRows (2460 : Fin 2886) =
    keyMomentRow2460 := by decide +kernel

theorem keyMomentRowsAt2461 : keyMomentRows (2461 : Fin 2886) =
    keyMomentRow2461 := by decide +kernel

theorem keyMomentRowsAt2462 : keyMomentRows (2462 : Fin 2886) =
    keyMomentRow2462 := by decide +kernel

theorem keyMomentRowsAt2463 : keyMomentRows (2463 : Fin 2886) =
    keyMomentRow2463 := by decide +kernel

theorem keyMomentChunkSound76 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 76) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2432 ∨ k.val = 2433 ∨ k.val = 2434 ∨ k.val = 2435 ∨ k.val = 2436 ∨ k.val = 2437 ∨ k.val = 2438 ∨ k.val = 2439 ∨ k.val = 2440 ∨ k.val = 2441 ∨ k.val = 2442 ∨ k.val = 2443 ∨ k.val = 2444 ∨ k.val = 2445 ∨ k.val = 2446 ∨ k.val = 2447 ∨ k.val = 2448 ∨ k.val = 2449 ∨ k.val = 2450 ∨ k.val = 2451 ∨ k.val = 2452 ∨ k.val = 2453 ∨ k.val = 2454 ∨ k.val = 2455 ∨ k.val = 2456 ∨ k.val = 2457 ∨ k.val = 2458 ∨ k.val = 2459 ∨ k.val = 2460 ∨ k.val = 2461 ∨ k.val = 2462 ∨ k.val = 2463 := by omega
  rcases heq with h2432 | h2433 | h2434 | h2435 | h2436 | h2437 | h2438 | h2439 | h2440 | h2441 | h2442 | h2443 | h2444 | h2445 | h2446 | h2447 | h2448 | h2449 | h2450 | h2451 | h2452 | h2453 | h2454 | h2455 | h2456 | h2457 | h2458 | h2459 | h2460 | h2461 | h2462 | h2463
  · have he : k = (2432 : Fin 2886) := Fin.ext h2432
    subst k
    rw [keyMomentRowsAt2432]
    exact keyMoment2432 B hB
  · have he : k = (2433 : Fin 2886) := Fin.ext h2433
    subst k
    rw [keyMomentRowsAt2433]
    exact keyMoment2433 B hB
  · have he : k = (2434 : Fin 2886) := Fin.ext h2434
    subst k
    rw [keyMomentRowsAt2434]
    exact keyMoment2434 B hB
  · have he : k = (2435 : Fin 2886) := Fin.ext h2435
    subst k
    rw [keyMomentRowsAt2435]
    exact keyMoment2435 B hB
  · have he : k = (2436 : Fin 2886) := Fin.ext h2436
    subst k
    rw [keyMomentRowsAt2436]
    exact keyMoment2436 B hB
  · have he : k = (2437 : Fin 2886) := Fin.ext h2437
    subst k
    rw [keyMomentRowsAt2437]
    exact keyMoment2437 B hB
  · have he : k = (2438 : Fin 2886) := Fin.ext h2438
    subst k
    rw [keyMomentRowsAt2438]
    exact keyMoment2438 B hB
  · have he : k = (2439 : Fin 2886) := Fin.ext h2439
    subst k
    rw [keyMomentRowsAt2439]
    exact keyMoment2439 B hB
  · have he : k = (2440 : Fin 2886) := Fin.ext h2440
    subst k
    rw [keyMomentRowsAt2440]
    exact keyMoment2440 B hB
  · have he : k = (2441 : Fin 2886) := Fin.ext h2441
    subst k
    rw [keyMomentRowsAt2441]
    exact keyMoment2441 B hB
  · have he : k = (2442 : Fin 2886) := Fin.ext h2442
    subst k
    rw [keyMomentRowsAt2442]
    exact keyMoment2442 B hB
  · have he : k = (2443 : Fin 2886) := Fin.ext h2443
    subst k
    rw [keyMomentRowsAt2443]
    exact keyMoment2443 B hB
  · have he : k = (2444 : Fin 2886) := Fin.ext h2444
    subst k
    rw [keyMomentRowsAt2444]
    exact keyMoment2444 B hB
  · have he : k = (2445 : Fin 2886) := Fin.ext h2445
    subst k
    rw [keyMomentRowsAt2445]
    exact keyMoment2445 B hB
  · have he : k = (2446 : Fin 2886) := Fin.ext h2446
    subst k
    rw [keyMomentRowsAt2446]
    exact keyMoment2446 B hB
  · have he : k = (2447 : Fin 2886) := Fin.ext h2447
    subst k
    rw [keyMomentRowsAt2447]
    exact keyMoment2447 B hB
  · have he : k = (2448 : Fin 2886) := Fin.ext h2448
    subst k
    rw [keyMomentRowsAt2448]
    exact keyMoment2448 B hB
  · have he : k = (2449 : Fin 2886) := Fin.ext h2449
    subst k
    rw [keyMomentRowsAt2449]
    exact keyMoment2449 B hB
  · have he : k = (2450 : Fin 2886) := Fin.ext h2450
    subst k
    rw [keyMomentRowsAt2450]
    exact keyMoment2450 B hB
  · have he : k = (2451 : Fin 2886) := Fin.ext h2451
    subst k
    rw [keyMomentRowsAt2451]
    exact keyMoment2451 B hB
  · have he : k = (2452 : Fin 2886) := Fin.ext h2452
    subst k
    rw [keyMomentRowsAt2452]
    exact keyMoment2452 B hB
  · have he : k = (2453 : Fin 2886) := Fin.ext h2453
    subst k
    rw [keyMomentRowsAt2453]
    exact keyMoment2453 B hB
  · have he : k = (2454 : Fin 2886) := Fin.ext h2454
    subst k
    rw [keyMomentRowsAt2454]
    exact keyMoment2454 B hB
  · have he : k = (2455 : Fin 2886) := Fin.ext h2455
    subst k
    rw [keyMomentRowsAt2455]
    exact keyMoment2455 B hB
  · have he : k = (2456 : Fin 2886) := Fin.ext h2456
    subst k
    rw [keyMomentRowsAt2456]
    exact keyMoment2456 B hB
  · have he : k = (2457 : Fin 2886) := Fin.ext h2457
    subst k
    rw [keyMomentRowsAt2457]
    exact keyMoment2457 B hB
  · have he : k = (2458 : Fin 2886) := Fin.ext h2458
    subst k
    rw [keyMomentRowsAt2458]
    exact keyMoment2458 B hB
  · have he : k = (2459 : Fin 2886) := Fin.ext h2459
    subst k
    rw [keyMomentRowsAt2459]
    exact keyMoment2459 B hB
  · have he : k = (2460 : Fin 2886) := Fin.ext h2460
    subst k
    rw [keyMomentRowsAt2460]
    exact keyMoment2460 B hB
  · have he : k = (2461 : Fin 2886) := Fin.ext h2461
    subst k
    rw [keyMomentRowsAt2461]
    exact keyMoment2461 B hB
  · have he : k = (2462 : Fin 2886) := Fin.ext h2462
    subst k
    rw [keyMomentRowsAt2462]
    exact keyMoment2462 B hB
  · have he : k = (2463 : Fin 2886) := Fin.ext h2463
    subst k
    rw [keyMomentRowsAt2463]
    exact keyMoment2463 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
