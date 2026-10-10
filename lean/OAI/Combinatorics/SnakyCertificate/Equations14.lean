import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_560 : fork [place ⟨517, 5, 5, 4⟩ cache_517, place ⟨416, 5, 4, 3⟩ cache_416, place ⟨359, 5, 3, 4⟩ cache_359, place ⟨356, 6, 3, 4⟩ cache_356, place ⟨483, 0, 4, 6⟩ cache_483] = cache_560 := by
  decide +kernel

theorem load_entry_560 : entryAt 560 = entry_560 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_560 : CacheEquation 560 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(560 < 6)), load_entry_560]
  change forkRow [placeRow ⟨517, 5, 5, 4⟩ (denote cache_517), placeRow ⟨416, 5, 4, 3⟩ (denote cache_416), placeRow ⟨359, 5, 3, 4⟩ (denote cache_359), placeRow ⟨356, 6, 3, 4⟩ (denote cache_356), placeRow ⟨483, 0, 4, 6⟩ (denote cache_483)] = denote cache_560
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_560

theorem verified_row_561 : fork [place ⟨295, 0, 5, 4⟩ cache_295, place ⟨173, 2, 5, 4⟩ cache_173, place ⟨263, 6, 1, 4⟩ cache_263, place ⟨236, 1, 5, 5⟩ cache_236, place ⟨546, 4, 5, 4⟩ cache_546, place ⟨176, 2, 5, 4⟩ cache_176, place ⟨535, 0, 4, 5⟩ cache_535] = cache_561 := by
  decide +kernel

theorem load_entry_561 : entryAt 561 = entry_561 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_561 : CacheEquation 561 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(561 < 6)), load_entry_561]
  change forkRow [placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨173, 2, 5, 4⟩ (denote cache_173), placeRow ⟨263, 6, 1, 4⟩ (denote cache_263), placeRow ⟨236, 1, 5, 5⟩ (denote cache_236), placeRow ⟨546, 4, 5, 4⟩ (denote cache_546), placeRow ⟨176, 2, 5, 4⟩ (denote cache_176), placeRow ⟨535, 0, 4, 5⟩ (denote cache_535)] = denote cache_561
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_561

theorem verified_row_562 : fork [place ⟨6, 7, 3, 0⟩ cache_6, place ⟨559, 0, 4, 5⟩ cache_559] = cache_562 := by
  decide +kernel

theorem load_entry_562 : entryAt 562 = entry_562 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_562 : CacheEquation 562 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(562 < 6)), load_entry_562]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (denote cache_6), placeRow ⟨559, 0, 4, 5⟩ (denote cache_559)] = denote cache_562
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_562

theorem verified_row_563 : fork [place ⟨167, 0, 7, 4⟩ cache_167, place ⟨538, 0, 3, 4⟩ cache_538, place ⟨514, 0, 7, 4⟩ cache_514, place ⟨330, 4, 3, 4⟩ cache_330, place ⟨545, 0, 5, 5⟩ cache_545] = cache_563 := by
  decide +kernel

theorem load_entry_563 : entryAt 563 = entry_563 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_563 : CacheEquation 563 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(563 < 6)), load_entry_563]
  change forkRow [placeRow ⟨167, 0, 7, 4⟩ (denote cache_167), placeRow ⟨538, 0, 3, 4⟩ (denote cache_538), placeRow ⟨514, 0, 7, 4⟩ (denote cache_514), placeRow ⟨330, 4, 3, 4⟩ (denote cache_330), placeRow ⟨545, 0, 5, 5⟩ (denote cache_545)] = denote cache_563
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_563

theorem verified_row_564 : fork [place ⟨560, 0, 4, 3⟩ cache_560, place ⟨421, 0, 3, 4⟩ cache_421, place ⟨401, 1, 3, 4⟩ cache_401, place ⟨340, 3, 3, 4⟩ cache_340, place ⟨509, 0, 3, 4⟩ cache_509, place ⟨528, 0, 4, 3⟩ cache_528, place ⟨423, 5, 4, 3⟩ cache_423, place ⟨425, 5, 4, 3⟩ cache_425, place ⟨336, 0, 3, 4⟩ cache_336] = cache_564 := by
  decide +kernel

theorem load_entry_564 : entryAt 564 = entry_564 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_564 : CacheEquation 564 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(564 < 6)), load_entry_564]
  change forkRow [placeRow ⟨560, 0, 4, 3⟩ (denote cache_560), placeRow ⟨421, 0, 3, 4⟩ (denote cache_421), placeRow ⟨401, 1, 3, 4⟩ (denote cache_401), placeRow ⟨340, 3, 3, 4⟩ (denote cache_340), placeRow ⟨509, 0, 3, 4⟩ (denote cache_509), placeRow ⟨528, 0, 4, 3⟩ (denote cache_528), placeRow ⟨423, 5, 4, 3⟩ (denote cache_423), placeRow ⟨425, 5, 4, 3⟩ (denote cache_425), placeRow ⟨336, 0, 3, 4⟩ (denote cache_336)] = denote cache_564
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_564

theorem verified_row_565 : fork [place ⟨443, 4, 4, 5⟩ cache_443, place ⟨131, 3, 3, 4⟩ cache_131, place ⟨538, 0, 3, 4⟩ cache_538, place ⟨459, 0, 5, 5⟩ cache_459, place ⟨144, 4, 3, 4⟩ cache_144] = cache_565 := by
  decide +kernel

theorem load_entry_565 : entryAt 565 = entry_565 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_565 : CacheEquation 565 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(565 < 6)), load_entry_565]
  change forkRow [placeRow ⟨443, 4, 4, 5⟩ (denote cache_443), placeRow ⟨131, 3, 3, 4⟩ (denote cache_131), placeRow ⟨538, 0, 3, 4⟩ (denote cache_538), placeRow ⟨459, 0, 5, 5⟩ (denote cache_459), placeRow ⟨144, 4, 3, 4⟩ (denote cache_144)] = denote cache_565
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_565

theorem verified_row_566 : fork [place ⟨314, 0, 3, 4⟩ cache_314, place ⟨180, 0, 4, 5⟩ cache_180, place ⟨442, 0, 4, 5⟩ cache_442, place ⟨466, 0, 6, 3⟩ cache_466, place ⟨504, 0, 3, 3⟩ cache_504] = cache_566 := by
  decide +kernel

theorem load_entry_566 : entryAt 566 = entry_566 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_566 : CacheEquation 566 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(566 < 6)), load_entry_566]
  change forkRow [placeRow ⟨314, 0, 3, 4⟩ (denote cache_314), placeRow ⟨180, 0, 4, 5⟩ (denote cache_180), placeRow ⟨442, 0, 4, 5⟩ (denote cache_442), placeRow ⟨466, 0, 6, 3⟩ (denote cache_466), placeRow ⟨504, 0, 3, 3⟩ (denote cache_504)] = denote cache_566
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_566

theorem verified_row_567 : fork [place ⟨21, 1, 4, 3⟩ cache_21, place ⟨561, 0, 6, 4⟩ cache_561, place ⟨500, 4, 3, 1⟩ cache_500] = cache_567 := by
  decide +kernel

theorem load_entry_567 : entryAt 567 = entry_567 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_567 : CacheEquation 567 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(567 < 6)), load_entry_567]
  change forkRow [placeRow ⟨21, 1, 4, 3⟩ (denote cache_21), placeRow ⟨561, 0, 6, 4⟩ (denote cache_561), placeRow ⟨500, 4, 3, 1⟩ (denote cache_500)] = denote cache_567
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_567

theorem verified_row_568 : fork [place ⟨538, 4, 6, 4⟩ cache_538, place ⟨547, 0, 2, 4⟩ cache_547, place ⟨275, 0, 6, 4⟩ cache_275, place ⟨565, 0, 2, 4⟩ cache_565, place ⟨330, 0, 6, 4⟩ cache_330] = cache_568 := by
  decide +kernel

theorem load_entry_568 : entryAt 568 = entry_568 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_568 : CacheEquation 568 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(568 < 6)), load_entry_568]
  change forkRow [placeRow ⟨538, 4, 6, 4⟩ (denote cache_538), placeRow ⟨547, 0, 2, 4⟩ (denote cache_547), placeRow ⟨275, 0, 6, 4⟩ (denote cache_275), placeRow ⟨565, 0, 2, 4⟩ (denote cache_565), placeRow ⟨330, 0, 6, 4⟩ (denote cache_330)] = denote cache_568
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_568

theorem verified_row_569 : fork [place ⟨34, 3, 4, 2⟩ cache_34, place ⟨568, 4, 5, 4⟩ cache_568] = cache_569 := by
  decide +kernel

theorem load_entry_569 : entryAt 569 = entry_569 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_569 : CacheEquation 569 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(569 < 6)), load_entry_569]
  change forkRow [placeRow ⟨34, 3, 4, 2⟩ (denote cache_34), placeRow ⟨568, 4, 5, 4⟩ (denote cache_568)] = denote cache_569
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_569

theorem verified_row_570 : fork [place ⟨569, 0, 2, 5⟩ cache_569, place ⟨2, 7, 4, 3⟩ cache_2] = cache_570 := by
  decide +kernel

theorem load_entry_570 : entryAt 570 = entry_570 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_570 : CacheEquation 570 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(570 < 6)), load_entry_570]
  change forkRow [placeRow ⟨569, 0, 2, 5⟩ (denote cache_569), placeRow ⟨2, 7, 4, 3⟩ (denote cache_2)] = denote cache_570
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_570

theorem verified_row_571 : fork [place ⟨293, 0, 4, 3⟩ cache_293, place ⟨570, 0, 4, 3⟩ cache_570, place ⟨382, 0, 4, 3⟩ cache_382, place ⟨556, 4, 2, 4⟩ cache_556] = cache_571 := by
  decide +kernel

theorem load_entry_571 : entryAt 571 = entry_571 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_571 : CacheEquation 571 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(571 < 6)), load_entry_571]
  change forkRow [placeRow ⟨293, 0, 4, 3⟩ (denote cache_293), placeRow ⟨570, 0, 4, 3⟩ (denote cache_570), placeRow ⟨382, 0, 4, 3⟩ (denote cache_382), placeRow ⟨556, 4, 2, 4⟩ (denote cache_556)] = denote cache_571
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_571

theorem verified_row_572 : fork [place ⟨564, 1, 6, 6⟩ cache_564, place ⟨465, 3, 3, 4⟩ cache_465, place ⟨385, 4, 3, 4⟩ cache_385, place ⟨364, 7, 3, 4⟩ cache_364, place ⟨499, 1, 6, 5⟩ cache_499] = cache_572 := by
  decide +kernel

theorem load_entry_572 : entryAt 572 = entry_572 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_572 : CacheEquation 572 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(572 < 6)), load_entry_572]
  change forkRow [placeRow ⟨564, 1, 6, 6⟩ (denote cache_564), placeRow ⟨465, 3, 3, 4⟩ (denote cache_465), placeRow ⟨385, 4, 3, 4⟩ (denote cache_385), placeRow ⟨364, 7, 3, 4⟩ (denote cache_364), placeRow ⟨499, 1, 6, 5⟩ (denote cache_499)] = denote cache_572
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_572

theorem verified_row_573 : fork [place ⟨527, 2, 3, 1⟩ cache_527, place ⟨499, 4, 3, 4⟩ cache_499, place ⟨527, 6, 5, 1⟩ cache_527, place ⟨499, 0, 5, 4⟩ cache_499, place ⟨407, 4, 4, 1⟩ cache_407, place ⟨531, 7, 2, 4⟩ cache_531, place ⟨407, 0, 4, 1⟩ cache_407] = cache_573 := by
  decide +kernel

theorem load_entry_573 : entryAt 573 = entry_573 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_573 : CacheEquation 573 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(573 < 6)), load_entry_573]
  change forkRow [placeRow ⟨527, 2, 3, 1⟩ (denote cache_527), placeRow ⟨499, 4, 3, 4⟩ (denote cache_499), placeRow ⟨527, 6, 5, 1⟩ (denote cache_527), placeRow ⟨499, 0, 5, 4⟩ (denote cache_499), placeRow ⟨407, 4, 4, 1⟩ (denote cache_407), placeRow ⟨531, 7, 2, 4⟩ (denote cache_531), placeRow ⟨407, 0, 4, 1⟩ (denote cache_407)] = denote cache_573
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_573

theorem verified_row_574 : fork [place ⟨497, 0, 2, 4⟩ cache_497, place ⟨539, 4, 4, 6⟩ cache_539, place ⟨355, 0, 2, 4⟩ cache_355, place ⟨390, 3, 2, 4⟩ cache_390, place ⟨544, 0, 2, 4⟩ cache_544, place ⟨462, 1, 4, 5⟩ cache_462, place ⟨563, 4, 5, 4⟩ cache_563, place ⟨540, 4, 4, 6⟩ cache_540, place ⟨518, 0, 2, 4⟩ cache_518, place ⟨495, 4, 2, 4⟩ cache_495] = cache_574 := by
  decide +kernel

theorem load_entry_574 : entryAt 574 = entry_574 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_574 : CacheEquation 574 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(574 < 6)), load_entry_574]
  change forkRow [placeRow ⟨497, 0, 2, 4⟩ (denote cache_497), placeRow ⟨539, 4, 4, 6⟩ (denote cache_539), placeRow ⟨355, 0, 2, 4⟩ (denote cache_355), placeRow ⟨390, 3, 2, 4⟩ (denote cache_390), placeRow ⟨544, 0, 2, 4⟩ (denote cache_544), placeRow ⟨462, 1, 4, 5⟩ (denote cache_462), placeRow ⟨563, 4, 5, 4⟩ (denote cache_563), placeRow ⟨540, 4, 4, 6⟩ (denote cache_540), placeRow ⟨518, 0, 2, 4⟩ (denote cache_518), placeRow ⟨495, 4, 2, 4⟩ (denote cache_495)] = denote cache_574
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_574

theorem verified_row_575 : fork [place ⟨314, 4, 5, 4⟩ cache_314, place ⟨504, 4, 5, 3⟩ cache_504, place ⟨180, 4, 4, 5⟩ cache_180, place ⟨442, 4, 4, 5⟩ cache_442, place ⟨559, 0, 4, 5⟩ cache_559] = cache_575 := by
  decide +kernel

theorem load_entry_575 : entryAt 575 = entry_575 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_575 : CacheEquation 575 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(575 < 6)), load_entry_575]
  change forkRow [placeRow ⟨314, 4, 5, 4⟩ (denote cache_314), placeRow ⟨504, 4, 5, 3⟩ (denote cache_504), placeRow ⟨180, 4, 4, 5⟩ (denote cache_180), placeRow ⟨442, 4, 4, 5⟩ (denote cache_442), placeRow ⟨559, 0, 4, 5⟩ (denote cache_559)] = denote cache_575
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_575

theorem verified_row_576 : fork [place ⟨495, 0, 5, 4⟩ cache_495, place ⟨544, 4, 5, 4⟩ cache_544, place ⟨462, 3, 3, 5⟩ cache_462, place ⟨540, 0, 3, 6⟩ cache_540, place ⟨355, 4, 5, 4⟩ cache_355, place ⟨539, 0, 3, 6⟩ cache_539, place ⟨497, 4, 5, 4⟩ cache_497, place ⟨390, 1, 5, 4⟩ cache_390, place ⟨563, 0, 2, 4⟩ cache_563, place ⟨518, 4, 5, 4⟩ cache_518] = cache_576 := by
  decide +kernel

theorem load_entry_576 : entryAt 576 = entry_576 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_576 : CacheEquation 576 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(576 < 6)), load_entry_576]
  change forkRow [placeRow ⟨495, 0, 5, 4⟩ (denote cache_495), placeRow ⟨544, 4, 5, 4⟩ (denote cache_544), placeRow ⟨462, 3, 3, 5⟩ (denote cache_462), placeRow ⟨540, 0, 3, 6⟩ (denote cache_540), placeRow ⟨355, 4, 5, 4⟩ (denote cache_355), placeRow ⟨539, 0, 3, 6⟩ (denote cache_539), placeRow ⟨497, 4, 5, 4⟩ (denote cache_497), placeRow ⟨390, 1, 5, 4⟩ (denote cache_390), placeRow ⟨563, 0, 2, 4⟩ (denote cache_563), placeRow ⟨518, 4, 5, 4⟩ (denote cache_518)] = denote cache_576
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_576

theorem verified_row_577 : fork [place ⟨64, 7, 5, 4⟩ cache_64, place ⟨64, 1, 3, 1⟩ cache_64, place ⟨443, 1, 5, 4⟩ cache_443, place ⟨443, 7, 3, 1⟩ cache_443] = cache_577 := by
  decide +kernel

theorem load_entry_577 : entryAt 577 = entry_577 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_577 : CacheEquation 577 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(577 < 6)), load_entry_577]
  change forkRow [placeRow ⟨64, 7, 5, 4⟩ (denote cache_64), placeRow ⟨64, 1, 3, 1⟩ (denote cache_64), placeRow ⟨443, 1, 5, 4⟩ (denote cache_443), placeRow ⟨443, 7, 3, 1⟩ (denote cache_443)] = denote cache_577
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_577

theorem verified_row_578 : fork [place ⟨574, 4, 4, 5⟩ cache_574, place ⟨2, 1, 4, 3⟩ cache_2] = cache_578 := by
  decide +kernel

theorem load_entry_578 : entryAt 578 = entry_578 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_578 : CacheEquation 578 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(578 < 6)), load_entry_578]
  change forkRow [placeRow ⟨574, 4, 4, 5⟩ (denote cache_574), placeRow ⟨2, 1, 4, 3⟩ (denote cache_2)] = denote cache_578
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_578

theorem verified_row_579 : fork [place ⟨2, 1, 4, 3⟩ cache_2, place ⟨576, 4, 4, 5⟩ cache_576] = cache_579 := by
  decide +kernel

theorem load_entry_579 : entryAt 579 = entry_579 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_579 : CacheEquation 579 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(579 < 6)), load_entry_579]
  change forkRow [placeRow ⟨2, 1, 4, 3⟩ (denote cache_2), placeRow ⟨576, 4, 4, 5⟩ (denote cache_576)] = denote cache_579
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_579

theorem verified_row_580 : fork [place ⟨2, 7, 4, 2⟩ cache_2, place ⟨579, 0, 3, 3⟩ cache_579] = cache_580 := by
  decide +kernel

theorem load_entry_580 : entryAt 580 = entry_580 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_580 : CacheEquation 580 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(580 < 6)), load_entry_580]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (denote cache_2), placeRow ⟨579, 0, 3, 3⟩ (denote cache_579)] = denote cache_580
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_580

theorem verified_row_581 : fork [place ⟨578, 4, 5, 3⟩ cache_578, place ⟨2, 5, 4, 2⟩ cache_2] = cache_581 := by
  decide +kernel

theorem load_entry_581 : entryAt 581 = entry_581 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_581 : CacheEquation 581 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(581 < 6)), load_entry_581]
  change forkRow [placeRow ⟨578, 4, 5, 3⟩ (denote cache_578), placeRow ⟨2, 5, 4, 2⟩ (denote cache_2)] = denote cache_581
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_581

theorem verified_row_582 : fork [place ⟨40, 3, 4, 3⟩ cache_40, place ⟨446, 5, 5, 3⟩ cache_446, place ⟨523, 0, 7, 0⟩ cache_523, place ⟨480, 4, 5, 3⟩ cache_480, place ⟨567, 4, 5, 4⟩ cache_567] = cache_582 := by
  decide +kernel

theorem load_entry_582 : entryAt 582 = entry_582 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_582 : CacheEquation 582 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(582 < 6)), load_entry_582]
  change forkRow [placeRow ⟨40, 3, 4, 3⟩ (denote cache_40), placeRow ⟨446, 5, 5, 3⟩ (denote cache_446), placeRow ⟨523, 0, 7, 0⟩ (denote cache_523), placeRow ⟨480, 4, 5, 3⟩ (denote cache_480), placeRow ⟨567, 4, 5, 4⟩ (denote cache_567)] = denote cache_582
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_582

theorem verified_row_583 : fork [place ⟨25, 5, 4, 3⟩ cache_25, place ⟨525, 0, 5, 4⟩ cache_525, place ⟨582, 0, 2, 8⟩ cache_582, place ⟨221, 3, 3, 7⟩ cache_221] = cache_583 := by
  decide +kernel

theorem load_entry_583 : entryAt 583 = entry_583 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_583 : CacheEquation 583 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(583 < 6)), load_entry_583]
  change forkRow [placeRow ⟨25, 5, 4, 3⟩ (denote cache_25), placeRow ⟨525, 0, 5, 4⟩ (denote cache_525), placeRow ⟨582, 0, 2, 8⟩ (denote cache_582), placeRow ⟨221, 3, 3, 7⟩ (denote cache_221)] = denote cache_583
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_583

theorem verified_row_584 : fork [place ⟨263, 1, 4, 5⟩ cache_263, place ⟨236, 4, 3, 5⟩ cache_236, place ⟨548, 3, 3, 4⟩ cache_548, place ⟨295, 3, 4, 5⟩ cache_295, place ⟨577, 0, 4, 5⟩ cache_577, place ⟨173, 1, 4, 5⟩ cache_173] = cache_584 := by
  decide +kernel

theorem load_entry_584 : entryAt 584 = entry_584 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_584 : CacheEquation 584 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(584 < 6)), load_entry_584]
  change forkRow [placeRow ⟨263, 1, 4, 5⟩ (denote cache_263), placeRow ⟨236, 4, 3, 5⟩ (denote cache_236), placeRow ⟨548, 3, 3, 4⟩ (denote cache_548), placeRow ⟨295, 3, 4, 5⟩ (denote cache_295), placeRow ⟨577, 0, 4, 5⟩ (denote cache_577), placeRow ⟨173, 1, 4, 5⟩ (denote cache_173)] = denote cache_584
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_584

theorem verified_row_585 : fork [place ⟨236, 2, 5, 1⟩ cache_236, place ⟨300, 4, 4, 5⟩ cache_300, place ⟨479, 1, 4, 5⟩ cache_479, place ⟨577, 0, 4, 5⟩ cache_577, place ⟨183, 3, 4, 5⟩ cache_183, place ⟨527, 6, 5, 1⟩ cache_527] = cache_585 := by
  decide +kernel

theorem load_entry_585 : entryAt 585 = entry_585 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_585 : CacheEquation 585 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(585 < 6)), load_entry_585]
  change forkRow [placeRow ⟨236, 2, 5, 1⟩ (denote cache_236), placeRow ⟨300, 4, 4, 5⟩ (denote cache_300), placeRow ⟨479, 1, 4, 5⟩ (denote cache_479), placeRow ⟨577, 0, 4, 5⟩ (denote cache_577), placeRow ⟨183, 3, 4, 5⟩ (denote cache_183), placeRow ⟨527, 6, 5, 1⟩ (denote cache_527)] = denote cache_585
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_585

theorem verified_row_586 : fork [place ⟨465, 4, 4, 5⟩ cache_465, place ⟨558, 1, 4, 5⟩ cache_558, place ⟨385, 1, 4, 5⟩ cache_385, place ⟨379, 4, 4, 5⟩ cache_379, place ⟨524, 0, 4, 5⟩ cache_524, place ⟨469, 2, 4, 5⟩ cache_469, place ⟨467, 2, 4, 5⟩ cache_467, place ⟨527, 4, 5, 5⟩ cache_527, place ⟨553, 0, 4, 5⟩ cache_553, place ⟨552, 1, 4, 5⟩ cache_552, place ⟨555, 1, 4, 5⟩ cache_555, place ⟨564, 0, 6, 4⟩ cache_564, place ⟨583, 0, 5, 2⟩ cache_583] = cache_586 := by
  decide +kernel

theorem load_entry_586 : entryAt 586 = entry_586 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_586 : CacheEquation 586 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(586 < 6)), load_entry_586]
  change forkRow [placeRow ⟨465, 4, 4, 5⟩ (denote cache_465), placeRow ⟨558, 1, 4, 5⟩ (denote cache_558), placeRow ⟨385, 1, 4, 5⟩ (denote cache_385), placeRow ⟨379, 4, 4, 5⟩ (denote cache_379), placeRow ⟨524, 0, 4, 5⟩ (denote cache_524), placeRow ⟨469, 2, 4, 5⟩ (denote cache_469), placeRow ⟨467, 2, 4, 5⟩ (denote cache_467), placeRow ⟨527, 4, 5, 5⟩ (denote cache_527), placeRow ⟨553, 0, 4, 5⟩ (denote cache_553), placeRow ⟨552, 1, 4, 5⟩ (denote cache_552), placeRow ⟨555, 1, 4, 5⟩ (denote cache_555), placeRow ⟨564, 0, 6, 4⟩ (denote cache_564), placeRow ⟨583, 0, 5, 2⟩ (denote cache_583)] = denote cache_586
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_586

theorem verified_row_587 : fork [place ⟨300, 2, 4, 1⟩ cache_300, place ⟨479, 1, 4, 5⟩ cache_479, place ⟨319, 3, 5, 5⟩ cache_319, place ⟨477, 6, 4, 1⟩ cache_477, place ⟨252, 3, 4, 5⟩ cache_252, place ⟨467, 2, 4, 5⟩ cache_467] = cache_587 := by
  decide +kernel

theorem load_entry_587 : entryAt 587 = entry_587 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_587 : CacheEquation 587 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(587 < 6)), load_entry_587]
  change forkRow [placeRow ⟨300, 2, 4, 1⟩ (denote cache_300), placeRow ⟨479, 1, 4, 5⟩ (denote cache_479), placeRow ⟨319, 3, 5, 5⟩ (denote cache_319), placeRow ⟨477, 6, 4, 1⟩ (denote cache_477), placeRow ⟨252, 3, 4, 5⟩ (denote cache_252), placeRow ⟨467, 2, 4, 5⟩ (denote cache_467)] = denote cache_587
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_587

theorem verified_row_588 : fork [place ⟨3, 1, 3, 3⟩ cache_3, place ⟨586, 0, 4, 5⟩ cache_586] = cache_588 := by
  decide +kernel

theorem load_entry_588 : entryAt 588 = entry_588 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_588 : CacheEquation 588 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(588 < 6)), load_entry_588]
  change forkRow [placeRow ⟨3, 1, 3, 3⟩ (denote cache_3), placeRow ⟨586, 0, 4, 5⟩ (denote cache_586)] = denote cache_588
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_588

theorem verified_row_589 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨588, 0, 4, 5⟩ cache_588] = cache_589 := by
  decide +kernel

theorem load_entry_589 : entryAt 589 = entry_589 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_589 : CacheEquation 589 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(589 < 6)), load_entry_589]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨588, 0, 4, 5⟩ (denote cache_588)] = denote cache_589
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_589

theorem verified_row_590 : fork [place ⟨295, 7, 4, 3⟩ cache_295, place ⟨173, 7, 4, 3⟩ cache_173, place ⟨577, 0, 4, 7⟩ cache_577, place ⟨490, 0, 4, 7⟩ cache_490, place ⟨217, 5, 4, 3⟩ cache_217] = cache_590 := by
  decide +kernel

theorem load_entry_590 : entryAt 590 = entry_590 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_590 : CacheEquation 590 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(590 < 6)), load_entry_590]
  change forkRow [placeRow ⟨295, 7, 4, 3⟩ (denote cache_295), placeRow ⟨173, 7, 4, 3⟩ (denote cache_173), placeRow ⟨577, 0, 4, 7⟩ (denote cache_577), placeRow ⟨490, 0, 4, 7⟩ (denote cache_490), placeRow ⟨217, 5, 4, 3⟩ (denote cache_217)] = denote cache_590
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_590

theorem verified_row_591 : fork [place ⟨524, 0, 4, 5⟩ cache_524, place ⟨529, 1, 4, 1⟩ cache_529, place ⟨529, 3, 4, 1⟩ cache_529, place ⟨538, 1, 4, 1⟩ cache_538, place ⟨538, 3, 4, 1⟩ cache_538, place ⟨197, 5, 4, 1⟩ cache_197] = cache_591 := by
  decide +kernel

theorem load_entry_591 : entryAt 591 = entry_591 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_591 : CacheEquation 591 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(591 < 6)), load_entry_591]
  change forkRow [placeRow ⟨524, 0, 4, 5⟩ (denote cache_524), placeRow ⟨529, 1, 4, 1⟩ (denote cache_529), placeRow ⟨529, 3, 4, 1⟩ (denote cache_529), placeRow ⟨538, 1, 4, 1⟩ (denote cache_538), placeRow ⟨538, 3, 4, 1⟩ (denote cache_538), placeRow ⟨197, 5, 4, 1⟩ (denote cache_197)] = denote cache_591
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_591

theorem verified_row_592 : fork [place ⟨588, 0, 4, 5⟩ cache_588, place ⟨108, 7, 3, 0⟩ cache_108] = cache_592 := by
  decide +kernel

theorem load_entry_592 : entryAt 592 = entry_592 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_592 : CacheEquation 592 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(592 < 6)), load_entry_592]
  change forkRow [placeRow ⟨588, 0, 4, 5⟩ (denote cache_588), placeRow ⟨108, 7, 3, 0⟩ (denote cache_108)] = denote cache_592
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_592

theorem verified_row_593 : fork [place ⟨2, 7, 4, 2⟩ cache_2, place ⟨586, 0, 4, 5⟩ cache_586] = cache_593 := by
  decide +kernel

theorem load_entry_593 : entryAt 593 = entry_593 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_593 : CacheEquation 593 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(593 < 6)), load_entry_593]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (denote cache_2), placeRow ⟨586, 0, 4, 5⟩ (denote cache_586)] = denote cache_593
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_593

theorem verified_row_594 : fork [place ⟨30, 1, 4, 3⟩ cache_30, place ⟨476, 1, 4, 3⟩ cache_476, place ⟨588, 0, 4, 5⟩ cache_588] = cache_594 := by
  decide +kernel

theorem load_entry_594 : entryAt 594 = entry_594 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_594 : CacheEquation 594 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(594 < 6)), load_entry_594]
  change forkRow [placeRow ⟨30, 1, 4, 3⟩ (denote cache_30), placeRow ⟨476, 1, 4, 3⟩ (denote cache_476), placeRow ⟨588, 0, 4, 5⟩ (denote cache_588)] = denote cache_594
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_594

theorem verified_row_595 : fork [place ⟨460, 4, 2, 4⟩ cache_460, place ⟨460, 2, 5, 4⟩ cache_460, place ⟨586, 1, 5, 4⟩ cache_586, place ⟨411, 4, 5, 4⟩ cache_411, place ⟨551, 1, 2, 4⟩ cache_551, place ⟨406, 5, 5, 4⟩ cache_406, place ⟨572, 0, 2, 4⟩ cache_572] = cache_595 := by
  decide +kernel

theorem load_entry_595 : entryAt 595 = entry_595 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_595 : CacheEquation 595 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(595 < 6)), load_entry_595]
  change forkRow [placeRow ⟨460, 4, 2, 4⟩ (denote cache_460), placeRow ⟨460, 2, 5, 4⟩ (denote cache_460), placeRow ⟨586, 1, 5, 4⟩ (denote cache_586), placeRow ⟨411, 4, 5, 4⟩ (denote cache_411), placeRow ⟨551, 1, 2, 4⟩ (denote cache_551), placeRow ⟨406, 5, 5, 4⟩ (denote cache_406), placeRow ⟨572, 0, 2, 4⟩ (denote cache_572)] = denote cache_595
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_595

theorem verified_row_596 : fork [place ⟨385, 5, 4, 2⟩ cache_385, place ⟨592, 0, 5, 6⟩ cache_592, place ⟨330, 1, 4, 6⟩ cache_330, place ⟨529, 5, 4, 6⟩ cache_529, place ⟨385, 1, 4, 6⟩ cache_385, place ⟨330, 5, 4, 2⟩ cache_330] = cache_596 := by
  decide +kernel

theorem load_entry_596 : entryAt 596 = entry_596 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_596 : CacheEquation 596 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(596 < 6)), load_entry_596]
  change forkRow [placeRow ⟨385, 5, 4, 2⟩ (denote cache_385), placeRow ⟨592, 0, 5, 6⟩ (denote cache_592), placeRow ⟨330, 1, 4, 6⟩ (denote cache_330), placeRow ⟨529, 5, 4, 6⟩ (denote cache_529), placeRow ⟨385, 1, 4, 6⟩ (denote cache_385), placeRow ⟨330, 5, 4, 2⟩ (denote cache_330)] = denote cache_596
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_596

theorem verified_row_597 : fork [place ⟨24, 6, 2, 3⟩ cache_24, place ⟨221, 0, 6, 4⟩ cache_221, place ⟨199, 3, 2, 4⟩ cache_199, place ⟨594, 1, 6, 5⟩ cache_594] = cache_597 := by
  decide +kernel

theorem load_entry_597 : entryAt 597 = entry_597 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_597 : CacheEquation 597 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(597 < 6)), load_entry_597]
  change forkRow [placeRow ⟨24, 6, 2, 3⟩ (denote cache_24), placeRow ⟨221, 0, 6, 4⟩ (denote cache_221), placeRow ⟨199, 3, 2, 4⟩ (denote cache_199), placeRow ⟨594, 1, 6, 5⟩ (denote cache_594)] = denote cache_597
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_597

theorem verified_row_598 : fork [place ⟨594, 0, 5, 6⟩ cache_594, place ⟨456, 5, 4, 2⟩ cache_456, place ⟨254, 1, 3, 2⟩ cache_254, place ⟨554, 1, 3, 2⟩ cache_554, place ⟨465, 0, 4, 6⟩ cache_465] = cache_598 := by
  decide +kernel

theorem load_entry_598 : entryAt 598 = entry_598 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_598 : CacheEquation 598 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(598 < 6)), load_entry_598]
  change forkRow [placeRow ⟨594, 0, 5, 6⟩ (denote cache_594), placeRow ⟨456, 5, 4, 2⟩ (denote cache_456), placeRow ⟨254, 1, 3, 2⟩ (denote cache_254), placeRow ⟨554, 1, 3, 2⟩ (denote cache_554), placeRow ⟨465, 0, 4, 6⟩ (denote cache_465)] = denote cache_598
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_598

theorem verified_row_599 : fork [place ⟨578, 4, 5, 3⟩ cache_578, place ⟨492, 0, 3, 1⟩ cache_492, place ⟨512, 4, 3, 1⟩ cache_512, place ⟨586, 4, 4, 5⟩ cache_586, place ⟨485, 0, 5, 3⟩ cache_485, place ⟨579, 4, 5, 3⟩ cache_579] = cache_599 := by
  decide +kernel

theorem load_entry_599 : entryAt 599 = entry_599 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_599 : CacheEquation 599 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(599 < 6)), load_entry_599]
  change forkRow [placeRow ⟨578, 4, 5, 3⟩ (denote cache_578), placeRow ⟨492, 0, 3, 1⟩ (denote cache_492), placeRow ⟨512, 4, 3, 1⟩ (denote cache_512), placeRow ⟨586, 4, 4, 5⟩ (denote cache_586), placeRow ⟨485, 0, 5, 3⟩ (denote cache_485), placeRow ⟨579, 4, 5, 3⟩ (denote cache_579)] = denote cache_599
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_599

end SnakyCertificate.Check

end OAI
