import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_600 : fork [place ⟨448, 0, 4, 5⟩ cache_448, place ⟨278, 2, 1, 4⟩ cache_278, place ⟨592, 5, 5, 3⟩ cache_592, place ⟨403, 5, 5, 4⟩ cache_403, place ⟨146, 5, 4, 3⟩ cache_146] = cache_600 := by
  decide +kernel

theorem load_entry_600 : entryAt 600 = entry_600 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_600 : CacheEquation 600 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(600 < 6)), load_entry_600]
  change forkRow [placeRow ⟨448, 0, 4, 5⟩ (denote cache_448), placeRow ⟨278, 2, 1, 4⟩ (denote cache_278), placeRow ⟨592, 5, 5, 3⟩ (denote cache_592), placeRow ⟨403, 5, 5, 4⟩ (denote cache_403), placeRow ⟨146, 5, 4, 3⟩ (denote cache_146)] = denote cache_600
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_600

theorem verified_row_601 : fork [place ⟨437, 6, 4, 1⟩ cache_437, place ⟨553, 0, 4, 5⟩ cache_553, place ⟨592, 0, 5, 5⟩ cache_592, place ⟨236, 4, 3, 5⟩ cache_236, place ⟨469, 4, 4, 1⟩ cache_469] = cache_601 := by
  decide +kernel

theorem load_entry_601 : entryAt 601 = entry_601 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_601 : CacheEquation 601 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(601 < 6)), load_entry_601]
  change forkRow [placeRow ⟨437, 6, 4, 1⟩ (denote cache_437), placeRow ⟨553, 0, 4, 5⟩ (denote cache_553), placeRow ⟨592, 0, 5, 5⟩ (denote cache_592), placeRow ⟨236, 4, 3, 5⟩ (denote cache_236), placeRow ⟨469, 4, 4, 1⟩ (denote cache_469)] = denote cache_601
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_601

theorem verified_row_602 : fork [place ⟨553, 0, 4, 7⟩ cache_553, place ⟨467, 4, 4, 3⟩ cache_467, place ⟨592, 0, 5, 7⟩ cache_592, place ⟨437, 6, 4, 3⟩ cache_437, place ⟨236, 4, 3, 7⟩ cache_236] = cache_602 := by
  decide +kernel

theorem load_entry_602 : entryAt 602 = entry_602 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_602 : CacheEquation 602 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(602 < 6)), load_entry_602]
  change forkRow [placeRow ⟨553, 0, 4, 7⟩ (denote cache_553), placeRow ⟨467, 4, 4, 3⟩ (denote cache_467), placeRow ⟨592, 0, 5, 7⟩ (denote cache_592), placeRow ⟨437, 6, 4, 3⟩ (denote cache_437), placeRow ⟨236, 4, 3, 7⟩ (denote cache_236)] = denote cache_602
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_602

theorem verified_row_603 : fork [place ⟨505, 1, 5, 4⟩ cache_505, place ⟨505, 5, 5, 4⟩ cache_505, place ⟨586, 5, 5, 4⟩ cache_586, place ⟨551, 7, 5, 4⟩ cache_551, place ⟨531, 6, 4, 2⟩ cache_531, place ⟨586, 1, 5, 4⟩ cache_586, place ⟨585, 1, 5, 4⟩ cache_585, place ⟨585, 5, 5, 4⟩ cache_585, place ⟨551, 3, 5, 4⟩ cache_551, place ⟨573, 1, 5, 4⟩ cache_573, place ⟨533, 5, 5, 4⟩ cache_533, place ⟨533, 1, 5, 4⟩ cache_533] = cache_603 := by
  decide +kernel

theorem load_entry_603 : entryAt 603 = entry_603 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_603 : CacheEquation 603 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(603 < 6)), load_entry_603]
  change forkRow [placeRow ⟨505, 1, 5, 4⟩ (denote cache_505), placeRow ⟨505, 5, 5, 4⟩ (denote cache_505), placeRow ⟨586, 5, 5, 4⟩ (denote cache_586), placeRow ⟨551, 7, 5, 4⟩ (denote cache_551), placeRow ⟨531, 6, 4, 2⟩ (denote cache_531), placeRow ⟨586, 1, 5, 4⟩ (denote cache_586), placeRow ⟨585, 1, 5, 4⟩ (denote cache_585), placeRow ⟨585, 5, 5, 4⟩ (denote cache_585), placeRow ⟨551, 3, 5, 4⟩ (denote cache_551), placeRow ⟨573, 1, 5, 4⟩ (denote cache_573), placeRow ⟨533, 5, 5, 4⟩ (denote cache_533), placeRow ⟨533, 1, 5, 4⟩ (denote cache_533)] = denote cache_603
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_603

theorem verified_row_604 : fork [place ⟨597, 0, 3, 4⟩ cache_597, place ⟨375, 2, 4, 3⟩ cache_375, place ⟨597, 1, 4, 3⟩ cache_597, place ⟨375, 3, 3, 4⟩ cache_375, place ⟨350, 3, 4, 3⟩ cache_350, place ⟨350, 2, 3, 4⟩ cache_350] = cache_604 := by
  decide +kernel

theorem load_entry_604 : entryAt 604 = entry_604 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_604 : CacheEquation 604 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(604 < 6)), load_entry_604]
  change forkRow [placeRow ⟨597, 0, 3, 4⟩ (denote cache_597), placeRow ⟨375, 2, 4, 3⟩ (denote cache_375), placeRow ⟨597, 1, 4, 3⟩ (denote cache_597), placeRow ⟨375, 3, 3, 4⟩ (denote cache_375), placeRow ⟨350, 3, 4, 3⟩ (denote cache_350), placeRow ⟨350, 2, 3, 4⟩ (denote cache_350)] = denote cache_604
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_604

theorem verified_row_605 : fork [place ⟨400, 5, 4, 3⟩ cache_400, place ⟨383, 6, 3, 4⟩ cache_383, place ⟨530, 4, 4, 3⟩ cache_530, place ⟨596, 1, 3, 4⟩ cache_596, place ⟨522, 2, 4, 3⟩ cache_522, place ⟨598, 0, 4, 3⟩ cache_598, place ⟨537, 3, 3, 4⟩ cache_537, place ⟨520, 1, 4, 3⟩ cache_520, place ⟨550, 4, 4, 3⟩ cache_550] = cache_605 := by
  decide +kernel

theorem load_entry_605 : entryAt 605 = entry_605 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_605 : CacheEquation 605 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(605 < 6)), load_entry_605]
  change forkRow [placeRow ⟨400, 5, 4, 3⟩ (denote cache_400), placeRow ⟨383, 6, 3, 4⟩ (denote cache_383), placeRow ⟨530, 4, 4, 3⟩ (denote cache_530), placeRow ⟨596, 1, 3, 4⟩ (denote cache_596), placeRow ⟨522, 2, 4, 3⟩ (denote cache_522), placeRow ⟨598, 0, 4, 3⟩ (denote cache_598), placeRow ⟨537, 3, 3, 4⟩ (denote cache_537), placeRow ⟨520, 1, 4, 3⟩ (denote cache_520), placeRow ⟨550, 4, 4, 3⟩ (denote cache_550)] = denote cache_605
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_605

theorem verified_row_606 : fork [place ⟨123, 1, 4, 3⟩ cache_123, place ⟨274, 0, 4, 3⟩ cache_274, place ⟨605, 0, 6, 4⟩ cache_605, place ⟨119, 1, 4, 3⟩ cache_119] = cache_606 := by
  decide +kernel

theorem load_entry_606 : entryAt 606 = entry_606 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_606 : CacheEquation 606 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(606 < 6)), load_entry_606]
  change forkRow [placeRow ⟨123, 1, 4, 3⟩ (denote cache_123), placeRow ⟨274, 0, 4, 3⟩ (denote cache_274), placeRow ⟨605, 0, 6, 4⟩ (denote cache_605), placeRow ⟨119, 1, 4, 3⟩ (denote cache_119)] = denote cache_606
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_606

theorem verified_row_607 : fork [place ⟨420, 3, 1, 2⟩ cache_420, place ⟨419, 3, 1, 4⟩ cache_419, place ⟨589, 0, 5, 5⟩ cache_589, place ⟨314, 0, 3, 4⟩ cache_314, place ⟨571, 1, 7, 3⟩ cache_571] = cache_607 := by
  decide +kernel

theorem load_entry_607 : entryAt 607 = entry_607 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_607 : CacheEquation 607 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(607 < 6)), load_entry_607]
  change forkRow [placeRow ⟨420, 3, 1, 2⟩ (denote cache_420), placeRow ⟨419, 3, 1, 4⟩ (denote cache_419), placeRow ⟨589, 0, 5, 5⟩ (denote cache_589), placeRow ⟨314, 0, 3, 4⟩ (denote cache_314), placeRow ⟨571, 1, 7, 3⟩ (denote cache_571)] = denote cache_607
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_607

theorem verified_row_608 : fork [place ⟨486, 4, 4, 5⟩ cache_486, place ⟨515, 1, 4, 5⟩ cache_515, place ⟨580, 0, 4, 5⟩ cache_580, place ⟨521, 0, 4, 5⟩ cache_521, place ⟨581, 4, 4, 5⟩ cache_581, place ⟨593, 0, 4, 5⟩ cache_593, place ⟨599, 4, 4, 5⟩ cache_599, place ⟨606, 1, 6, 2⟩ cache_606] = cache_608 := by
  decide +kernel

theorem load_entry_608 : entryAt 608 = entry_608 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_608 : CacheEquation 608 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(608 < 6)), load_entry_608]
  change forkRow [placeRow ⟨486, 4, 4, 5⟩ (denote cache_486), placeRow ⟨515, 1, 4, 5⟩ (denote cache_515), placeRow ⟨580, 0, 4, 5⟩ (denote cache_580), placeRow ⟨521, 0, 4, 5⟩ (denote cache_521), placeRow ⟨581, 4, 4, 5⟩ (denote cache_581), placeRow ⟨593, 0, 4, 5⟩ (denote cache_593), placeRow ⟨599, 4, 4, 5⟩ (denote cache_599), placeRow ⟨606, 1, 6, 2⟩ (denote cache_606)] = denote cache_608
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_608

theorem verified_row_609 : fork [place ⟨286, 4, 4, 5⟩ cache_286, place ⟨107, 3, 4, 5⟩ cache_107, place ⟨532, 4, 4, 5⟩ cache_532, place ⟨542, 0, 4, 5⟩ cache_542, place ⟨221, 3, 4, 5⟩ cache_221, place ⟨562, 4, 4, 5⟩ cache_562, place ⟨575, 4, 4, 5⟩ cache_575, place ⟨604, 1, 6, 4⟩ cache_604] = cache_609 := by
  decide +kernel

theorem load_entry_609 : entryAt 609 = entry_609 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_609 : CacheEquation 609 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(609 < 6)), load_entry_609]
  change forkRow [placeRow ⟨286, 4, 4, 5⟩ (denote cache_286), placeRow ⟨107, 3, 4, 5⟩ (denote cache_107), placeRow ⟨532, 4, 4, 5⟩ (denote cache_532), placeRow ⟨542, 0, 4, 5⟩ (denote cache_542), placeRow ⟨221, 3, 4, 5⟩ (denote cache_221), placeRow ⟨562, 4, 4, 5⟩ (denote cache_562), placeRow ⟨575, 4, 4, 5⟩ (denote cache_575), placeRow ⟨604, 1, 6, 4⟩ (denote cache_604)] = denote cache_609
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_609

theorem verified_row_610 : fork [place ⟨221, 2, 5, 4⟩ cache_221, place ⟨286, 5, 5, 4⟩ cache_286, place ⟨107, 2, 5, 4⟩ cache_107, place ⟨472, 1, 5, 4⟩ cache_472, place ⟨566, 1, 5, 4⟩ cache_566, place ⟨532, 5, 5, 4⟩ cache_532, place ⟨542, 1, 5, 4⟩ cache_542, place ⟨609, 0, 2, 6⟩ cache_609] = cache_610 := by
  decide +kernel

theorem load_entry_610 : entryAt 610 = entry_610 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_610 : CacheEquation 610 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(610 < 6)), load_entry_610]
  change forkRow [placeRow ⟨221, 2, 5, 4⟩ (denote cache_221), placeRow ⟨286, 5, 5, 4⟩ (denote cache_286), placeRow ⟨107, 2, 5, 4⟩ (denote cache_107), placeRow ⟨472, 1, 5, 4⟩ (denote cache_472), placeRow ⟨566, 1, 5, 4⟩ (denote cache_566), placeRow ⟨532, 5, 5, 4⟩ (denote cache_532), placeRow ⟨542, 1, 5, 4⟩ (denote cache_542), placeRow ⟨609, 0, 2, 6⟩ (denote cache_609)] = denote cache_610
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_610

theorem verified_row_611 : fork [place ⟨456, 2, 5, 4⟩ cache_456, place ⟨456, 4, 1, 4⟩ cache_456, place ⟨594, 7, 1, 3⟩ cache_594, place ⟨594, 1, 5, 5⟩ cache_594] = cache_611 := by
  decide +kernel

theorem load_entry_611 : entryAt 611 = entry_611 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_611 : CacheEquation 611 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(611 < 6)), load_entry_611]
  change forkRow [placeRow ⟨456, 2, 5, 4⟩ (denote cache_456), placeRow ⟨456, 4, 1, 4⟩ (denote cache_456), placeRow ⟨594, 7, 1, 3⟩ (denote cache_594), placeRow ⟨594, 1, 5, 5⟩ (denote cache_594)] = denote cache_611
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_611

theorem verified_row_612 : fork [place ⟨589, 1, 5, 5⟩ cache_589, place ⟨589, 7, 0, 3⟩ cache_589] = cache_612 := by
  decide +kernel

theorem load_entry_612 : entryAt 612 = entry_612 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_612 : CacheEquation 612 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(612 < 6)), load_entry_612]
  change forkRow [placeRow ⟨589, 1, 5, 5⟩ (denote cache_589), placeRow ⟨589, 7, 0, 3⟩ (denote cache_589)] = denote cache_612
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_612

theorem verified_row_613 : fork [place ⟨607, 5, 5, 4⟩ cache_607, place ⟨503, 3, 1, 4⟩ cache_503, place ⟨592, 7, 1, 3⟩ cache_592, place ⟨592, 5, 5, 3⟩ cache_592, place ⟨607, 7, 1, 4⟩ cache_607, place ⟨612, 4, 1, 4⟩ cache_612, place ⟨612, 0, 5, 4⟩ cache_612] = cache_613 := by
  decide +kernel

theorem load_entry_613 : entryAt 613 = entry_613 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_613 : CacheEquation 613 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(613 < 6)), load_entry_613]
  change forkRow [placeRow ⟨607, 5, 5, 4⟩ (denote cache_607), placeRow ⟨503, 3, 1, 4⟩ (denote cache_503), placeRow ⟨592, 7, 1, 3⟩ (denote cache_592), placeRow ⟨592, 5, 5, 3⟩ (denote cache_592), placeRow ⟨607, 7, 1, 4⟩ (denote cache_607), placeRow ⟨612, 4, 1, 4⟩ (denote cache_612), placeRow ⟨612, 0, 5, 4⟩ (denote cache_612)] = denote cache_613
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_613

theorem verified_row_614 : fork [place ⟨608, 1, 7, 5⟩ cache_608, place ⟨543, 3, 5, 6⟩ cache_543, place ⟨370, 6, 3, 4⟩ cache_370, place ⟨392, 7, 3, 4⟩ cache_392, place ⟨610, 3, 5, 6⟩ cache_610, place ⟨600, 0, 6, 4⟩ cache_600, place ⟨613, 0, 6, 4⟩ cache_613] = cache_614 := by
  decide +kernel

theorem load_entry_614 : entryAt 614 = entry_614 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_614 : CacheEquation 614 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(614 < 6)), load_entry_614]
  change forkRow [placeRow ⟨608, 1, 7, 5⟩ (denote cache_608), placeRow ⟨543, 3, 5, 6⟩ (denote cache_543), placeRow ⟨370, 6, 3, 4⟩ (denote cache_370), placeRow ⟨392, 7, 3, 4⟩ (denote cache_392), placeRow ⟨610, 3, 5, 6⟩ (denote cache_610), placeRow ⟨600, 0, 6, 4⟩ (denote cache_600), placeRow ⟨613, 0, 6, 4⟩ (denote cache_613)] = denote cache_614
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_614

theorem verified_row_615 : fork [place ⟨602, 7, 6, 4⟩ cache_602, place ⟨614, 1, 4, 3⟩ cache_614, place ⟨533, 5, 6, 4⟩ cache_533, place ⟨590, 7, 6, 4⟩ cache_590, place ⟨611, 6, 3, 4⟩ cache_611, place ⟨587, 3, 3, 4⟩ cache_587, place ⟨601, 5, 6, 4⟩ cache_601, place ⟨406, 1, 6, 4⟩ cache_406, place ⟨591, 3, 3, 4⟩ cache_591, place ⟨586, 3, 3, 4⟩ cache_586, place ⟨584, 5, 6, 4⟩ cache_584, place ⟨406, 3, 3, 4⟩ cache_406] = cache_615 := by
  decide +kernel

theorem load_entry_615 : entryAt 615 = entry_615 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_615 : CacheEquation 615 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(615 < 6)), load_entry_615]
  change forkRow [placeRow ⟨602, 7, 6, 4⟩ (denote cache_602), placeRow ⟨614, 1, 4, 3⟩ (denote cache_614), placeRow ⟨533, 5, 6, 4⟩ (denote cache_533), placeRow ⟨590, 7, 6, 4⟩ (denote cache_590), placeRow ⟨611, 6, 3, 4⟩ (denote cache_611), placeRow ⟨587, 3, 3, 4⟩ (denote cache_587), placeRow ⟨601, 5, 6, 4⟩ (denote cache_601), placeRow ⟨406, 1, 6, 4⟩ (denote cache_406), placeRow ⟨591, 3, 3, 4⟩ (denote cache_591), placeRow ⟨586, 3, 3, 4⟩ (denote cache_586), placeRow ⟨584, 5, 6, 4⟩ (denote cache_584), placeRow ⟨406, 3, 3, 4⟩ (denote cache_406)] = denote cache_615
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_615

end SnakyCertificate.Check

end OAI
