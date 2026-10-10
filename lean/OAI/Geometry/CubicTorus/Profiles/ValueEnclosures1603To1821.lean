import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures1384To1602

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape
lemma b1602 : Encl e1602 (220945423463 / 500000000000 : ℝ) (441890846931 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1601 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1603 : ℝ := e1600 / e1602
lemma b1603 : Encl e1603 (59789134481 / 125000000000 : ℝ) (59789134483 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1600 b1602 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1604 : ℝ := e5 - e1603
lemma b1604 : Encl e1604 (65210865517 / 125000000000 : ℝ) (65210865519 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b1603 (by norm_num) (by norm_num)

def e1605 : ℝ := e8 * e1539
lemma b1605 : Encl e1605 (126821848031 / 200000000000 : ℝ) (634109240161 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1539 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1606 : ℝ := e5 - e1605
lemma b1606 : Encl e1606 (365890759839 / 1000000000000 : ℝ) (73178151969 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b1605 (by norm_num) (by norm_num)

def e1607 : ℝ := e1606 / e1541
lemma b1607 : Encl e1607 (76984804753 / 125000000000 : ℝ) (15396960951 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b1606 b1541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1608 : ℝ := e5 - e1607
lemma b1608 : Encl e1608 (9603039049 / 25000000000 : ℝ) (48015195247 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b1607 (by norm_num) (by norm_num)

def e1609 : ℝ := e1604 - e1608
lemma b1609 : Encl e1609 (1719567027 / 12500000000 : ℝ) (8597835137 / 62500000000 : ℝ) := by
  exact Encl.sub b1604 b1608 (by norm_num) (by norm_num)

def e1610 : ℝ := e1597 * e1609
lemma b1610 : Encl e1610 (4792095701 / 1000000000000 : ℝ) (479209571 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1597 b1609 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1611 : ℝ := e1595 - e1585
lemma b1611 : Encl e1611 (35231773741 / 1000000000000 : ℝ) (8807943447 / 250000000000 : ℝ) := by
  exact Encl.sub b1595 b1585 (by norm_num) (by norm_num)

def e1612 : ℝ := e5 + e1602
lemma b1612 : Encl e1612 (720945423463 / 500000000000 : ℝ) (1441890846931 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1602 (by norm_num) (by norm_num)

def e1613 : ℝ := e1576 / e1612
lemma b1613 : Encl e1613 (622147528271 / 1000000000000 : ℝ) (155536882069 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1576 b1612 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1614 : ℝ := e1613 ^ 2
lemma b1614 : Encl e1614 (387067546933 / 1000000000000 : ℝ) (19353377347 / 50000000000 : ℝ) := by
  exact Encl.pow b1613 (by norm_num) 2 (by norm_num) (by norm_num)

def e1615 : ℝ := e5 + e1614
lemma b1615 : Encl e1615 (1387067546933 / 1000000000000 : ℝ) (69353377347 / 50000000000 : ℝ) := by
  exact Encl.add b5 b1614 (by norm_num) (by norm_num)

def e1616 : ℝ := Real.sqrt e1615
lemma b1616 : Encl e1616 (1177738318529 / 1000000000000 : ℝ) (1177738318533 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1615 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1617 : ℝ := e5 + e1616
lemma b1617 : Encl e1617 (2177738318529 / 1000000000000 : ℝ) (2177738318533 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1616 (by norm_num) (by norm_num)

def e1618 : ℝ := e1613 / e1617
lemma b1618 : Encl e1618 (71421290953 / 250000000000 : ℝ) (35710645477 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1613 b1617 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1619 : ℝ := Real.arcsin e1576
lemma b1619 : Encl e1619 (1113090939099 / 1000000000000 : ℝ) (278272734779 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e1576) (a := (71421290953 / 250000000000 : ℝ)) (b := (35710645477 / 125000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (112133603307 / 125000000000 : ℝ) by norm_num).trans b1576.1
        exact b1576.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1576) (71421290953 / 250000000000 : ℝ) (35710645477 / 125000000000 : ℝ) from b1618) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1620 : ℝ := e59 * e1619
lemma b1620 : Encl e1620 (28383818947 / 50000000000 : ℝ) (11353527579 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1619 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1621 : ℝ := e61 * e1576
lemma b1621 : Encl e1621 (439563724963 / 1000000000000 : ℝ) (87912744993 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1576 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1622 : ℝ := e1621 * e1602
lemma b1622 : Encl e1622 (194239186701 / 1000000000000 : ℝ) (38847837341 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1621 b1602 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1623 : ℝ := e1620 - e1622
lemma b1623 : Encl e1623 (74687438447 / 200000000000 : ℝ) (373437192249 / 1000000000000 : ℝ) := by
  exact Encl.sub b1620 b1622 (by norm_num) (by norm_num)

def e1624 : ℝ := e43 * e1602
lemma b1624 : Encl e1624 (220945423463 / 10000000000 : ℝ) (441890846931 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1602 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1625 : ℝ := e1576 / e1624
lemma b1625 : Encl e1625 (4060137623 / 100000000000 : ℝ) (5075172029 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1576 b1624 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1626 : ℝ := e1623 - e1625
lemma b1626 : Encl e1626 (332835816003 / 1000000000000 : ℝ) (332835816019 / 1000000000000 : ℝ) := by
  exact Encl.sub b1623 b1625 (by norm_num) (by norm_num)

def e1627 : ℝ := e1626 - e1556
lemma b1627 : Encl e1627 (117405991627 / 1000000000000 : ℝ) (117405991657 / 1000000000000 : ℝ) := by
  exact Encl.sub b1626 b1556 (by norm_num) (by norm_num)

def e1628 : ℝ := e1611 * e1627
lemma b1628 : Encl e1628 (1034105333 / 250000000000 : ℝ) (206821067 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b1611 b1627 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1629 : ℝ := e1610 + e1628
lemma b1629 : Encl e1629 (8928517033 / 1000000000000 : ℝ) (178570341 / 20000000000 : ℝ) := by
  exact Encl.add b1610 b1628 (by norm_num) (by norm_num)

def e1630 : ℝ := e1576 - e1509
lemma b1630 : Encl e1630 (92674492151 / 1000000000000 : ℝ) (23168623039 / 250000000000 : ℝ) := by
  exact Encl.sub b1576 b1509 (by norm_num) (by norm_num)

def e1631 : ℝ := e1629 / e1630
lemma b1631 : Encl e1631 (48171383653 / 500000000000 : ℝ) (19268553499 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1629 b1630 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1632 : ℝ := e1574 + e1631
lemma b1632 : Encl e1632 (-73287539193 / 500000000000 : ℝ) (-73287539077 / 500000000000 : ℝ) := by
  exact Encl.add b1574 b1631 (by norm_num) (by norm_num)

def e1633 : ℝ := e4 * e1595
lemma b1633 : Encl e1633 (354784324093 / 500000000000 : ℝ) (177392162053 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1595 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1634 : ℝ := e4 / e1507
lemma b1634 : Encl e1634 (167753104849 / 200000000000 : ℝ) (838765524247 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1635 : ℝ := e89 * e1634
lemma b1635 : Encl e1635 (743336591727 / 500000000000 : ℝ) (1486673183459 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1634 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1636 : ℝ := e1634 ^ 2
lemma b1636 : Encl e1636 (703527604661 / 1000000000000 : ℝ) (351763802333 / 500000000000 : ℝ) := by
  exact Encl.pow b1634 (by norm_num) 2 (by norm_num) (by norm_num)

def e1637 : ℝ := e91 * e1636
lemma b1637 : Encl e1637 (552549288599 / 1000000000000 : ℝ) (110509857721 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1636 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1638 : ℝ := e5 + e1637
lemma b1638 : Encl e1638 (1552549288599 / 1000000000000 : ℝ) (310509857721 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1637 (by norm_num) (by norm_num)

def e1639 : ℝ := Real.sqrt e1638
lemma b1639 : Encl e1639 (623006679057 / 500000000000 : ℝ) (1246013358117 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1638 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1640 : ℝ := e1635 * e1639
lemma b1640 : Encl e1640 (1852414645733 / 1000000000000 : ℝ) (370482929149 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1635 b1639 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1641 : ℝ := e97 * e1636
lemma b1641 : Encl e1641 (1105098577199 / 1000000000000 : ℝ) (1105098577209 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1636 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1642 : ℝ := e1640 - e1641
lemma b1642 : Encl e1642 (186829017131 / 250000000000 : ℝ) (373658034273 / 500000000000 : ℝ) := by
  exact Encl.sub b1640 b1641 (by norm_num) (by norm_num)

def e1643 : ℝ := e1576 * e1642
lemma b1643 : Encl e1643 (335196974291 / 500000000000 : ℝ) (167598487151 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1576 b1642 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1644 : ℝ := e1633 - e1643
lemma b1644 : Encl e1644 (19587349791 / 500000000000 : ℝ) (3917469963 / 100000000000 : ℝ) := by
  exact Encl.sub b1633 b1643 (by norm_num) (by norm_num)

def e1645 : ℝ := e165 - e1604
lemma b1645 : Encl e1645 (198313075823 / 1000000000000 : ℝ) (49578268973 / 250000000000 : ℝ) := by
  exact Encl.sub b165 b1604 (by norm_num) (by norm_num)

def e1646 : ℝ := e1644 * e1645
lemma b1646 : Encl e1646 (60694181 / 7812500000 : ℝ) (7768855181 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1644 b1645 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1647 : ℝ := e1642 - e1595
lemma b1647 : Encl e1647 (30394180931 / 1000000000000 : ℝ) (30394180977 / 1000000000000 : ℝ) := by
  exact Encl.sub b1642 b1595 (by norm_num) (by norm_num)

def e1648 : ℝ := e183 - e1626
lemma b1648 : Encl e1648 (187316953493 / 1000000000000 : ℝ) (4682923841 / 25000000000 : ℝ) := by
  exact Encl.sub b183 b1626 (by norm_num) (by norm_num)

def e1649 : ℝ := e1647 * e1648
lemma b1649 : Encl e1649 (45546763 / 8000000000 : ℝ) (5693345389 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1647 b1648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1650 : ℝ := e1646 + e1649
lemma b1650 : Encl e1650 (13462200543 / 1000000000000 : ℝ) (1346220057 / 100000000000 : ℝ) := by
  exact Encl.add b1646 b1649 (by norm_num) (by norm_num)

def e1651 : ℝ := e4 - e1576
lemma b1651 : Encl e1651 (11584311519 / 125000000000 : ℝ) (18534898431 / 200000000000 : ℝ) := by
  exact Encl.sub b4 b1576 (by norm_num) (by norm_num)

def e1652 : ℝ := e1650 / e1651
lemma b1652 : Encl e1652 (36315819569 / 250000000000 : ℝ) (145263278573 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1650 b1651 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1653 : ℝ := e1632 + e1652
lemma b1653 : Encl e1653 (-131180011 / 100000000000 : ℝ) (-1311799581 / 1000000000000 : ℝ) := by
  exact Encl.add b1632 b1652 (by norm_num) (by norm_num)

def e1654 : ℝ := e924 / e1507
lemma b1654 : Encl e1654 (813559322033 / 1000000000000 : ℝ) (406779661017 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1655 : ℝ := min e7 e1654
lemma b1655 : Encl e1655 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1654 (by norm_num) (by norm_num)

def e1656 : ℝ := e1655 - e5
lemma b1656 : Encl e1656 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1655 b5 (by norm_num) (by norm_num)

def e1657 : ℝ := e23 * e1507
lemma b1657 : Encl e1657 (59 / 25 : ℝ) (59 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b1507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1658 : ℝ := e1657 * e1518
lemma b1658 : Encl e1658 (221372559979 / 125000000000 : ℝ) (1770980479837 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1657 b1518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1659 : ℝ := e1658 / e0
lemma b1659 : Encl e1659 (563720594969 / 1000000000000 : ℝ) (563720594971 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1658 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1660 : ℝ := e1656 + e1659
lemma b1660 : Encl e1660 (49082141757 / 200000000000 : ℝ) (61352677197 / 250000000000 : ℝ) := by
  exact Encl.add b1656 b1659 (by norm_num) (by norm_num)

def e1661 : ℝ := e23 * e1512
lemma b1661 : Encl e1661 (3481 / 1250 : ℝ) (3481 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b1512 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1662 : ℝ := e1661 * e1518
lemma b1662 : Encl e1662 (2089756966201 / 1000000000000 : ℝ) (32652452597 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b1661 b1518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1663 : ℝ := e0 + e1662
lemma b1663 : Encl e1663 (523134961979 / 100000000000 : ℝ) (2615674809899 / 500000000000 : ℝ) := by
  exact Encl.add b0 b1662 (by norm_num) (by norm_num)

def e1664 : ℝ := Real.sqrt e1663
lemma b1664 : Encl e1664 (71475449373 / 31250000000 : ℝ) (2287214379939 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1663 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1665 : ℝ := e932 * e1664
lemma b1665 : Encl e1665 (1456085897909 / 1000000000000 : ℝ) (728042948957 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1664 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1666 : ℝ := e1507 ^ 3
lemma b1666 : Encl e1666 (205379 / 125000 : ℝ) (205379 / 125000 : ℝ) := by
  exact Encl.pow b1507 (by norm_num) 3 (by norm_num) (by norm_num)

def e1667 : ℝ := e939 * e1666
lemma b1667 : Encl e1667 (13760393 / 62500000 : ℝ) (13760393 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1666 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1668 : ℝ := min e1667 e941
lemma b1668 : Encl e1668 (13760393 / 62500000 : ℝ) (13760393 / 62500000 : ℝ) := by
  exact Encl.min b1667 b941 (by norm_num) (by norm_num)

def e1669 : ℝ := e23 * e1660
lemma b1669 : Encl e1669 (49082141757 / 100000000000 : ℝ) (61352677197 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1660 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1670 : ℝ := e944 * e1668
lemma b1670 : Encl e1670 (41281179 / 31250000 : ℝ) (41281179 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1668 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1671 : ℝ := e1665 ^ 2
lemma b1671 : Encl e1671 (2120186142089 / 1000000000000 : ℝ) (424037228421 / 200000000000 : ℝ) := by
  exact Encl.pow b1665 (by norm_num) 2 (by norm_num) (by norm_num)

def e1672 : ℝ := e1670 * e1671
lemma b1672 : Encl e1672 (700190269159 / 250000000000 : ℝ) (1400380538329 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1670 b1671 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1673 : ℝ := e1672 * e1660
lemma b1673 : Encl e1673 (343668380477 / 500000000000 : ℝ) (687336760969 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1672 b1660 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1674 : ℝ := e1673 / e9
lemma b1674 : Encl e1674 (306846768283 / 125000000000 : ℝ) (1227387073159 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1673 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1675 : ℝ := e5 + e1674
lemma b1675 : Encl e1675 (431846768283 / 125000000000 : ℝ) (1727387073159 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1674 (by norm_num) (by norm_num)

def e1676 : ℝ := Real.sqrt e1675
lemma b1676 : Encl e1676 (1858702274777 / 1000000000000 : ℝ) (1858702274793 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1675 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1677 : ℝ := e5 + e1676
lemma b1677 : Encl e1677 (2858702274777 / 1000000000000 : ℝ) (2858702274793 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1676 (by norm_num) (by norm_num)

def e1678 : ℝ := e1669 / e1677
lemma b1678 : Encl e1678 (171693786337 / 1000000000000 : ℝ) (171693786341 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1669 b1677 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1679 : ℝ := e1668 * e954
lemma b1679 : Encl e1679 (2038959993 / 1000000000000 : ℝ) (1019479997 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1668 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1680 : ℝ := e1660 - e1678
lemma b1680 : Encl e1680 (18429230611 / 250000000000 : ℝ) (73716922451 / 1000000000000 : ℝ) := by
  exact Encl.sub b1660 b1678 (by norm_num) (by norm_num)

def e1681 : ℝ := e1680 / e1665
lemma b1681 : Encl e1681 (25313383829 / 500000000000 : ℝ) (3164172979 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b1680 b1665 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1682 : ℝ := e1681 ^ 2
lemma b1682 : Encl e1682 (2563069603 / 1000000000000 : ℝ) (512613921 / 200000000000 : ℝ) := by
  exact Encl.pow b1681 (by norm_num) 2 (by norm_num) (by norm_num)

def e1683 : ℝ := e9 * e1682
lemma b1683 : Encl e1683 (22426859 / 31250000000 : ℝ) (71765949 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1682 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1684 : ℝ := e1678 ^ 3
lemma b1684 : Encl e1684 (5061319279 / 1000000000000 : ℝ) (5061319281 / 1000000000000 : ℝ) := by
  exact Encl.pow b1678 (by norm_num) 3 (by norm_num) (by norm_num)

def e1685 : ℝ := e1668 * e1684
lemma b1685 : Encl e1685 (557165939 / 500000000000 : ℝ) (1114331879 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1668 b1684 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1686 : ℝ := e1683 + e1685
lemma b1686 : Encl e1686 (915995683 / 500000000000 : ℝ) (1831991369 / 1000000000000 : ℝ) := by
  exact Encl.add b1683 b1685 (by norm_num) (by norm_num)

def e1687 : ℝ := min e1679 e1686
lemma b1687 : Encl e1687 (915995683 / 500000000000 : ℝ) (1831991369 / 1000000000000 : ℝ) := by
  exact Encl.min b1679 b1686 (by norm_num) (by norm_num)

def e1688 : ℝ := (61 / 50 : ℝ)
lemma b1688 : Encl e1688 (61 / 50 : ℝ) (61 / 50 : ℝ) := by
  exact Encl.exact (61 / 50 : ℝ)

def e1689 : ℝ := e1688 / e0
lemma b1689 : Encl e1689 (48542257643 / 125000000000 : ℝ) (77667612229 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b1688 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1690 : ℝ := e1688 * e7
lemma b1690 : Encl e1690 (166332387771 / 200000000000 : ℝ) (831661938857 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1688 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1691 : ℝ := e8 * e1688
lemma b1691 : Encl e1691 (2989 / 2500 : ℝ) (2989 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1692 : ℝ := e1691 / e0
lemma b1692 : Encl e1692 (380571299921 / 1000000000000 : ℝ) (190285649961 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1691 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1693 : ℝ := e1688 ^ 2
lemma b1693 : Encl e1693 (3721 / 2500 : ℝ) (3721 / 2500 : ℝ) := by
  exact Encl.pow b1688 (by norm_num) 2 (by norm_num) (by norm_num)

def e1694 : ℝ := e17 * e1693
lemma b1694 : Encl e1694 (3721 / 625 : ℝ) (3721 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b1693 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1695 : ℝ := e1694 / e0
lemma b1695 : Encl e1695 (1895089738383 / 1000000000000 : ℝ) (118443108649 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b1694 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1696 : ℝ := e5 + e1695
lemma b1696 : Encl e1696 (2895089738383 / 1000000000000 : ℝ) (180943108649 / 62500000000 : ℝ) := by
  exact Encl.add b5 b1695 (by norm_num) (by norm_num)

def e1697 : ℝ := Real.sqrt e1696
lemma b1697 : Encl e1697 (212687040419 / 125000000000 : ℝ) (850748161677 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1696 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1698 : ℝ := e5 + e1697
lemma b1698 : Encl e1698 (337687040419 / 125000000000 : ℝ) (1350748161677 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1697 (by norm_num) (by norm_num)

def e1699 : ℝ := e23 / e1698
lemma b1699 : Encl e1699 (740330454167 / 1000000000000 : ℝ) (92541306771 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1698 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1700 : ℝ := e9 * e1699
lemma b1700 : Encl e1700 (103646263583 / 500000000000 : ℝ) (3238945737 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1699 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1701 : ℝ := e1692 + e1700
lemma b1701 : Encl e1701 (587863827087 / 1000000000000 : ℝ) (58786382709 / 100000000000 : ℝ) := by
  exact Encl.add b1692 b1700 (by norm_num) (by norm_num)

def e1702 : ℝ := e1701 - e5
lemma b1702 : Encl e1702 (-412136172913 / 1000000000000 : ℝ) (-41213617291 / 100000000000 : ℝ) := by
  exact Encl.sub b1701 b5 (by norm_num) (by norm_num)

def e1703 : ℝ := e0 / e1693
lemma b1703 : Encl e1703 (263839748521 / 125000000000 : ℝ) (2110717988169 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1693 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1704 : ℝ := e1689 ^ 2
lemma b1704 : Encl e1704 (150806449733 / 1000000000000 : ℝ) (75403224867 / 500000000000 : ℝ) := by
  exact Encl.pow b1689 (by norm_num) 2 (by norm_num) (by norm_num)

def e1705 : ℝ := e5 - e1704
lemma b1705 : Encl e1705 (424596775133 / 500000000000 : ℝ) (849193550267 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1704 (by norm_num) (by norm_num)

def e1706 : ℝ := Real.sqrt e1705
lemma b1706 : Encl e1706 (921516983167 / 1000000000000 : ℝ) (7199351431 / 7812500000 : ℝ) := by
  exact Encl.sqrt b1705 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1707 : ℝ := e29 - e1706
lemma b1707 : Encl e1707 (-127425158251 / 500000000000 : ℝ) (-509700633 / 2000000000 : ℝ) := by
  exact Encl.sub b29 b1706 (by norm_num) (by norm_num)

def e1708 : ℝ := e1706 ^ 3
lemma b1708 : Encl e1708 (156509255713 / 200000000000 : ℝ) (97818284821 / 125000000000 : ℝ) := by
  exact Encl.pow b1706 (by norm_num) 3 (by norm_num) (by norm_num)

def e1709 : ℝ := e1708 / e35
lemma b1709 : Encl e1709 (260848759521 / 1000000000000 : ℝ) (260848759523 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1708 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1710 : ℝ := e1707 + e1709
lemma b1710 : Encl e1710 (5998443019 / 1000000000000 : ℝ) (5998443023 / 1000000000000 : ℝ) := by
  exact Encl.add b1707 b1709 (by norm_num) (by norm_num)

def e1711 : ℝ := e8 * e1710
lemma b1711 : Encl e1711 (2939237079 / 500000000000 : ℝ) (5878474163 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1710 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1712 : ℝ := e1704 / e1706
lemma b1712 : Encl e1712 (81825106041 / 500000000000 : ℝ) (40912553021 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1704 b1706 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1713 : ℝ := e1712 - e23
lemma b1713 : Encl e1713 (-918174893959 / 500000000000 : ℝ) (-459087446979 / 250000000000 : ℝ) := by
  exact Encl.sub b1712 b23 (by norm_num) (by norm_num)

def e1714 : ℝ := e23 * e1706
lemma b1714 : Encl e1714 (921516983167 / 500000000000 : ℝ) (7199351431 / 3906250000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1706 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1715 : ℝ := e1713 + e1714
lemma b1715 : Encl e1715 (417761151 / 62500000000 : ℝ) (334208921 / 50000000000 : ℝ) := by
  exact Encl.add b1713 b1714 (by norm_num) (by norm_num)

def e1716 : ℝ := e1715 / e43
lemma b1716 : Encl e1716 (8355223 / 62500000000 : ℝ) (133683569 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1715 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1717 : ℝ := e1711 - e1716
lemma b1717 : Encl e1717 (5744790589 / 1000000000000 : ℝ) (1148958119 / 200000000000 : ℝ) := by
  exact Encl.sub b1711 b1716 (by norm_num) (by norm_num)

def e1718 : ℝ := e1703 * e1717
lemma b1718 : Encl e1718 (6062816417 / 500000000000 : ℝ) (757852053 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b1703 b1717 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1719 : ℝ := e1702 + e1718
lemma b1719 : Encl e1719 (-400010540079 / 1000000000000 : ℝ) (-200005270031 / 500000000000 : ℝ) := by
  exact Encl.add b1702 b1718 (by norm_num) (by norm_num)

def e1720 : ℝ := e1690 ^ 2
lemma b1720 : Encl e1720 (34583079027 / 50000000000 : ℝ) (2701803049 / 3906250000 : ℝ) := by
  exact Encl.pow b1690 (by norm_num) 2 (by norm_num) (by norm_num)

def e1721 : ℝ := e5 - e1720
lemma b1721 : Encl e1721 (1204446951 / 3906250000 : ℝ) (15416920973 / 50000000000 : ℝ) := by
  exact Encl.sub b5 b1720 (by norm_num) (by norm_num)

def e1722 : ℝ := Real.sqrt e1721
lemma b1722 : Encl e1722 (6941028601 / 12500000000 : ℝ) (111056457617 / 200000000000 : ℝ) := by
  exact Encl.sqrt b1721 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1723 : ℝ := e5 + e1722
lemma b1723 : Encl e1723 (19441028601 / 12500000000 : ℝ) (311056457617 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1722 (by norm_num) (by norm_num)

def e1724 : ℝ := e1690 / e1723
lemma b1724 : Encl e1724 (267366877777 / 500000000000 : ℝ) (267366877779 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1690 b1723 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1725 : ℝ := e1724 ^ 2
lemma b1725 : Encl e1725 (17871261833 / 62500000000 : ℝ) (142970094667 / 500000000000 : ℝ) := by
  exact Encl.pow b1724 (by norm_num) 2 (by norm_num) (by norm_num)

def e1726 : ℝ := e5 + e1725
lemma b1726 : Encl e1726 (80371261833 / 62500000000 : ℝ) (642970094667 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1725 (by norm_num) (by norm_num)

def e1727 : ℝ := Real.sqrt e1726
lemma b1727 : Encl e1727 (566996514391 / 500000000000 : ℝ) (566996514393 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1726 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1728 : ℝ := e5 + e1727
lemma b1728 : Encl e1728 (1066996514391 / 500000000000 : ℝ) (1066996514393 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1727 (by norm_num) (by norm_num)

def e1729 : ℝ := e1724 / e1728
lemma b1729 : Encl e1729 (250578960821 / 1000000000000 : ℝ) (10023158433 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b1724 b1728 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1730 : ℝ := Real.arcsin e1690
lemma b1730 : Encl e1730 (982093972619 / 1000000000000 : ℝ) (245523493159 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e1690) (a := (250578960821 / 1000000000000 : ℝ)) (b := (10023158433 / 40000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (166332387771 / 200000000000 : ℝ) by norm_num).trans b1690.1
        exact b1690.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1690) (250578960821 / 1000000000000 : ℝ) (10023158433 / 40000000000 : ℝ) from b1729) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1731 : ℝ := e59 * e1730
lemma b1731 : Encl e1731 (100173585207 / 200000000000 : ℝ) (100173585209 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1730 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1732 : ℝ := e61 * e1690
lemma b1732 : Encl e1732 (203757175019 / 500000000000 : ℝ) (10187858751 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1690 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1733 : ℝ := e1732 * e1722
lemma b1733 : Encl e1733 (113142750357 / 500000000000 : ℝ) (113142750359 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1732 b1722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1734 : ℝ := e1731 - e1733
lemma b1734 : Encl e1734 (274582425317 / 1000000000000 : ℝ) (274582425331 / 1000000000000 : ℝ) := by
  exact Encl.sub b1731 b1733 (by norm_num) (by norm_num)

def e1735 : ℝ := e43 * e1722
lemma b1735 : Encl e1735 (6941028601 / 250000000 : ℝ) (111056457617 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1736 : ℝ := e1690 / e1735
lemma b1736 : Encl e1736 (29954563893 / 1000000000000 : ℝ) (14977281947 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1690 b1735 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1737 : ℝ := e1734 - e1736
lemma b1737 : Encl e1737 (244627861423 / 1000000000000 : ℝ) (122313930719 / 500000000000 : ℝ) := by
  exact Encl.sub b1734 b1736 (by norm_num) (by norm_num)

def e1738 : ℝ := e5 + e1706
lemma b1738 : Encl e1738 (1921516983167 / 1000000000000 : ℝ) (15011851431 / 7812500000 : ℝ) := by
  exact Encl.add b5 b1706 (by norm_num) (by norm_num)

def e1739 : ℝ := e1689 / e1738
lemma b1739 : Encl e1739 (202099728779 / 1000000000000 : ℝ) (202099728781 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1689 b1738 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1740 : ℝ := e1739 ^ 2
lemma b1740 : Encl e1740 (10211075093 / 250000000000 : ℝ) (20422150187 / 500000000000 : ℝ) := by
  exact Encl.pow b1739 (by norm_num) 2 (by norm_num) (by norm_num)

def e1741 : ℝ := e5 + e1740
lemma b1741 : Encl e1741 (260211075093 / 250000000000 : ℝ) (520422150187 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1740 (by norm_num) (by norm_num)

def e1742 : ℝ := Real.sqrt e1741
lemma b1742 : Encl e1742 (255054442763 / 250000000000 : ℝ) (510108885527 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1741 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1743 : ℝ := e5 + e1742
lemma b1743 : Encl e1743 (505054442763 / 250000000000 : ℝ) (1010108885527 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1742 (by norm_num) (by norm_num)

def e1744 : ℝ := e1739 / e1743
lemma b1744 : Encl e1744 (100038585777 / 1000000000000 : ℝ) (100038585779 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1739 b1743 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1745 : ℝ := Real.arcsin e1689
lemma b1745 : Encl e1745 (398827424339 / 1000000000000 : ℝ) (99706856087 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e1689) (a := (100038585777 / 1000000000000 : ℝ)) (b := (100038585779 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (48542257643 / 125000000000 : ℝ) by norm_num).trans b1689.1
        exact b1689.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1689) (100038585777 / 1000000000000 : ℝ) (100038585779 / 1000000000000 : ℝ) from b1744) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1746 : ℝ := e59 * e1745
lemma b1746 : Encl e1746 (50850496603 / 250000000000 : ℝ) (101700993209 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1745 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1747 : ℝ := e61 * e1689
lemma b1747 : Encl e1747 (4757141249 / 25000000000 : ℝ) (95142824981 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1689 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1748 : ℝ := e1747 * e1706
lemma b1748 : Encl e1748 (175351458091 / 1000000000000 : ℝ) (87675729047 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1747 b1706 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1749 : ℝ := e1746 - e1748
lemma b1749 : Encl e1749 (14025264159 / 500000000000 : ℝ) (28050528327 / 1000000000000 : ℝ) := by
  exact Encl.sub b1746 b1748 (by norm_num) (by norm_num)

def e1750 : ℝ := e43 * e1706
lemma b1750 : Encl e1750 (921516983167 / 20000000000 : ℝ) (7199351431 / 156250000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1706 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1751 : ℝ := e1689 / e1750
lemma b1751 : Encl e1751 (2107058623 / 250000000000 : ℝ) (8428234493 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1689 b1750 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1752 : ℝ := e1749 - e1751
lemma b1752 : Encl e1752 (784891753 / 40000000000 : ℝ) (3924458767 / 200000000000 : ℝ) := by
  exact Encl.sub b1749 b1751 (by norm_num) (by norm_num)

def e1753 : ℝ := e1737 - e1752
lemma b1753 : Encl e1753 (56251391897 / 250000000000 : ℝ) (225005567613 / 1000000000000 : ℝ) := by
  exact Encl.sub b1737 b1752 (by norm_num) (by norm_num)

def e1754 : ℝ := e1753 / e1688
lemma b1754 : Encl e1754 (11526924569 / 62500000000 : ℝ) (92215396563 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1753 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1755 : ℝ := e1719 + e1754
lemma b1755 : Encl e1755 (-8623189879 / 40000000000 : ℝ) (-26947468367 / 125000000000 : ℝ) := by
  exact Encl.add b1719 b1754 (by norm_num) (by norm_num)

def e1756 : ℝ := e1690 + e4
lemma b1756 : Encl e1756 (364281051493 / 200000000000 : ℝ) (455351314367 / 250000000000 : ℝ) := by
  exact Encl.add b1690 b4 (by norm_num) (by norm_num)

def e1757 : ℝ := e1756 / e23
lemma b1757 : Encl e1757 (227675657183 / 250000000000 : ℝ) (455351314367 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1756 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1758 : ℝ := e1690 / e1688
lemma b1758 : Encl e1758 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1690 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1759 : ℝ := e89 * e1758
lemma b1759 : Encl e1759 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1758 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1760 : ℝ := e1758 ^ 2
lemma b1760 : Encl e1760 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1758 (by norm_num) 2 (by norm_num) (by norm_num)

def e1761 : ℝ := e91 * e1760
lemma b1761 : Encl e1761 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1760 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1762 : ℝ := e5 + e1761
lemma b1762 : Encl e1762 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1761 (by norm_num) (by norm_num)

def e1763 : ℝ := Real.sqrt e1762
lemma b1763 : Encl e1763 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1762 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1764 : ℝ := e1759 * e1763
lemma b1764 : Encl e1764 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1759 b1763 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1765 : ℝ := e97 * e1760
lemma b1765 : Encl e1765 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1760 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1766 : ℝ := e1764 - e1765
lemma b1766 : Encl e1766 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1764 b1765 (by norm_num) (by norm_num)

def e1767 : ℝ := e1757 * e1766
lemma b1767 : Encl e1767 (310408489311 / 500000000000 : ℝ) (310408489323 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1757 b1766 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1768 : ℝ := e1757 / e1688
lemma b1768 : Encl e1768 (373238782267 / 500000000000 : ℝ) (746477564537 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1757 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1769 : ℝ := e89 * e1768
lemma b1769 : Encl e1769 (82693564617 / 62500000000 : ℝ) (1323097033879 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1768 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1770 : ℝ := e1768 ^ 2
lemma b1770 : Encl e1770 (34826797147 / 62500000000 : ℝ) (278614377179 / 500000000000 : ℝ) := by
  exact Encl.pow b1768 (by norm_num) 2 (by norm_num) (by norm_num)

def e1771 : ℝ := e91 * e1770
lemma b1771 : Encl e1771 (21882322013 / 50000000000 : ℝ) (218823220133 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1770 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1772 : ℝ := e5 + e1771
lemma b1772 : Encl e1772 (71882322013 / 50000000000 : ℝ) (718823220133 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1771 (by norm_num) (by norm_num)

def e1773 : ℝ := Real.sqrt e1772
lemma b1773 : Encl e1773 (599509474541 / 500000000000 : ℝ) (599509474543 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1772 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1774 : ℝ := e1769 * e1773
lemma b1774 : Encl e1774 (793209207543 / 500000000000 : ℝ) (1586418415101 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1769 b1773 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1775 : ℝ := e97 * e1770
lemma b1775 : Encl e1775 (21882322013 / 25000000000 : ℝ) (875292880531 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1770 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1776 : ℝ := e1774 - e1775
lemma b1776 : Encl e1776 (142225106911 / 200000000000 : ℝ) (711125534581 / 1000000000000 : ℝ) := by
  exact Encl.sub b1774 b1775 (by norm_num) (by norm_num)

def e1777 : ℝ := e1690 * e1776
lemma b1777 : Encl e1777 (591416040837 / 1000000000000 : ℝ) (591416040861 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1690 b1776 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1778 : ℝ := e1767 - e1777
lemma b1778 : Encl e1778 (29400937761 / 1000000000000 : ℝ) (29400937809 / 1000000000000 : ℝ) := by
  exact Encl.sub b1767 b1777 (by norm_num) (by norm_num)

def e1779 : ℝ := e1757 ^ 2
lemma b1779 : Encl e1779 (829379277979 / 1000000000000 : ℝ) (25918102437 / 31250000000 : ℝ) := by
  exact Encl.pow b1757 (by norm_num) 2 (by norm_num) (by norm_num)

def e1780 : ℝ := e8 * e1779
lemma b1780 : Encl e1780 (812791692419 / 1000000000000 : ℝ) (32511667697 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1779 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1781 : ℝ := e5 - e1780
lemma b1781 : Encl e1781 (7488332303 / 40000000000 : ℝ) (187208307581 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1780 (by norm_num) (by norm_num)

def e1782 : ℝ := e5 - e1779
lemma b1782 : Encl e1782 (5331897563 / 31250000000 : ℝ) (170620722021 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1779 (by norm_num) (by norm_num)

def e1783 : ℝ := Real.sqrt e1782
lemma b1783 : Encl e1783 (206531306353 / 500000000000 : ℝ) (413062612713 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1782 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1784 : ℝ := e1781 / e1783
lemma b1784 : Encl e1784 (453220170049 / 1000000000000 : ℝ) (453220170073 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1781 b1783 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1785 : ℝ := e5 - e1784
lemma b1785 : Encl e1785 (546779829927 / 1000000000000 : ℝ) (546779829951 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1784 (by norm_num) (by norm_num)

def e1786 : ℝ := e8 * e1720
lemma b1786 : Encl e1786 (677828348929 / 1000000000000 : ℝ) (338914174467 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1720 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1787 : ℝ := e5 - e1786
lemma b1787 : Encl e1787 (161085825533 / 500000000000 : ℝ) (322171651071 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1786 (by norm_num) (by norm_num)

def e1788 : ℝ := e1787 / e1722
lemma b1788 : Encl e1788 (580194358759 / 1000000000000 : ℝ) (290097179387 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1787 b1722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1789 : ℝ := e5 - e1788
lemma b1789 : Encl e1789 (209902820613 / 500000000000 : ℝ) (419805641241 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1788 (by norm_num) (by norm_num)

def e1790 : ℝ := e1785 - e1789
lemma b1790 : Encl e1790 (63487094343 / 500000000000 : ℝ) (5078967549 / 40000000000 : ℝ) := by
  exact Encl.sub b1785 b1789 (by norm_num) (by norm_num)

def e1791 : ℝ := e1778 * e1790
lemma b1791 : Encl e1791 (1866580109 / 500000000000 : ℝ) (3733160227 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1778 b1790 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1792 : ℝ := e1776 - e1766
lemma b1792 : Encl e1792 (29435420727 / 1000000000000 : ℝ) (3679427597 / 125000000000 : ℝ) := by
  exact Encl.sub b1776 b1766 (by norm_num) (by norm_num)

def e1793 : ℝ := e5 + e1783
lemma b1793 : Encl e1793 (706531306353 / 500000000000 : ℝ) (1413062612713 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1783 (by norm_num) (by norm_num)

def e1794 : ℝ := e1757 / e1793
lemma b1794 : Encl e1794 (644488517733 / 1000000000000 : ℝ) (644488517739 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1757 b1793 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1795 : ℝ := e1794 ^ 2
lemma b1795 : Encl e1795 (415365449489 / 1000000000000 : ℝ) (207682724749 / 500000000000 : ℝ) := by
  exact Encl.pow b1794 (by norm_num) 2 (by norm_num) (by norm_num)

def e1796 : ℝ := e5 + e1795
lemma b1796 : Encl e1796 (1415365449489 / 1000000000000 : ℝ) (707682724749 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1795 (by norm_num) (by norm_num)

def e1797 : ℝ := Real.sqrt e1796
lemma b1797 : Encl e1797 (1189691325297 / 1000000000000 : ℝ) (594845662651 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1796 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1798 : ℝ := e5 + e1797
lemma b1798 : Encl e1798 (2189691325297 / 1000000000000 : ℝ) (1094845662651 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1797 (by norm_num) (by norm_num)

def e1799 : ℝ := e1794 / e1798
lemma b1799 : Encl e1799 (147164239609 / 500000000000 : ℝ) (147164239611 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1794 b1798 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1800 : ℝ := Real.arcsin e1757
lemma b1800 : Encl e1800 (1144981907199 / 1000000000000 : ℝ) (71561369201 / 62500000000 : ℝ) := by
  apply Encl.arcsin (z := e1757) (a := (147164239609 / 500000000000 : ℝ)) (b := (147164239611 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (227675657183 / 250000000000 : ℝ) by norm_num).trans b1757.1
        exact b1757.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1757) (147164239609 / 500000000000 : ℝ) (147164239611 / 500000000000 : ℝ) from b1799) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1801 : ℝ := e59 * e1800
lemma b1801 : Encl e1801 (583940772671 / 1000000000000 : ℝ) (583940772681 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1800 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1802 : ℝ := e61 * e1757
lemma b1802 : Encl e1802 (223122144039 / 500000000000 : ℝ) (5578053601 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1757 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1803 : ℝ := e1802 * e1783
lemma b1803 : Encl e1803 (92163415769 / 500000000000 : ℝ) (184326831543 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1802 b1783 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1804 : ℝ := e1801 - e1803
lemma b1804 : Encl e1804 (49951742641 / 125000000000 : ℝ) (399613941143 / 1000000000000 : ℝ) := by
  exact Encl.sub b1801 b1803 (by norm_num) (by norm_num)

def e1805 : ℝ := e43 * e1783
lemma b1805 : Encl e1805 (206531306353 / 10000000000 : ℝ) (413062612713 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1783 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1806 : ℝ := e1757 / e1805
lemma b1806 : Encl e1806 (44095137187 / 1000000000000 : ℝ) (44095137189 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1757 b1805 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1807 : ℝ := e1804 - e1806
lemma b1807 : Encl e1807 (355518803939 / 1000000000000 : ℝ) (88879700989 / 250000000000 : ℝ) := by
  exact Encl.sub b1804 b1806 (by norm_num) (by norm_num)

def e1808 : ℝ := e1807 - e1737
lemma b1808 : Encl e1808 (110890942501 / 1000000000000 : ℝ) (110890942533 / 1000000000000 : ℝ) := by
  exact Encl.sub b1807 b1737 (by norm_num) (by norm_num)

def e1809 : ℝ := e1792 * e1808
lemma b1809 : Encl e1809 (3264121547 / 1000000000000 : ℝ) (1632060777 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1792 b1808 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1810 : ℝ := e1791 + e1809
lemma b1810 : Encl e1810 (1399456353 / 200000000000 : ℝ) (6997281781 / 1000000000000 : ℝ) := by
  exact Encl.add b1791 b1809 (by norm_num) (by norm_num)

def e1811 : ℝ := e1757 - e1690
lemma b1811 : Encl e1811 (632325519 / 8000000000 : ℝ) (79040689879 / 1000000000000 : ℝ) := by
  exact Encl.sub b1757 b1690 (by norm_num) (by norm_num)

def e1812 : ℝ := e1810 / e1811
lemma b1812 : Encl e1812 (44263794861 / 500000000000 : ℝ) (8852758993 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1810 b1811 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1813 : ℝ := e1755 + e1812
lemma b1813 : Encl e1813 (-127052157253 / 1000000000000 : ℝ) (-63526078503 / 500000000000 : ℝ) := by
  exact Encl.add b1755 b1812 (by norm_num) (by norm_num)

def e1814 : ℝ := e4 * e1776
lemma b1814 : Encl e1814 (351915873259 / 500000000000 : ℝ) (351915873273 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1776 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1815 : ℝ := e4 / e1688
lemma b1815 : Encl e1815 (405632507627 / 500000000000 : ℝ) (162253003051 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1816 : ℝ := e89 * e1815
lemma b1816 : Encl e1816 (1437929800391 / 1000000000000 : ℝ) (287585960079 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1815 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1817 : ℝ := e1815 ^ 2
lemma b1817 : Encl e1817 (26326036999 / 40000000000 : ℝ) (658150924977 / 1000000000000 : ℝ) := by
  exact Encl.pow b1815 (by norm_num) 2 (by norm_num) (by norm_num)

def e1818 : ℝ := e91 * e1817
lemma b1818 : Encl e1818 (516910527713 / 1000000000000 : ℝ) (129227631929 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1817 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1819 : ℝ := e5 + e1818
lemma b1819 : Encl e1819 (1516910527713 / 1000000000000 : ℝ) (379227631929 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1818 (by norm_num) (by norm_num)

def e1820 : ℝ := Real.sqrt e1819
lemma b1820 : Encl e1820 (246325843363 / 200000000000 : ℝ) (1231629216817 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1819 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1821 : ℝ := e1816 * e1820

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
