import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block17
import OAI.Analysis.MutuallyUnbiased.GramRows.Block35
import OAI.Analysis.MutuallyUnbiased.GramRows.Block36
import OAI.Analysis.MutuallyUnbiased.GramRows.Block37

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows9_0 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1476, row1477, row1478, row1479, row1480, row1481, row1482, row1483, row1484, row1485, row1486, row1487, row642, row643, row644, row645, row646, row647, row1488, row1489, row1490, row1491, row1492, row1493, row654, row655, row656, row657, row658, row659]

theorem entryCheck9_0 : entry9_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_0 k)) := by decide +kernel

theorem rowsSound9_0 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1476 x
  · exact rowEval1477 x
  · exact rowEval1478 x
  · exact rowEval1479 x
  · exact rowEval1480 x
  · exact rowEval1481 x
  · exact rowEval1482 x
  · exact rowEval1483 x
  · exact rowEval1484 x
  · exact rowEval1485 x
  · exact rowEval1486 x
  · exact rowEval1487 x
  · exact rowEval642 x
  · exact rowEval643 x
  · exact rowEval644 x
  · exact rowEval645 x
  · exact rowEval646 x
  · exact rowEval647 x
  · exact rowEval1488 x
  · exact rowEval1489 x
  · exact rowEval1490 x
  · exact rowEval1491 x
  · exact rowEval1492 x
  · exact rowEval1493 x
  · exact rowEval654 x
  · exact rowEval655 x
  · exact rowEval656 x
  · exact rowEval657 x
  · exact rowEval658 x
  · exact rowEval659 x

theorem entryEval9_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_0 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck9_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_0]

def rows9_1 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1494, row1495, row1496, row1497, row1498, row1499, row1500, row1501, row1502, row1503, row1504, row1505, row1506, row1507, row1508, row1509, row1510, row1511, row1512, row1513, row1514, row1515, row1516, row1517, row1518, row1519, row1520, row1521, row1522, row1523]

theorem entryCheck9_1 : entry9_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_1 k)) := by decide +kernel

theorem rowsSound9_1 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1494 x
  · exact rowEval1495 x
  · exact rowEval1496 x
  · exact rowEval1497 x
  · exact rowEval1498 x
  · exact rowEval1499 x
  · exact rowEval1500 x
  · exact rowEval1501 x
  · exact rowEval1502 x
  · exact rowEval1503 x
  · exact rowEval1504 x
  · exact rowEval1505 x
  · exact rowEval1506 x
  · exact rowEval1507 x
  · exact rowEval1508 x
  · exact rowEval1509 x
  · exact rowEval1510 x
  · exact rowEval1511 x
  · exact rowEval1512 x
  · exact rowEval1513 x
  · exact rowEval1514 x
  · exact rowEval1515 x
  · exact rowEval1516 x
  · exact rowEval1517 x
  · exact rowEval1518 x
  · exact rowEval1519 x
  · exact rowEval1520 x
  · exact rowEval1521 x
  · exact rowEval1522 x
  · exact rowEval1523 x

theorem entryEval9_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_1 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck9_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_1]

def rows9_2 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1524, row1525, row1526, row1527, row1528, row1529, row1530, row1531, row1532, row1533, row1534, row1535, row1536, row1537, row1538, row1539, row1540, row1541, row1542, row1543, row1544, row1545, row1546, row1547, row1548, row1549, row1550, row1551, row1552, row1553]

theorem entryCheck9_2 : entry9_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_2 k)) := by decide +kernel

theorem rowsSound9_2 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1524 x
  · exact rowEval1525 x
  · exact rowEval1526 x
  · exact rowEval1527 x
  · exact rowEval1528 x
  · exact rowEval1529 x
  · exact rowEval1530 x
  · exact rowEval1531 x
  · exact rowEval1532 x
  · exact rowEval1533 x
  · exact rowEval1534 x
  · exact rowEval1535 x
  · exact rowEval1536 x
  · exact rowEval1537 x
  · exact rowEval1538 x
  · exact rowEval1539 x
  · exact rowEval1540 x
  · exact rowEval1541 x
  · exact rowEval1542 x
  · exact rowEval1543 x
  · exact rowEval1544 x
  · exact rowEval1545 x
  · exact rowEval1546 x
  · exact rowEval1547 x
  · exact rowEval1548 x
  · exact rowEval1549 x
  · exact rowEval1550 x
  · exact rowEval1551 x
  · exact rowEval1552 x
  · exact rowEval1553 x

theorem entryEval9_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_2 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck9_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_2]

def rows9_3 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1554, row1555, row1556, row1557, row1558, row1559, row1560, row1561, row1562, row1563, row1564, row1565, row1566, row1567, row1568, row1569, row1570, row1571, row1572, row1573, row1574, row1575, row1576, row1577, row1578, row1579, row1580, row1581, row1582, row1583]

theorem entryCheck9_3 : entry9_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_3 k)) := by decide +kernel

theorem rowsSound9_3 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1554 x
  · exact rowEval1555 x
  · exact rowEval1556 x
  · exact rowEval1557 x
  · exact rowEval1558 x
  · exact rowEval1559 x
  · exact rowEval1560 x
  · exact rowEval1561 x
  · exact rowEval1562 x
  · exact rowEval1563 x
  · exact rowEval1564 x
  · exact rowEval1565 x
  · exact rowEval1566 x
  · exact rowEval1567 x
  · exact rowEval1568 x
  · exact rowEval1569 x
  · exact rowEval1570 x
  · exact rowEval1571 x
  · exact rowEval1572 x
  · exact rowEval1573 x
  · exact rowEval1574 x
  · exact rowEval1575 x
  · exact rowEval1576 x
  · exact rowEval1577 x
  · exact rowEval1578 x
  · exact rowEval1579 x
  · exact rowEval1580 x
  · exact rowEval1581 x
  · exact rowEval1582 x
  · exact rowEval1583 x

theorem entryEval9_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_3 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck9_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_3]

def rows9_4 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1584, row1585, row1586, row1587, row1588, row1589, row1590, row1591, row1592, row1593, row1594, row1595, row1596, row1597, row1598, row1599, row1600, row1601, row1602, row1603, row1604, row1605, row1606, row1607, row1608, row1609, row1610, row1611, row1612, row1613]

theorem entryCheck9_4 : entry9_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_4 k)) := by decide +kernel

theorem rowsSound9_4 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1584 x
  · exact rowEval1585 x
  · exact rowEval1586 x
  · exact rowEval1587 x
  · exact rowEval1588 x
  · exact rowEval1589 x
  · exact rowEval1590 x
  · exact rowEval1591 x
  · exact rowEval1592 x
  · exact rowEval1593 x
  · exact rowEval1594 x
  · exact rowEval1595 x
  · exact rowEval1596 x
  · exact rowEval1597 x
  · exact rowEval1598 x
  · exact rowEval1599 x
  · exact rowEval1600 x
  · exact rowEval1601 x
  · exact rowEval1602 x
  · exact rowEval1603 x
  · exact rowEval1604 x
  · exact rowEval1605 x
  · exact rowEval1606 x
  · exact rowEval1607 x
  · exact rowEval1608 x
  · exact rowEval1609 x
  · exact rowEval1610 x
  · exact rowEval1611 x
  · exact rowEval1612 x
  · exact rowEval1613 x

theorem entryEval9_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_4 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck9_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_4]

def rows9_5 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1614, row1615, row1616, row1617, row1618, row1619, row1620, row1621, row1622, row1623, row1624, row1625, row1626, row1627, row1628, row1629, row1630, row1631, row1632, row1633, row1634, row1635, row1636, row1637, row1638, row1639, row1640, row1641, row1642, row1643]

theorem entryCheck9_5 : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

theorem rowsSound9_5 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1614 x
  · exact rowEval1615 x
  · exact rowEval1616 x
  · exact rowEval1617 x
  · exact rowEval1618 x
  · exact rowEval1619 x
  · exact rowEval1620 x
  · exact rowEval1621 x
  · exact rowEval1622 x
  · exact rowEval1623 x
  · exact rowEval1624 x
  · exact rowEval1625 x
  · exact rowEval1626 x
  · exact rowEval1627 x
  · exact rowEval1628 x
  · exact rowEval1629 x
  · exact rowEval1630 x
  · exact rowEval1631 x
  · exact rowEval1632 x
  · exact rowEval1633 x
  · exact rowEval1634 x
  · exact rowEval1635 x
  · exact rowEval1636 x
  · exact rowEval1637 x
  · exact rowEval1638 x
  · exact rowEval1639 x
  · exact rowEval1640 x
  · exact rowEval1641 x
  · exact rowEval1642 x
  · exact rowEval1643 x

theorem entryEval9_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_5 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck9_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_5]

def rows9_6 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1644, row1645, row1646, row1647, row1648, row1649, row1650, row1651, row1652, row1653, row1654, row1655, row1656, row1657, row1658, row1659, row1660, row1661, row1662, row1663, row1664, row1665, row1666, row1667, row1668, row1669, row1670, row1671, row1672, row1673]

theorem entryCheck9_6 : entry9_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_6 k)) := by decide +kernel

theorem rowsSound9_6 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval1644 x
  · exact rowEval1645 x
  · exact rowEval1646 x
  · exact rowEval1647 x
  · exact rowEval1648 x
  · exact rowEval1649 x
  · exact rowEval1650 x
  · exact rowEval1651 x
  · exact rowEval1652 x
  · exact rowEval1653 x
  · exact rowEval1654 x
  · exact rowEval1655 x
  · exact rowEval1656 x
  · exact rowEval1657 x
  · exact rowEval1658 x
  · exact rowEval1659 x
  · exact rowEval1660 x
  · exact rowEval1661 x
  · exact rowEval1662 x
  · exact rowEval1663 x
  · exact rowEval1664 x
  · exact rowEval1665 x
  · exact rowEval1666 x
  · exact rowEval1667 x
  · exact rowEval1668 x
  · exact rowEval1669 x
  · exact rowEval1670 x
  · exact rowEval1671 x
  · exact rowEval1672 x
  · exact rowEval1673 x

theorem entryEval9_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_6 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck9_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_6]

def rows9_7 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1674, row1675, row1676, row1677, row1678, row1679, row1680, row1681, row1682, row1683, row1684, row1685, row1686, row1687, row1688, row1689, row1690, row1691, row1692, row1693, row1694, row1695, row1696, row1697, row1698, row1699, row1700, row1701, row1702, row1703]

theorem entryCheck9_7 : entry9_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_7 k)) := by decide +kernel

theorem rowsSound9_7 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval1674 x
  · exact rowEval1675 x
  · exact rowEval1676 x
  · exact rowEval1677 x
  · exact rowEval1678 x
  · exact rowEval1679 x
  · exact rowEval1680 x
  · exact rowEval1681 x
  · exact rowEval1682 x
  · exact rowEval1683 x
  · exact rowEval1684 x
  · exact rowEval1685 x
  · exact rowEval1686 x
  · exact rowEval1687 x
  · exact rowEval1688 x
  · exact rowEval1689 x
  · exact rowEval1690 x
  · exact rowEval1691 x
  · exact rowEval1692 x
  · exact rowEval1693 x
  · exact rowEval1694 x
  · exact rowEval1695 x
  · exact rowEval1696 x
  · exact rowEval1697 x
  · exact rowEval1698 x
  · exact rowEval1699 x
  · exact rowEval1700 x
  · exact rowEval1701 x
  · exact rowEval1702 x
  · exact rowEval1703 x

theorem entryEval9_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_7 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck9_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_7]

def rows9_8 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1704, row1705, row1706, row1707, row1708, row1709, row1710, row1711, row1712, row1713, row1714, row1715, row1716, row1717, row1718, row1719, row1720, row1721, row1722, row1723, row1724, row1725, row1726, row1727, row1728, row1729, row1730, row1731, row1732, row1733]

theorem entryCheck9_8 : entry9_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_8 k)) := by decide +kernel

theorem rowsSound9_8 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval1704 x
  · exact rowEval1705 x
  · exact rowEval1706 x
  · exact rowEval1707 x
  · exact rowEval1708 x
  · exact rowEval1709 x
  · exact rowEval1710 x
  · exact rowEval1711 x
  · exact rowEval1712 x
  · exact rowEval1713 x
  · exact rowEval1714 x
  · exact rowEval1715 x
  · exact rowEval1716 x
  · exact rowEval1717 x
  · exact rowEval1718 x
  · exact rowEval1719 x
  · exact rowEval1720 x
  · exact rowEval1721 x
  · exact rowEval1722 x
  · exact rowEval1723 x
  · exact rowEval1724 x
  · exact rowEval1725 x
  · exact rowEval1726 x
  · exact rowEval1727 x
  · exact rowEval1728 x
  · exact rowEval1729 x
  · exact rowEval1730 x
  · exact rowEval1731 x
  · exact rowEval1732 x
  · exact rowEval1733 x

theorem entryEval9_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_8 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck9_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_8]

def rows9_9 : Fin GramFunctions.Block1.form9.size → Integer.Sparse Key := ![row1734, row1735, row1736, row1737, row1738, row1739, row1740, row1741, row1742, row1743, row1744, row1745, row1746, row1747, row1748, row1749, row1750, row1751, row1752, row1753, row1754, row1755, row1756, row1757, row1758, row1759, row1760, row1761, row1762, row1763]

theorem entryCheck9_9 : entry9_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form9.terms k).coefficient) (rows9_9 k)) := by decide +kernel

theorem rowsSound9_9 (k : Fin GramFunctions.Block1.form9.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows9_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form9.terms k).tag (GramFunctions.Block1.form9.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval1734 x
  · exact rowEval1735 x
  · exact rowEval1736 x
  · exact rowEval1737 x
  · exact rowEval1738 x
  · exact rowEval1739 x
  · exact rowEval1740 x
  · exact rowEval1741 x
  · exact rowEval1742 x
  · exact rowEval1743 x
  · exact rowEval1744 x
  · exact rowEval1745 x
  · exact rowEval1746 x
  · exact rowEval1747 x
  · exact rowEval1748 x
  · exact rowEval1749 x
  · exact rowEval1750 x
  · exact rowEval1751 x
  · exact rowEval1752 x
  · exact rowEval1753 x
  · exact rowEval1754 x
  · exact rowEval1755 x
  · exact rowEval1756 x
  · exact rowEval1757 x
  · exact rowEval1758 x
  · exact rowEval1759 x
  · exact rowEval1760 x
  · exact rowEval1761 x
  · exact rowEval1762 x
  · exact rowEval1763 x

theorem entryEval9_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry9_9 (GramNormalization.eval B) = GramFunctions.Block1.form9.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck9_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form9 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound9_9]

end MUB6.Certificate.GramEntries.Block1

end OAI
