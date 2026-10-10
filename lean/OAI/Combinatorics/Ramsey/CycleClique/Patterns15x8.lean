import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates048
import OAI.Combinatorics.Ramsey.CycleClique.Certificates049
import OAI.Combinatorics.Ramsey.CycleClique.Certificates050
import OAI.Combinatorics.Ramsey.CycleClique.Certificates051
import OAI.Combinatorics.Ramsey.CycleClique.Certificates052
import OAI.Combinatorics.Ramsey.CycleClique.Certificates053
import OAI.Combinatorics.Ramsey.CycleClique.Certificates054
import OAI.Combinatorics.Ramsey.CycleClique.Certificates055
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.PatternReduction

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_15_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[],[6]],[[],[],[],[],[],[],[7]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[1,5]],[[],[],[],[],[],[1,6]],[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]]]

theorem patterns_15_8_0_verified : ∀ D ∈ patterns_15_8_0, PatternVerified 15 8 D := by

  simp only [patterns_15_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_1515, certificate_1515_valid⟩, ⟨⟨certificate_1516, certificate_1516_valid⟩, ⟨⟨certificate_1517, certificate_1517_valid⟩, ⟨⟨certificate_1518, certificate_1518_valid⟩, ⟨⟨certificate_1519, certificate_1519_valid⟩, ⟨⟨certificate_1520, certificate_1520_valid⟩, ⟨⟨certificate_1521, certificate_1521_valid⟩, ⟨⟨certificate_1522, certificate_1522_valid⟩, ⟨⟨certificate_1523, certificate_1523_valid⟩, ⟨⟨certificate_1524, certificate_1524_valid⟩, ⟨⟨certificate_1525, certificate_1525_valid⟩, ⟨⟨certificate_1526, certificate_1526_valid⟩, ⟨⟨certificate_1527, certificate_1527_valid⟩, ⟨⟨certificate_1528, certificate_1528_valid⟩, ⟨⟨certificate_1529, certificate_1529_valid⟩, ⟨⟨certificate_1530, certificate_1530_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_1 : List (List (List ℕ)) := [[[],[],[],[],[],[2,4]],[[],[],[],[],[],[2,5]],[[],[],[],[],[],[3,3]],[[],[],[],[],[],[3,4]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]],[[],[],[],[],[1],[5]],[[],[],[],[],[1],[6]],[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,1,4]],[[],[],[],[],[1,1,5]],[[],[],[],[],[1,2,1]]]

theorem patterns_15_8_1_verified : ∀ D ∈ patterns_15_8_1, PatternVerified 15 8 D := by

  simp only [patterns_15_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_1531, certificate_1531_valid⟩, ⟨⟨certificate_1532, certificate_1532_valid⟩, ⟨⟨certificate_1533, certificate_1533_valid⟩, ⟨⟨certificate_1534, certificate_1534_valid⟩, ⟨⟨certificate_1535, certificate_1535_valid⟩, ⟨⟨certificate_1536, certificate_1536_valid⟩, ⟨⟨certificate_1537, certificate_1537_valid⟩, ⟨⟨certificate_1538, certificate_1538_valid⟩, ⟨⟨certificate_1539, certificate_1539_valid⟩, ⟨⟨certificate_1540, certificate_1540_valid⟩, ⟨⟨certificate_1541, certificate_1541_valid⟩, ⟨⟨certificate_1542, certificate_1542_valid⟩, ⟨⟨certificate_1543, certificate_1543_valid⟩, ⟨⟨certificate_1544, certificate_1544_valid⟩, ⟨⟨certificate_1545, certificate_1545_valid⟩, ⟨⟨certificate_1546, certificate_1546_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_2 : List (List (List ℕ)) := [[[],[],[],[],[1,2,2]],[[],[],[],[],[1,2,3]],[[],[],[],[],[1,2,4]],[[],[],[],[],[1,3,1]],[[],[],[],[],[1,3,2]],[[],[],[],[],[1,3,3]],[[],[],[],[],[1,4,1]],[[],[],[],[],[1,4,2]],[[],[],[],[],[1,5,1]],[[],[],[],[],[2],[2]],[[],[],[],[],[2],[3]],[[],[],[],[],[2],[4]],[[],[],[],[],[2],[5]],[[],[],[],[],[2,1,2]],[[],[],[],[],[2,1,3]],[[],[],[],[],[2,1,4]]]

theorem patterns_15_8_2_verified : ∀ D ∈ patterns_15_8_2, PatternVerified 15 8 D := by

  simp only [patterns_15_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_1547, certificate_1547_valid⟩, ⟨⟨certificate_1548, certificate_1548_valid⟩, ⟨⟨certificate_1549, certificate_1549_valid⟩, ⟨⟨certificate_1550, certificate_1550_valid⟩, ⟨⟨certificate_1551, certificate_1551_valid⟩, ⟨⟨certificate_1552, certificate_1552_valid⟩, ⟨⟨certificate_1553, certificate_1553_valid⟩, ⟨⟨certificate_1554, certificate_1554_valid⟩, ⟨⟨certificate_1555, certificate_1555_valid⟩, ⟨⟨certificate_1556, certificate_1556_valid⟩, ⟨⟨certificate_1557, certificate_1557_valid⟩, ⟨⟨certificate_1558, certificate_1558_valid⟩, ⟨⟨certificate_1559, certificate_1559_valid⟩, ⟨⟨certificate_1560, certificate_1560_valid⟩, ⟨⟨certificate_1561, certificate_1561_valid⟩, ⟨⟨certificate_1562, certificate_1562_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_3 : List (List (List ℕ)) := [[[],[],[],[],[2,2,2]],[[],[],[],[],[2,2,3]],[[],[],[],[],[2,3,2]],[[],[],[],[],[3],[3]],[[],[],[],[],[3],[4]],[[],[],[],[],[3,1,3]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[1,4]],[[],[],[],[1],[1,5]],[[],[],[],[1],[2,2]],[[],[],[],[1],[2,3]],[[],[],[],[1],[2,4]],[[],[],[],[1],[3,3]],[[],[],[],[1,1],[2]]]

theorem patterns_15_8_3_verified : ∀ D ∈ patterns_15_8_3, PatternVerified 15 8 D := by

  simp only [patterns_15_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_1563, certificate_1563_valid⟩, ⟨⟨certificate_1564, certificate_1564_valid⟩, ⟨⟨certificate_1565, certificate_1565_valid⟩, ⟨⟨certificate_1566, certificate_1566_valid⟩, ⟨⟨certificate_1567, certificate_1567_valid⟩, ⟨⟨certificate_1568, certificate_1568_valid⟩, ⟨⟨certificate_1569, certificate_1569_valid⟩, ⟨⟨certificate_1570, certificate_1570_valid⟩, ⟨⟨certificate_1571, certificate_1571_valid⟩, ⟨⟨certificate_1572, certificate_1572_valid⟩, ⟨⟨certificate_1573, certificate_1573_valid⟩, ⟨⟨certificate_1574, certificate_1574_valid⟩, ⟨⟨certificate_1575, certificate_1575_valid⟩, ⟨⟨certificate_1576, certificate_1576_valid⟩, ⟨⟨certificate_1577, certificate_1577_valid⟩, ⟨⟨certificate_1578, certificate_1578_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_4 : List (List (List ℕ)) := [[[],[],[],[1,1],[3]],[[],[],[],[1,1],[4]],[[],[],[],[1,1],[5]],[[],[],[],[1,1,1,1]],[[],[],[],[1,1,1,2]],[[],[],[],[1,1,1,3]],[[],[],[],[1,1,1,4]],[[],[],[],[1,1,2,1]],[[],[],[],[1,1,2,2]],[[],[],[],[1,1,2,3]],[[],[],[],[1,1,3,1]],[[],[],[],[1,1,3,2]],[[],[],[],[1,1,4,1]],[[],[],[],[1,2],[2]],[[],[],[],[1,2],[3]],[[],[],[],[1,2],[4]]]

theorem patterns_15_8_4_verified : ∀ D ∈ patterns_15_8_4, PatternVerified 15 8 D := by

  simp only [patterns_15_8_4, List.forall_mem_cons]

  exact ⟨⟨certificate_1579, certificate_1579_valid⟩, ⟨⟨certificate_1580, certificate_1580_valid⟩, ⟨⟨certificate_1581, certificate_1581_valid⟩, ⟨⟨certificate_1582, certificate_1582_valid⟩, ⟨⟨certificate_1583, certificate_1583_valid⟩, ⟨⟨certificate_1584, certificate_1584_valid⟩, ⟨⟨certificate_1585, certificate_1585_valid⟩, ⟨⟨certificate_1586, certificate_1586_valid⟩, ⟨⟨certificate_1587, certificate_1587_valid⟩, ⟨⟨certificate_1588, certificate_1588_valid⟩, ⟨⟨certificate_1589, certificate_1589_valid⟩, ⟨⟨certificate_1590, certificate_1590_valid⟩, ⟨⟨certificate_1591, certificate_1591_valid⟩, ⟨⟨certificate_1592, certificate_1592_valid⟩, ⟨⟨certificate_1593, certificate_1593_valid⟩, ⟨⟨certificate_1594, certificate_1594_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_5 : List (List (List ℕ)) := [[[],[],[],[1,2,1,2]],[[],[],[],[1,2,1,3]],[[],[],[],[1,2,2,1]],[[],[],[],[1,2,2,2]],[[],[],[],[1,2,3,1]],[[],[],[],[1,3],[2]],[[],[],[],[1,3],[3]],[[],[],[],[1,3,1,2]],[[],[],[],[1,4],[2]],[[],[],[],[2],[2,2]],[[],[],[],[2],[2,3]],[[],[],[],[2,1,1,2]],[[],[],[],[2,1,1,3]],[[],[],[],[2,1,2,2]],[[],[],[],[2,2],[3]],[[],[],[1],[1],[1]]]

theorem patterns_15_8_5_verified : ∀ D ∈ patterns_15_8_5, PatternVerified 15 8 D := by

  simp only [patterns_15_8_5, List.forall_mem_cons]

  exact ⟨⟨certificate_1595, certificate_1595_valid⟩, ⟨⟨certificate_1596, certificate_1596_valid⟩, ⟨⟨certificate_1597, certificate_1597_valid⟩, ⟨⟨certificate_1598, certificate_1598_valid⟩, ⟨⟨certificate_1599, certificate_1599_valid⟩, ⟨⟨certificate_1600, certificate_1600_valid⟩, ⟨⟨certificate_1601, certificate_1601_valid⟩, ⟨⟨certificate_1602, certificate_1602_valid⟩, ⟨⟨certificate_1603, certificate_1603_valid⟩, ⟨⟨certificate_1604, certificate_1604_valid⟩, ⟨⟨certificate_1605, certificate_1605_valid⟩, ⟨⟨certificate_1606, certificate_1606_valid⟩, ⟨⟨certificate_1607, certificate_1607_valid⟩, ⟨⟨certificate_1608, certificate_1608_valid⟩, ⟨⟨certificate_1609, certificate_1609_valid⟩, ⟨⟨certificate_1610, certificate_1610_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_6 : List (List (List ℕ)) := [[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1],[4]],[[],[],[1],[1],[5]],[[],[],[1],[1,1,1]],[[],[],[1],[1,1,2]],[[],[],[1],[1,1,3]],[[],[],[1],[1,1,4]],[[],[],[1],[1,2,1]],[[],[],[1],[1,2,2]],[[],[],[1],[1,2,3]],[[],[],[1],[1,3,1]],[[],[],[1],[1,3,2]],[[],[],[1],[1,4,1]],[[],[],[1],[2],[2]],[[],[],[1],[2],[3]]]

theorem patterns_15_8_6_verified : ∀ D ∈ patterns_15_8_6, PatternVerified 15 8 D := by

  simp only [patterns_15_8_6, List.forall_mem_cons]

  exact ⟨⟨certificate_1611, certificate_1611_valid⟩, ⟨⟨certificate_1612, certificate_1612_valid⟩, ⟨⟨certificate_1613, certificate_1613_valid⟩, ⟨⟨certificate_1614, certificate_1614_valid⟩, ⟨⟨certificate_1615, certificate_1615_valid⟩, ⟨⟨certificate_1616, certificate_1616_valid⟩, ⟨⟨certificate_1617, certificate_1617_valid⟩, ⟨⟨certificate_1618, certificate_1618_valid⟩, ⟨⟨certificate_1619, certificate_1619_valid⟩, ⟨⟨certificate_1620, certificate_1620_valid⟩, ⟨⟨certificate_1621, certificate_1621_valid⟩, ⟨⟨certificate_1622, certificate_1622_valid⟩, ⟨⟨certificate_1623, certificate_1623_valid⟩, ⟨⟨certificate_1624, certificate_1624_valid⟩, ⟨⟨certificate_1625, certificate_1625_valid⟩, ⟨⟨certificate_1626, certificate_1626_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_7 : List (List (List ℕ)) := [[[],[],[1],[2],[4]],[[],[],[1],[2,1,2]],[[],[],[1],[2,1,3]],[[],[],[1],[2,2,2]],[[],[],[1],[3],[3]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1],[1,3]],[[],[],[1,1],[1,4]],[[],[],[1,1],[2,2]],[[],[],[1,1],[2,3]],[[],[],[1,1,1],[2]],[[],[],[1,1,1],[3]],[[],[],[1,1,1],[4]],[[],[],[1,1,1,1,1]],[[],[],[1,1,1,1,2]]]

theorem patterns_15_8_7_verified : ∀ D ∈ patterns_15_8_7, PatternVerified 15 8 D := by

  simp only [patterns_15_8_7, List.forall_mem_cons]

  exact ⟨⟨certificate_1627, certificate_1627_valid⟩, ⟨⟨certificate_1628, certificate_1628_valid⟩, ⟨⟨certificate_1629, certificate_1629_valid⟩, ⟨⟨certificate_1630, certificate_1630_valid⟩, ⟨⟨certificate_1631, certificate_1631_valid⟩, ⟨⟨certificate_1632, certificate_1632_valid⟩, ⟨⟨certificate_1633, certificate_1633_valid⟩, ⟨⟨certificate_1634, certificate_1634_valid⟩, ⟨⟨certificate_1635, certificate_1635_valid⟩, ⟨⟨certificate_1636, certificate_1636_valid⟩, ⟨⟨certificate_1637, certificate_1637_valid⟩, ⟨⟨certificate_1638, certificate_1638_valid⟩, ⟨⟨certificate_1639, certificate_1639_valid⟩, ⟨⟨certificate_1640, certificate_1640_valid⟩, ⟨⟨certificate_1641, certificate_1641_valid⟩, ⟨⟨certificate_1642, certificate_1642_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_8 : List (List (List ℕ)) := [[[],[],[1,1,1,1,3]],[[],[],[1,1,1,2,1]],[[],[],[1,1,1,2,2]],[[],[],[1,1,1,3,1]],[[],[],[1,1,2],[2]],[[],[],[1,1,2],[3]],[[],[],[1,1,2,1,1]],[[],[],[1,1,2,1,2]],[[],[],[1,1,2,2,1]],[[],[],[1,1,3],[2]],[[],[],[1,1,3,1,1]],[[],[],[1,2],[1,2]],[[],[],[1,2],[1,3]],[[],[],[1,2],[2,2]],[[],[],[1,2,1],[2]],[[],[],[1,2,1],[3]]]

theorem patterns_15_8_8_verified : ∀ D ∈ patterns_15_8_8, PatternVerified 15 8 D := by

  simp only [patterns_15_8_8, List.forall_mem_cons]

  exact ⟨⟨certificate_1643, certificate_1643_valid⟩, ⟨⟨certificate_1644, certificate_1644_valid⟩, ⟨⟨certificate_1645, certificate_1645_valid⟩, ⟨⟨certificate_1646, certificate_1646_valid⟩, ⟨⟨certificate_1647, certificate_1647_valid⟩, ⟨⟨certificate_1648, certificate_1648_valid⟩, ⟨⟨certificate_1649, certificate_1649_valid⟩, ⟨⟨certificate_1650, certificate_1650_valid⟩, ⟨⟨certificate_1651, certificate_1651_valid⟩, ⟨⟨certificate_1652, certificate_1652_valid⟩, ⟨⟨certificate_1653, certificate_1653_valid⟩, ⟨⟨certificate_1654, certificate_1654_valid⟩, ⟨⟨certificate_1655, certificate_1655_valid⟩, ⟨⟨certificate_1656, certificate_1656_valid⟩, ⟨⟨certificate_1657, certificate_1657_valid⟩, ⟨⟨certificate_1658, certificate_1658_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_9 : List (List (List ℕ)) := [[[],[],[1,2,1,1,2]],[[],[],[1,2,1,2,1]],[[],[],[1,2,2],[2]],[[],[],[1,3,1],[2]],[[],[],[2],[2],[2]],[[],[],[2],[2],[3]],[[],[],[2],[2,1,2]],[[],[],[2,1,1,1,2]],[[],[1],[1],[1,1]],[[],[1],[1],[1,2]],[[],[1],[1],[1,3]],[[],[1],[1],[1,4]],[[],[1],[1],[2,2]],[[],[1],[1],[2,3]],[[],[1],[1,1],[2]],[[],[1],[1,1],[3]]]

theorem patterns_15_8_9_verified : ∀ D ∈ patterns_15_8_9, PatternVerified 15 8 D := by

  simp only [patterns_15_8_9, List.forall_mem_cons]

  exact ⟨⟨certificate_1659, certificate_1659_valid⟩, ⟨⟨certificate_1660, certificate_1660_valid⟩, ⟨⟨certificate_1661, certificate_1661_valid⟩, ⟨⟨certificate_1662, certificate_1662_valid⟩, ⟨⟨certificate_1663, certificate_1663_valid⟩, ⟨⟨certificate_1664, certificate_1664_valid⟩, ⟨⟨certificate_1665, certificate_1665_valid⟩, ⟨⟨certificate_1666, certificate_1666_valid⟩, ⟨⟨certificate_1667, certificate_1667_valid⟩, ⟨⟨certificate_1668, certificate_1668_valid⟩, ⟨⟨certificate_1669, certificate_1669_valid⟩, ⟨⟨certificate_1670, certificate_1670_valid⟩, ⟨⟨certificate_1671, certificate_1671_valid⟩, ⟨⟨certificate_1672, certificate_1672_valid⟩, ⟨⟨certificate_1673, certificate_1673_valid⟩, ⟨⟨certificate_1674, certificate_1674_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_10 : List (List (List ℕ)) := [[[],[1],[1,1],[4]],[[],[1],[1,1,1,1]],[[],[1],[1,1,1,2]],[[],[1],[1,1,1,3]],[[],[1],[1,1,2,1]],[[],[1],[1,1,2,2]],[[],[1],[1,1,3,1]],[[],[1],[1,2],[2]],[[],[1],[1,2],[3]],[[],[1],[1,2,1,2]],[[],[1],[1,2,2,1]],[[],[1],[1,3],[2]],[[],[1],[2],[2,2]],[[],[1],[2,1,1,2]],[[],[1,1],[1,1,1]],[[],[1,1],[1,1,2]]]

theorem patterns_15_8_10_verified : ∀ D ∈ patterns_15_8_10, PatternVerified 15 8 D := by

  simp only [patterns_15_8_10, List.forall_mem_cons]

  exact ⟨⟨certificate_1675, certificate_1675_valid⟩, ⟨⟨certificate_1676, certificate_1676_valid⟩, ⟨⟨certificate_1677, certificate_1677_valid⟩, ⟨⟨certificate_1678, certificate_1678_valid⟩, ⟨⟨certificate_1679, certificate_1679_valid⟩, ⟨⟨certificate_1680, certificate_1680_valid⟩, ⟨⟨certificate_1681, certificate_1681_valid⟩, ⟨⟨certificate_1682, certificate_1682_valid⟩, ⟨⟨certificate_1683, certificate_1683_valid⟩, ⟨⟨certificate_1684, certificate_1684_valid⟩, ⟨⟨certificate_1685, certificate_1685_valid⟩, ⟨⟨certificate_1686, certificate_1686_valid⟩, ⟨⟨certificate_1687, certificate_1687_valid⟩, ⟨⟨certificate_1688, certificate_1688_valid⟩, ⟨⟨certificate_1689, certificate_1689_valid⟩, ⟨⟨certificate_1690, certificate_1690_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_11 : List (List (List ℕ)) := [[[],[1,1],[1,1,3]],[[],[1,1],[1,2,1]],[[],[1,1],[1,2,2]],[[],[1,1],[1,3,1]],[[],[1,1],[2],[2]],[[],[1,1],[2],[3]],[[],[1,1],[2,1,2]],[[],[1,1,1],[1,2]],[[],[1,1,1],[1,3]],[[],[1,1,1],[2,2]],[[],[1,1,1,1],[2]],[[],[1,1,1,1],[3]],[[],[1,1,1,1,1,1]],[[],[1,1,1,1,1,2]],[[],[1,1,1,1,2,1]],[[],[1,1,1,2],[2]]]

theorem patterns_15_8_11_verified : ∀ D ∈ patterns_15_8_11, PatternVerified 15 8 D := by

  simp only [patterns_15_8_11, List.forall_mem_cons]

  exact ⟨⟨certificate_1691, certificate_1691_valid⟩, ⟨⟨certificate_1692, certificate_1692_valid⟩, ⟨⟨certificate_1693, certificate_1693_valid⟩, ⟨⟨certificate_1694, certificate_1694_valid⟩, ⟨⟨certificate_1695, certificate_1695_valid⟩, ⟨⟨certificate_1696, certificate_1696_valid⟩, ⟨⟨certificate_1697, certificate_1697_valid⟩, ⟨⟨certificate_1698, certificate_1698_valid⟩, ⟨⟨certificate_1699, certificate_1699_valid⟩, ⟨⟨certificate_1700, certificate_1700_valid⟩, ⟨⟨certificate_1701, certificate_1701_valid⟩, ⟨⟨certificate_1702, certificate_1702_valid⟩, ⟨⟨certificate_1703, certificate_1703_valid⟩, ⟨⟨certificate_1704, certificate_1704_valid⟩, ⟨⟨certificate_1705, certificate_1705_valid⟩, ⟨⟨certificate_1706, certificate_1706_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_12 : List (List (List ℕ)) := [[[],[1,1,1,2,1,1]],[[],[1,1,2],[1,2]],[[],[1,1,2,1],[2]],[[],[1,2],[1,2,1]],[[],[1,2],[2],[2]],[[1],[1],[1],[1]],[[1],[1],[1],[2]],[[1],[1],[1],[3]],[[1],[1],[1],[4]],[[1],[1],[1,1,1]],[[1],[1],[1,1,2]],[[1],[1],[1,1,3]],[[1],[1],[1,2,1]],[[1],[1],[1,2,2]],[[1],[1],[1,3,1]],[[1],[1],[2],[2]]]

theorem patterns_15_8_12_verified : ∀ D ∈ patterns_15_8_12, PatternVerified 15 8 D := by

  simp only [patterns_15_8_12, List.forall_mem_cons]

  exact ⟨⟨certificate_1707, certificate_1707_valid⟩, ⟨⟨certificate_1708, certificate_1708_valid⟩, ⟨⟨certificate_1709, certificate_1709_valid⟩, ⟨⟨certificate_1710, certificate_1710_valid⟩, ⟨⟨certificate_1711, certificate_1711_valid⟩, ⟨⟨certificate_1712, certificate_1712_valid⟩, ⟨⟨certificate_1713, certificate_1713_valid⟩, ⟨⟨certificate_1714, certificate_1714_valid⟩, ⟨⟨certificate_1715, certificate_1715_valid⟩, ⟨⟨certificate_1716, certificate_1716_valid⟩, ⟨⟨certificate_1717, certificate_1717_valid⟩, ⟨⟨certificate_1718, certificate_1718_valid⟩, ⟨⟨certificate_1719, certificate_1719_valid⟩, ⟨⟨certificate_1720, certificate_1720_valid⟩, ⟨⟨certificate_1721, certificate_1721_valid⟩, ⟨⟨certificate_1722, certificate_1722_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_13 : List (List (List ℕ)) := [[[1],[1],[2],[3]],[[1],[1],[2,1,2]],[[1],[1,1],[1,1]],[[1],[1,1],[1,2]],[[1],[1,1],[1,3]],[[1],[1,1],[2,2]],[[1],[1,1,1],[2]],[[1],[1,1,1],[3]],[[1],[1,1,1,1,1]],[[1],[1,1,1,1,2]],[[1],[1,1,1,2,1]],[[1],[1,1,2],[2]],[[1],[1,1,2,1,1]],[[1],[1,2],[1,2]],[[1],[1,2,1],[2]],[[1],[2],[2],[2]]]

theorem patterns_15_8_13_verified : ∀ D ∈ patterns_15_8_13, PatternVerified 15 8 D := by

  simp only [patterns_15_8_13, List.forall_mem_cons]

  exact ⟨⟨certificate_1723, certificate_1723_valid⟩, ⟨⟨certificate_1724, certificate_1724_valid⟩, ⟨⟨certificate_1725, certificate_1725_valid⟩, ⟨⟨certificate_1726, certificate_1726_valid⟩, ⟨⟨certificate_1727, certificate_1727_valid⟩, ⟨⟨certificate_1728, certificate_1728_valid⟩, ⟨⟨certificate_1729, certificate_1729_valid⟩, ⟨⟨certificate_1730, certificate_1730_valid⟩, ⟨⟨certificate_1731, certificate_1731_valid⟩, ⟨⟨certificate_1732, certificate_1732_valid⟩, ⟨⟨certificate_1733, certificate_1733_valid⟩, ⟨⟨certificate_1734, certificate_1734_valid⟩, ⟨⟨certificate_1735, certificate_1735_valid⟩, ⟨⟨certificate_1736, certificate_1736_valid⟩, ⟨⟨certificate_1737, certificate_1737_valid⟩, ⟨⟨certificate_1738, certificate_1738_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8_14 : List (List (List ℕ)) := [[[1,1],[1,1],[2]],[[1,1],[1,1],[3]],[[1,1],[1,1,1,1]],[[1,1],[1,1,1,2]],[[1,1],[1,1,2,1]],[[1,1],[1,2],[2]],[[1,1,1],[1,1,1]],[[1,1,1],[1,1,2]],[[1,1,1],[1,2,1]],[[1,1,1],[2],[2]],[[1,1,1,1],[1,2]],[[1,1,1,1,1],[2]],[[1,1,1,1,1,1,1]]]

theorem patterns_15_8_14_verified : ∀ D ∈ patterns_15_8_14, PatternVerified 15 8 D := by

  simp only [patterns_15_8_14, List.forall_mem_cons]

  exact ⟨⟨certificate_1739, certificate_1739_valid⟩, ⟨⟨certificate_1740, certificate_1740_valid⟩, ⟨⟨certificate_1741, certificate_1741_valid⟩, ⟨⟨certificate_1742, certificate_1742_valid⟩, ⟨⟨certificate_1743, certificate_1743_valid⟩, ⟨⟨certificate_1744, certificate_1744_valid⟩, ⟨⟨certificate_1745, certificate_1745_valid⟩, ⟨⟨certificate_1746, certificate_1746_valid⟩, ⟨⟨certificate_1747, certificate_1747_valid⟩, ⟨⟨certificate_1748, certificate_1748_valid⟩, ⟨⟨certificate_1749, certificate_1749_valid⟩, ⟨⟨certificate_1750, certificate_1750_valid⟩, ⟨⟨certificate_1751, certificate_1751_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_15_8 : List (List (List ℕ)) := patterns_15_8_0 ++ (patterns_15_8_1 ++ (patterns_15_8_2 ++ (patterns_15_8_3 ++ (patterns_15_8_4 ++ (patterns_15_8_5 ++ (patterns_15_8_6 ++ (patterns_15_8_7 ++ (patterns_15_8_8 ++ (patterns_15_8_9 ++ (patterns_15_8_10 ++ (patterns_15_8_11 ++ (patterns_15_8_12 ++ (patterns_15_8_13 ++ (patterns_15_8_14 ++ ([])))))))))))))))

theorem patterns_15_8_verified : ∀ D ∈ patterns_15_8, PatternVerified 15 8 D := by

  simp only [patterns_15_8, List.forall_mem_append]

  exact ⟨patterns_15_8_0_verified, ⟨patterns_15_8_1_verified, ⟨patterns_15_8_2_verified, ⟨patterns_15_8_3_verified, ⟨patterns_15_8_4_verified, ⟨patterns_15_8_5_verified, ⟨patterns_15_8_6_verified, ⟨patterns_15_8_7_verified, ⟨patterns_15_8_8_verified, ⟨patterns_15_8_9_verified, ⟨patterns_15_8_10_verified, ⟨patterns_15_8_11_verified, ⟨patterns_15_8_12_verified, ⟨patterns_15_8_13_verified, ⟨patterns_15_8_14_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_15_8_coverage : patternChoices 8 7 [] = patterns_15_8 := by decide +kernel

theorem finite_patterns_15_8 : ∀ D ∈ patternChoices 8 (15-8) [], PatternVerified 15 8 D := by

  rw [patterns_15_8_coverage]

  exact patterns_15_8_verified

end CycleClique

end OAI
