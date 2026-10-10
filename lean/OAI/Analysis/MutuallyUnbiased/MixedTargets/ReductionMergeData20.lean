import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData20
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData21
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData19

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge640 : Integer.Sparse Master := [(Sum.inr 1511, -2862630613510520832000), (Sum.inr 1512, -1812234680041734144000)]

def originalMerge640 : Integer.Sparse OriginalKey := originalTerm645 ++ originalTerm646

theorem reducedMerge640Check : reducedMerge640 = Integer.Sparse.mergeBy masterLess reducedTerm645 reducedTerm646 := by decide +kernel

def reducedMerge641 : Integer.Sparse Master := [(Sum.inr 1510, -2210913934743306240000), (Sum.inr 1511, -2862630613510520832000), (Sum.inr 1512, -1812234680041734144000)]

def originalMerge641 : Integer.Sparse OriginalKey := originalTerm644 ++ originalMerge640

theorem reducedMerge641Check : reducedMerge641 = Integer.Sparse.mergeBy masterLess reducedTerm644 reducedMerge640 := by decide +kernel

def reducedMerge642 : Integer.Sparse Master := [(Sum.inr 1513, 807931683631005696000), (Sum.inr 1514, 279082176459964416000)]

def originalMerge642 : Integer.Sparse OriginalKey := originalTerm647 ++ originalTerm648

theorem reducedMerge642Check : reducedMerge642 = Integer.Sparse.mergeBy masterLess reducedTerm647 reducedTerm648 := by decide +kernel

def reducedMerge643 : Integer.Sparse Master := [(Sum.inr 1515, 1951341470849433600000), (Sum.inr 1516, 1532149313286832128000)]

def originalMerge643 : Integer.Sparse OriginalKey := originalTerm649 ++ originalTerm650

theorem reducedMerge643Check : reducedMerge643 = Integer.Sparse.mergeBy masterLess reducedTerm649 reducedTerm650 := by decide +kernel

def reducedMerge644 : Integer.Sparse Master := [(Sum.inr 1513, 807931683631005696000), (Sum.inr 1514, 279082176459964416000), (Sum.inr 1515, 1951341470849433600000), (Sum.inr 1516, 1532149313286832128000)]

def originalMerge644 : Integer.Sparse OriginalKey := originalMerge642 ++ originalMerge643

theorem reducedMerge644Check : reducedMerge644 = Integer.Sparse.mergeBy masterLess reducedMerge642 reducedMerge643 := by decide +kernel

def reducedMerge645 : Integer.Sparse Master := [(Sum.inr 1510, -2210913934743306240000), (Sum.inr 1511, -2862630613510520832000), (Sum.inr 1512, -1812234680041734144000), (Sum.inr 1513, 807931683631005696000), (Sum.inr 1514, 279082176459964416000), (Sum.inr 1515, 1951341470849433600000), (Sum.inr 1516, 1532149313286832128000)]

def originalMerge645 : Integer.Sparse OriginalKey := originalMerge641 ++ originalMerge644

theorem reducedMerge645Check : reducedMerge645 = Integer.Sparse.mergeBy masterLess reducedMerge641 reducedMerge644 := by decide +kernel

def reducedMerge646 : Integer.Sparse Master := [(Sum.inr 1520, 3125626258862112768000), (Sum.inr 1522, 1398340775856439296000)]

def originalMerge646 : Integer.Sparse OriginalKey := originalTerm651 ++ originalTerm652

theorem reducedMerge646Check : reducedMerge646 = Integer.Sparse.mergeBy masterLess reducedTerm651 reducedTerm652 := by decide +kernel

def reducedMerge647 : Integer.Sparse Master := [(Sum.inr 1523, 1978196107527585792000), (Sum.inr 1526, 3237439447258103808000)]

def originalMerge647 : Integer.Sparse OriginalKey := originalTerm653 ++ originalTerm654

theorem reducedMerge647Check : reducedMerge647 = Integer.Sparse.mergeBy masterLess reducedTerm653 reducedTerm654 := by decide +kernel

def reducedMerge648 : Integer.Sparse Master := [(Sum.inr 1520, 3125626258862112768000), (Sum.inr 1522, 1398340775856439296000), (Sum.inr 1523, 1978196107527585792000), (Sum.inr 1526, 3237439447258103808000)]

def originalMerge648 : Integer.Sparse OriginalKey := originalMerge646 ++ originalMerge647

theorem reducedMerge648Check : reducedMerge648 = Integer.Sparse.mergeBy masterLess reducedMerge646 reducedMerge647 := by decide +kernel

def reducedMerge649 : Integer.Sparse Master := [(Sum.inr 1528, -115736953684230144000), (Sum.inr 1529, -190397481621258240000)]

def originalMerge649 : Integer.Sparse OriginalKey := originalTerm655 ++ originalTerm656

theorem reducedMerge649Check : reducedMerge649 = Integer.Sparse.mergeBy masterLess reducedTerm655 reducedTerm656 := by decide +kernel

def reducedMerge650 : Integer.Sparse Master := [(Sum.inr 1530, -179029231679176704000), (Sum.inr 1531, -24315273996926976000)]

def originalMerge650 : Integer.Sparse OriginalKey := originalTerm657 ++ originalTerm658

theorem reducedMerge650Check : reducedMerge650 = Integer.Sparse.mergeBy masterLess reducedTerm657 reducedTerm658 := by decide +kernel

def reducedMerge651 : Integer.Sparse Master := [(Sum.inr 1528, -115736953684230144000), (Sum.inr 1529, -190397481621258240000), (Sum.inr 1530, -179029231679176704000), (Sum.inr 1531, -24315273996926976000)]

def originalMerge651 : Integer.Sparse OriginalKey := originalMerge649 ++ originalMerge650

theorem reducedMerge651Check : reducedMerge651 = Integer.Sparse.mergeBy masterLess reducedMerge649 reducedMerge650 := by decide +kernel

def reducedMerge652 : Integer.Sparse Master := [(Sum.inr 1520, 3125626258862112768000), (Sum.inr 1522, 1398340775856439296000), (Sum.inr 1523, 1978196107527585792000), (Sum.inr 1526, 3237439447258103808000), (Sum.inr 1528, -115736953684230144000), (Sum.inr 1529, -190397481621258240000), (Sum.inr 1530, -179029231679176704000), (Sum.inr 1531, -24315273996926976000)]

def originalMerge652 : Integer.Sparse OriginalKey := originalMerge648 ++ originalMerge651

theorem reducedMerge652Check : reducedMerge652 = Integer.Sparse.mergeBy masterLess reducedMerge648 reducedMerge651 := by decide +kernel

def reducedMerge653 : Integer.Sparse Master := [(Sum.inr 1510, -2210913934743306240000), (Sum.inr 1511, -2862630613510520832000), (Sum.inr 1512, -1812234680041734144000), (Sum.inr 1513, 807931683631005696000), (Sum.inr 1514, 279082176459964416000), (Sum.inr 1515, 1951341470849433600000), (Sum.inr 1516, 1532149313286832128000), (Sum.inr 1520, 3125626258862112768000), (Sum.inr 1522, 1398340775856439296000), (Sum.inr 1523, 1978196107527585792000), (Sum.inr 1526, 3237439447258103808000), (Sum.inr 1528, -115736953684230144000), (Sum.inr 1529, -190397481621258240000), (Sum.inr 1530, -179029231679176704000), (Sum.inr 1531, -24315273996926976000)]

def originalMerge653 : Integer.Sparse OriginalKey := originalMerge645 ++ originalMerge652

theorem reducedMerge653Check : reducedMerge653 = Integer.Sparse.mergeBy masterLess reducedMerge645 reducedMerge652 := by decide +kernel

def reducedMerge654 : Integer.Sparse Master := [(Sum.inr 1375, -11526746062619934720000), (Sum.inr 1383, 4656026210537963520000), (Sum.inr 1385, -3478154931439534080000), (Sum.inr 1388, -2299907207666073600000), (Sum.inr 1391, -2356119002871889920000), (Sum.inr 1406, -22276992136265072640000), (Sum.inr 1408, -17269758213677383680000), (Sum.inr 1435, 847409560407244800000), (Sum.inr 1436, -3245969833485926400000), (Sum.inr 1438, 39708998817546240000), (Sum.inr 1501, -1056230257065984000000), (Sum.inr 1502, -1423280520010137600000), (Sum.inr 1504, -1951341470849433600000), (Sum.inr 1505, 1056230257065984000000), (Sum.inr 1508, 1423280520010137600000), (Sum.inr 1510, -2210913934743306240000), (Sum.inr 1511, -2862630613510520832000), (Sum.inr 1512, -1812234680041734144000), (Sum.inr 1513, 807931683631005696000), (Sum.inr 1514, 279082176459964416000), (Sum.inr 1515, 1951341470849433600000), (Sum.inr 1516, 1532149313286832128000), (Sum.inr 1520, 3125626258862112768000), (Sum.inr 1522, 1398340775856439296000), (Sum.inr 1523, 1978196107527585792000), (Sum.inr 1526, 3237439447258103808000), (Sum.inr 1528, -115736953684230144000), (Sum.inr 1529, -190397481621258240000), (Sum.inr 1530, -179029231679176704000), (Sum.inr 1531, -24315273996926976000)]

def originalMerge654 : Integer.Sparse OriginalKey := originalMerge639 ++ originalMerge653

theorem reducedMerge654Check : reducedMerge654 = Integer.Sparse.mergeBy masterLess reducedMerge639 reducedMerge653 := by decide +kernel

def reducedMerge655 : Integer.Sparse Master := [(Sum.inr 1310, -626180907745935360000), (Sum.inr 1314, 5977466481711513600000), (Sum.inr 1315, 3501622812129361920000), (Sum.inr 1316, -9579839035999518720000), (Sum.inr 1317, 7341542882196848640000), (Sum.inr 1318, -4432587559454638080000), (Sum.inr 1319, -3032742142629642240000), (Sum.inr 1320, 11886766950399344640000), (Sum.inr 1321, -10548491592982855680000), (Sum.inr 1322, 9579839035999518720000), (Sum.inr 1323, -4933072605979607040000), (Sum.inr 1324, -8886421804453724160000), (Sum.inr 1325, -8635312347795947520000), (Sum.inr 1326, 277114839928012800000), (Sum.inr 1327, -5341116330562682880000), (Sum.inr 1328, -2299907207666073600000), (Sum.inr 1330, -819339736118722560000), (Sum.inr 1332, -3493413807980544000000), (Sum.inr 1333, 7641023538228756480000), (Sum.inr 1334, 8698253102854963200000), (Sum.inr 1335, 7361272231133184000000), (Sum.inr 1336, 3435031202884485120000), (Sum.inr 1337, -1895122181062656000000), (Sum.inr 1338, 4158977745420288000000), (Sum.inr 1348, 1542086242739159040000), (Sum.inr 1366, -1899117244195799040000), (Sum.inr 1367, 2667259420956426240000), (Sum.inr 1369, -3750701327642787840000), (Sum.inr 1370, 1899117244195799040000), (Sum.inr 1372, 8859486641663508480000), (Sum.inr 1375, -11526746062619934720000), (Sum.inr 1383, 4656026210537963520000), (Sum.inr 1385, -3478154931439534080000), (Sum.inr 1388, -2299907207666073600000), (Sum.inr 1391, -2356119002871889920000), (Sum.inr 1406, -22276992136265072640000), (Sum.inr 1408, -17269758213677383680000), (Sum.inr 1435, 847409560407244800000), (Sum.inr 1436, -3245969833485926400000), (Sum.inr 1438, 39708998817546240000), (Sum.inr 1501, -1056230257065984000000), (Sum.inr 1502, -1423280520010137600000), (Sum.inr 1504, -1951341470849433600000), (Sum.inr 1505, 1056230257065984000000), (Sum.inr 1508, 1423280520010137600000), (Sum.inr 1510, -2210913934743306240000), (Sum.inr 1511, -2862630613510520832000), (Sum.inr 1512, -1812234680041734144000), (Sum.inr 1513, 807931683631005696000), (Sum.inr 1514, 279082176459964416000), (Sum.inr 1515, 1951341470849433600000), (Sum.inr 1516, 1532149313286832128000), (Sum.inr 1520, 3125626258862112768000), (Sum.inr 1522, 1398340775856439296000), (Sum.inr 1523, 1978196107527585792000), (Sum.inr 1526, 3237439447258103808000), (Sum.inr 1528, -115736953684230144000), (Sum.inr 1529, -190397481621258240000), (Sum.inr 1530, -179029231679176704000), (Sum.inr 1531, -24315273996926976000)]

def originalMerge655 : Integer.Sparse OriginalKey := originalMerge625 ++ originalMerge654

theorem reducedMerge655Check : reducedMerge655 = Integer.Sparse.mergeBy masterLess reducedMerge625 reducedMerge654 := by decide +kernel

def reducedMerge656 : Integer.Sparse Master := [(Sum.inr 1533, 3726326584597413888000), (Sum.inr 1534, 92042023309737984000)]

def originalMerge656 : Integer.Sparse OriginalKey := originalTerm660 ++ originalTerm661

theorem reducedMerge656Check : reducedMerge656 = Integer.Sparse.mergeBy masterLess reducedTerm660 reducedTerm661 := by decide +kernel

def reducedMerge657 : Integer.Sparse Master := [(Sum.inr 1532, 513372727945986048000), (Sum.inr 1533, 3726326584597413888000), (Sum.inr 1534, 92042023309737984000)]

def originalMerge657 : Integer.Sparse OriginalKey := originalTerm659 ++ originalMerge656

theorem reducedMerge657Check : reducedMerge657 = Integer.Sparse.mergeBy masterLess reducedTerm659 reducedMerge656 := by decide +kernel

def reducedMerge658 : Integer.Sparse Master := [(Sum.inr 1540, 299269579737268224000), (Sum.inr 1667, -1090667657931522048000)]

def originalMerge658 : Integer.Sparse OriginalKey := originalTerm662 ++ originalTerm663

theorem reducedMerge658Check : reducedMerge658 = Integer.Sparse.mergeBy masterLess reducedTerm662 reducedTerm663 := by decide +kernel

def reducedMerge659 : Integer.Sparse Master := [(Sum.inr 1668, -1101980502152183808000), (Sum.inr 1670, -735052166107693056000)]

def originalMerge659 : Integer.Sparse OriginalKey := originalTerm664 ++ originalTerm665

theorem reducedMerge659Check : reducedMerge659 = Integer.Sparse.mergeBy masterLess reducedTerm664 reducedTerm665 := by decide +kernel

def reducedMerge660 : Integer.Sparse Master := [(Sum.inr 1540, 299269579737268224000), (Sum.inr 1667, -1090667657931522048000), (Sum.inr 1668, -1101980502152183808000), (Sum.inr 1670, -735052166107693056000)]

def originalMerge660 : Integer.Sparse OriginalKey := originalMerge658 ++ originalMerge659

theorem reducedMerge660Check : reducedMerge660 = Integer.Sparse.mergeBy masterLess reducedMerge658 reducedMerge659 := by decide +kernel

def reducedMerge661 : Integer.Sparse Master := [(Sum.inr 1532, 513372727945986048000), (Sum.inr 1533, 3726326584597413888000), (Sum.inr 1534, 92042023309737984000), (Sum.inr 1540, 299269579737268224000), (Sum.inr 1667, -1090667657931522048000), (Sum.inr 1668, -1101980502152183808000), (Sum.inr 1670, -735052166107693056000)]

def originalMerge661 : Integer.Sparse OriginalKey := originalMerge657 ++ originalMerge660

theorem reducedMerge661Check : reducedMerge661 = Integer.Sparse.mergeBy masterLess reducedMerge657 reducedMerge660 := by decide +kernel

def reducedMerge662 : Integer.Sparse Master := [(Sum.inr 1672, -615325865037004800000), (Sum.inr 1676, 441343231347916800000)]

def originalMerge662 : Integer.Sparse OriginalKey := originalTerm666 ++ originalTerm667

theorem reducedMerge662Check : reducedMerge662 = Integer.Sparse.mergeBy masterLess reducedTerm666 reducedTerm667 := by decide +kernel

def reducedMerge663 : Integer.Sparse Master := [(Sum.inr 1678, 2798915153550114816000), (Sum.inr 1679, 4204277593279561728000)]

def originalMerge663 : Integer.Sparse OriginalKey := originalTerm668 ++ originalTerm669

theorem reducedMerge663Check : reducedMerge663 = Integer.Sparse.mergeBy masterLess reducedTerm668 reducedTerm669 := by decide +kernel

def reducedMerge664 : Integer.Sparse Master := [(Sum.inr 1672, -615325865037004800000), (Sum.inr 1676, 441343231347916800000), (Sum.inr 1678, 2798915153550114816000), (Sum.inr 1679, 4204277593279561728000)]

def originalMerge664 : Integer.Sparse OriginalKey := originalMerge662 ++ originalMerge663

theorem reducedMerge664Check : reducedMerge664 = Integer.Sparse.mergeBy masterLess reducedMerge662 reducedMerge663 := by decide +kernel

def reducedMerge665 : Integer.Sparse Master := [(Sum.inr 1682, 4390161007521300480000), (Sum.inr 1684, 604529641244196864000)]

def originalMerge665 : Integer.Sparse OriginalKey := originalTerm670 ++ originalTerm671

theorem reducedMerge665Check : reducedMerge665 = Integer.Sparse.mergeBy masterLess reducedTerm670 reducedTerm671 := by decide +kernel

def reducedMerge666 : Integer.Sparse Master := [(Sum.inr 1685, 910860777696264192000), (Sum.inr 1686, 789405404560883712000)]

def originalMerge666 : Integer.Sparse OriginalKey := originalTerm672 ++ originalTerm673

theorem reducedMerge666Check : reducedMerge666 = Integer.Sparse.mergeBy masterLess reducedTerm672 reducedTerm673 := by decide +kernel

def reducedMerge667 : Integer.Sparse Master := [(Sum.inr 1682, 4390161007521300480000), (Sum.inr 1684, 604529641244196864000), (Sum.inr 1685, 910860777696264192000), (Sum.inr 1686, 789405404560883712000)]

def originalMerge667 : Integer.Sparse OriginalKey := originalMerge665 ++ originalMerge666

theorem reducedMerge667Check : reducedMerge667 = Integer.Sparse.mergeBy masterLess reducedMerge665 reducedMerge666 := by decide +kernel

def reducedMerge668 : Integer.Sparse Master := [(Sum.inr 1672, -615325865037004800000), (Sum.inr 1676, 441343231347916800000), (Sum.inr 1678, 2798915153550114816000), (Sum.inr 1679, 4204277593279561728000), (Sum.inr 1682, 4390161007521300480000), (Sum.inr 1684, 604529641244196864000), (Sum.inr 1685, 910860777696264192000), (Sum.inr 1686, 789405404560883712000)]

def originalMerge668 : Integer.Sparse OriginalKey := originalMerge664 ++ originalMerge667

theorem reducedMerge668Check : reducedMerge668 = Integer.Sparse.mergeBy masterLess reducedMerge664 reducedMerge667 := by decide +kernel

def reducedMerge669 : Integer.Sparse Master := [(Sum.inr 1532, 513372727945986048000), (Sum.inr 1533, 3726326584597413888000), (Sum.inr 1534, 92042023309737984000), (Sum.inr 1540, 299269579737268224000), (Sum.inr 1667, -1090667657931522048000), (Sum.inr 1668, -1101980502152183808000), (Sum.inr 1670, -735052166107693056000), (Sum.inr 1672, -615325865037004800000), (Sum.inr 1676, 441343231347916800000), (Sum.inr 1678, 2798915153550114816000), (Sum.inr 1679, 4204277593279561728000), (Sum.inr 1682, 4390161007521300480000), (Sum.inr 1684, 604529641244196864000), (Sum.inr 1685, 910860777696264192000), (Sum.inr 1686, 789405404560883712000)]

def originalMerge669 : Integer.Sparse OriginalKey := originalMerge661 ++ originalMerge668

theorem reducedMerge669Check : reducedMerge669 = Integer.Sparse.mergeBy masterLess reducedMerge661 reducedMerge668 := by decide +kernel

def reducedMerge670 : Integer.Sparse Master := [(Sum.inr 1688, 1305313133883752448000), (Sum.inr 1689, 3666193326655340544000)]

def originalMerge670 : Integer.Sparse OriginalKey := originalTerm675 ++ originalTerm676

theorem reducedMerge670Check : reducedMerge670 = Integer.Sparse.mergeBy masterLess reducedTerm675 reducedTerm676 := by decide +kernel

def reducedMerge671 : Integer.Sparse Master := [(Sum.inr 1687, -120789168095232000000), (Sum.inr 1688, 1305313133883752448000), (Sum.inr 1689, 3666193326655340544000)]

def originalMerge671 : Integer.Sparse OriginalKey := originalTerm674 ++ originalMerge670

theorem reducedMerge671Check : reducedMerge671 = Integer.Sparse.mergeBy masterLess reducedTerm674 reducedMerge670 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
