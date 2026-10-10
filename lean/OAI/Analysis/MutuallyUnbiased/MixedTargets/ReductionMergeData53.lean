import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData53
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData54
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData52

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1696 : Integer.Sparse Master := [(Sum.inr 4819, -9689775870270504960000), (Sum.inr 4821, 24425621100813090816000)]

def originalMerge1696 : Integer.Sparse OriginalKey := originalTerm1701 ++ originalTerm1702

theorem reducedMerge1696Check : reducedMerge1696 = Integer.Sparse.mergeBy masterLess reducedTerm1701 reducedTerm1702 := by decide +kernel

def reducedMerge1697 : Integer.Sparse Master := [(Sum.inr 4830, 4276208522593566720000), (Sum.inr 4836, 14865336275325419520000)]

def originalMerge1697 : Integer.Sparse OriginalKey := originalTerm1703 ++ originalTerm1704

theorem reducedMerge1697Check : reducedMerge1697 = Integer.Sparse.mergeBy masterLess reducedTerm1703 reducedTerm1704 := by decide +kernel

def reducedMerge1698 : Integer.Sparse Master := [(Sum.inr 4819, -9689775870270504960000), (Sum.inr 4821, 24425621100813090816000), (Sum.inr 4830, 4276208522593566720000), (Sum.inr 4836, 14865336275325419520000)]

def originalMerge1698 : Integer.Sparse OriginalKey := originalMerge1696 ++ originalMerge1697

theorem reducedMerge1698Check : reducedMerge1698 = Integer.Sparse.mergeBy masterLess reducedMerge1696 reducedMerge1697 := by decide +kernel

def reducedMerge1699 : Integer.Sparse Master := [(Sum.inr 4844, -10611725918904778752000), (Sum.inr 4851, -3651536391380140032000)]

def originalMerge1699 : Integer.Sparse OriginalKey := originalTerm1705 ++ originalTerm1706

theorem reducedMerge1699Check : reducedMerge1699 = Integer.Sparse.mergeBy masterLess reducedTerm1705 reducedTerm1706 := by decide +kernel

def reducedMerge1700 : Integer.Sparse Master := [(Sum.inr 4852, 25540881314177875968000), (Sum.inr 4853, -8931969569439350784000)]

def originalMerge1700 : Integer.Sparse OriginalKey := originalTerm1707 ++ originalTerm1708

theorem reducedMerge1700Check : reducedMerge1700 = Integer.Sparse.mergeBy masterLess reducedTerm1707 reducedTerm1708 := by decide +kernel

def reducedMerge1701 : Integer.Sparse Master := [(Sum.inr 4844, -10611725918904778752000), (Sum.inr 4851, -3651536391380140032000), (Sum.inr 4852, 25540881314177875968000), (Sum.inr 4853, -8931969569439350784000)]

def originalMerge1701 : Integer.Sparse OriginalKey := originalMerge1699 ++ originalMerge1700

theorem reducedMerge1701Check : reducedMerge1701 = Integer.Sparse.mergeBy masterLess reducedMerge1699 reducedMerge1700 := by decide +kernel

def reducedMerge1702 : Integer.Sparse Master := [(Sum.inr 4819, -9689775870270504960000), (Sum.inr 4821, 24425621100813090816000), (Sum.inr 4830, 4276208522593566720000), (Sum.inr 4836, 14865336275325419520000), (Sum.inr 4844, -10611725918904778752000), (Sum.inr 4851, -3651536391380140032000), (Sum.inr 4852, 25540881314177875968000), (Sum.inr 4853, -8931969569439350784000)]

def originalMerge1702 : Integer.Sparse OriginalKey := originalMerge1698 ++ originalMerge1701

theorem reducedMerge1702Check : reducedMerge1702 = Integer.Sparse.mergeBy masterLess reducedMerge1698 reducedMerge1701 := by decide +kernel

def reducedMerge1703 : Integer.Sparse Master := [(Sum.inr 4793, 2175984329530540032000), (Sum.inr 4795, -657568140574851072000), (Sum.inr 4803, 9126733393928650752000), (Sum.inr 4808, 6795525312677412864000), (Sum.inr 4815, 10203027601367236608000), (Sum.inr 4816, 16684169003853152256000), (Sum.inr 4817, -4302249789556260864000), (Sum.inr 4819, -9689775870270504960000), (Sum.inr 4821, 24425621100813090816000), (Sum.inr 4830, 4276208522593566720000), (Sum.inr 4836, 14865336275325419520000), (Sum.inr 4844, -10611725918904778752000), (Sum.inr 4851, -3651536391380140032000), (Sum.inr 4852, 25540881314177875968000), (Sum.inr 4853, -8931969569439350784000)]

def originalMerge1703 : Integer.Sparse OriginalKey := originalMerge1695 ++ originalMerge1702

theorem reducedMerge1703Check : reducedMerge1703 = Integer.Sparse.mergeBy masterLess reducedMerge1695 reducedMerge1702 := by decide +kernel

def reducedMerge1704 : Integer.Sparse Master := [(Sum.inr 4705, 5611114966542188544000), (Sum.inr 4756, -4157338039461347328000), (Sum.inr 4757, -9921532838029295616000), (Sum.inr 4761, -9955508355996844032000), (Sum.inr 4762, -3552860462980792320000), (Sum.inr 4765, 1531209998492762112000), (Sum.inr 4768, -10577125298707365888000), (Sum.inr 4771, -2142501973049475072000), (Sum.inr 4772, -7032198870020653056000), (Sum.inr 4773, 2026857879932239872000), (Sum.inr 4774, -2118434941245063168000), (Sum.inr 4775, 12472080070696501248000), (Sum.inr 4776, 13670070453059715072000), (Sum.inr 4777, 1819985088072646656000), (Sum.inr 4792, -3874325650567593984000), (Sum.inr 4793, 2175984329530540032000), (Sum.inr 4795, -657568140574851072000), (Sum.inr 4803, 9126733393928650752000), (Sum.inr 4808, 6795525312677412864000), (Sum.inr 4815, 10203027601367236608000), (Sum.inr 4816, 16684169003853152256000), (Sum.inr 4817, -4302249789556260864000), (Sum.inr 4819, -9689775870270504960000), (Sum.inr 4821, 24425621100813090816000), (Sum.inr 4830, 4276208522593566720000), (Sum.inr 4836, 14865336275325419520000), (Sum.inr 4844, -10611725918904778752000), (Sum.inr 4851, -3651536391380140032000), (Sum.inr 4852, 25540881314177875968000), (Sum.inr 4853, -8931969569439350784000)]

def originalMerge1704 : Integer.Sparse OriginalKey := originalMerge1689 ++ originalMerge1703

theorem reducedMerge1704Check : reducedMerge1704 = Integer.Sparse.mergeBy masterLess reducedMerge1689 reducedMerge1703 := by decide +kernel

def reducedMerge1705 : Integer.Sparse Master := [(Sum.inr 4863, 3301651066537377792000), (Sum.inr 4867, 25180426029650411520000)]

def originalMerge1705 : Integer.Sparse OriginalKey := originalTerm1710 ++ originalTerm1711

theorem reducedMerge1705Check : reducedMerge1705 = Integer.Sparse.mergeBy masterLess reducedTerm1710 reducedTerm1711 := by decide +kernel

def reducedMerge1706 : Integer.Sparse Master := [(Sum.inr 4856, 47721697208593809408000), (Sum.inr 4863, 3301651066537377792000), (Sum.inr 4867, 25180426029650411520000)]

def originalMerge1706 : Integer.Sparse OriginalKey := originalTerm1709 ++ originalMerge1705

theorem reducedMerge1706Check : reducedMerge1706 = Integer.Sparse.mergeBy masterLess reducedTerm1709 reducedMerge1705 := by decide +kernel

def reducedMerge1707 : Integer.Sparse Master := [(Sum.inr 4872, -1313798019878486016000), (Sum.inr 4878, 21125648675937189888000)]

def originalMerge1707 : Integer.Sparse OriginalKey := originalTerm1712 ++ originalTerm1713

theorem reducedMerge1707Check : reducedMerge1707 = Integer.Sparse.mergeBy masterLess reducedTerm1712 reducedTerm1713 := by decide +kernel

def reducedMerge1708 : Integer.Sparse Master := [(Sum.inr 4879, 58246227271801110528000), (Sum.inr 4880, 15911341251193995264000)]

def originalMerge1708 : Integer.Sparse OriginalKey := originalTerm1714 ++ originalTerm1715

theorem reducedMerge1708Check : reducedMerge1708 = Integer.Sparse.mergeBy masterLess reducedTerm1714 reducedTerm1715 := by decide +kernel

def reducedMerge1709 : Integer.Sparse Master := [(Sum.inr 4872, -1313798019878486016000), (Sum.inr 4878, 21125648675937189888000), (Sum.inr 4879, 58246227271801110528000), (Sum.inr 4880, 15911341251193995264000)]

def originalMerge1709 : Integer.Sparse OriginalKey := originalMerge1707 ++ originalMerge1708

theorem reducedMerge1709Check : reducedMerge1709 = Integer.Sparse.mergeBy masterLess reducedMerge1707 reducedMerge1708 := by decide +kernel

def reducedMerge1710 : Integer.Sparse Master := [(Sum.inr 4856, 47721697208593809408000), (Sum.inr 4863, 3301651066537377792000), (Sum.inr 4867, 25180426029650411520000), (Sum.inr 4872, -1313798019878486016000), (Sum.inr 4878, 21125648675937189888000), (Sum.inr 4879, 58246227271801110528000), (Sum.inr 4880, 15911341251193995264000)]

def originalMerge1710 : Integer.Sparse OriginalKey := originalMerge1706 ++ originalMerge1709

theorem reducedMerge1710Check : reducedMerge1710 = Integer.Sparse.mergeBy masterLess reducedMerge1706 reducedMerge1709 := by decide +kernel

def reducedMerge1711 : Integer.Sparse Master := [(Sum.inr 4881, 9824764650698833920000), (Sum.inr 4884, 19178062513867063296000)]

def originalMerge1711 : Integer.Sparse OriginalKey := originalTerm1716 ++ originalTerm1717

theorem reducedMerge1711Check : reducedMerge1711 = Integer.Sparse.mergeBy masterLess reducedTerm1716 reducedTerm1717 := by decide +kernel

def reducedMerge1712 : Integer.Sparse Master := [(Sum.inr 4885, -1093534813718839296000), (Sum.inr 4886, 22163666956793413632000)]

def originalMerge1712 : Integer.Sparse OriginalKey := originalTerm1718 ++ originalTerm1719

theorem reducedMerge1712Check : reducedMerge1712 = Integer.Sparse.mergeBy masterLess reducedTerm1718 reducedTerm1719 := by decide +kernel

def reducedMerge1713 : Integer.Sparse Master := [(Sum.inr 4881, 9824764650698833920000), (Sum.inr 4884, 19178062513867063296000), (Sum.inr 4885, -1093534813718839296000), (Sum.inr 4886, 22163666956793413632000)]

def originalMerge1713 : Integer.Sparse OriginalKey := originalMerge1711 ++ originalMerge1712

theorem reducedMerge1713Check : reducedMerge1713 = Integer.Sparse.mergeBy masterLess reducedMerge1711 reducedMerge1712 := by decide +kernel

def reducedMerge1714 : Integer.Sparse Master := [(Sum.inr 2243, 9372634478002962432000), (Sum.inr 2244, 2883452798765629440000), (Sum.inr 2262, 2883452798765629440000)]

def originalMerge1714 : Integer.Sparse OriginalKey := originalTerm1720 ++ originalTerm1721

theorem reducedMerge1714Check : reducedMerge1714 = Integer.Sparse.mergeBy masterLess reducedTerm1720 reducedTerm1721 := by decide +kernel

def reducedMerge1715 : Integer.Sparse Master := [(Sum.inr 2245, -4057256850042912768000), (Sum.inr 2247, -757011477946171392000), (Sum.inr 2277, -4057256850042912768000), (Sum.inr 2290, -757011477946171392000)]

def originalMerge1715 : Integer.Sparse OriginalKey := originalTerm1722 ++ originalTerm1723

theorem reducedMerge1715Check : reducedMerge1715 = Integer.Sparse.mergeBy masterLess reducedTerm1722 reducedTerm1723 := by decide +kernel

def reducedMerge1716 : Integer.Sparse Master := [(Sum.inr 2243, 9372634478002962432000), (Sum.inr 2244, 2883452798765629440000), (Sum.inr 2245, -4057256850042912768000), (Sum.inr 2247, -757011477946171392000), (Sum.inr 2262, 2883452798765629440000), (Sum.inr 2277, -4057256850042912768000), (Sum.inr 2290, -757011477946171392000)]

def originalMerge1716 : Integer.Sparse OriginalKey := originalMerge1714 ++ originalMerge1715

theorem reducedMerge1716Check : reducedMerge1716 = Integer.Sparse.mergeBy masterLess reducedMerge1714 reducedMerge1715 := by decide +kernel

def reducedMerge1717 : Integer.Sparse Master := [(Sum.inr 2243, 9372634478002962432000), (Sum.inr 2244, 2883452798765629440000), (Sum.inr 2245, -4057256850042912768000), (Sum.inr 2247, -757011477946171392000), (Sum.inr 2262, 2883452798765629440000), (Sum.inr 2277, -4057256850042912768000), (Sum.inr 2290, -757011477946171392000), (Sum.inr 4881, 9824764650698833920000), (Sum.inr 4884, 19178062513867063296000), (Sum.inr 4885, -1093534813718839296000), (Sum.inr 4886, 22163666956793413632000)]

def originalMerge1717 : Integer.Sparse OriginalKey := originalMerge1713 ++ originalMerge1716

theorem reducedMerge1717Check : reducedMerge1717 = Integer.Sparse.mergeBy masterLess reducedMerge1713 reducedMerge1716 := by decide +kernel

def reducedMerge1718 : Integer.Sparse Master := [(Sum.inr 2243, 9372634478002962432000), (Sum.inr 2244, 2883452798765629440000), (Sum.inr 2245, -4057256850042912768000), (Sum.inr 2247, -757011477946171392000), (Sum.inr 2262, 2883452798765629440000), (Sum.inr 2277, -4057256850042912768000), (Sum.inr 2290, -757011477946171392000), (Sum.inr 4856, 47721697208593809408000), (Sum.inr 4863, 3301651066537377792000), (Sum.inr 4867, 25180426029650411520000), (Sum.inr 4872, -1313798019878486016000), (Sum.inr 4878, 21125648675937189888000), (Sum.inr 4879, 58246227271801110528000), (Sum.inr 4880, 15911341251193995264000), (Sum.inr 4881, 9824764650698833920000), (Sum.inr 4884, 19178062513867063296000), (Sum.inr 4885, -1093534813718839296000), (Sum.inr 4886, 22163666956793413632000)]

def originalMerge1718 : Integer.Sparse OriginalKey := originalMerge1710 ++ originalMerge1717

theorem reducedMerge1718Check : reducedMerge1718 = Integer.Sparse.mergeBy masterLess reducedMerge1710 reducedMerge1717 := by decide +kernel

def reducedMerge1719 : Integer.Sparse Master := [(Sum.inr 4892, 6273766636234997760000)]

def originalMerge1719 : Integer.Sparse OriginalKey := originalTerm1725 ++ originalTerm1726

theorem reducedMerge1719Check : reducedMerge1719 = Integer.Sparse.mergeBy masterLess reducedTerm1725 reducedTerm1726 := by decide +kernel

def reducedMerge1720 : Integer.Sparse Master := [(Sum.inr 4891, 39451307385118261248000), (Sum.inr 4892, 6273766636234997760000)]

def originalMerge1720 : Integer.Sparse OriginalKey := originalTerm1724 ++ originalMerge1719

theorem reducedMerge1720Check : reducedMerge1720 = Integer.Sparse.mergeBy masterLess reducedTerm1724 reducedMerge1719 := by decide +kernel

def reducedMerge1721 : Integer.Sparse Master := []

def originalMerge1721 : Integer.Sparse OriginalKey := originalTerm1727 ++ originalTerm1728

theorem reducedMerge1721Check : reducedMerge1721 = Integer.Sparse.mergeBy masterLess reducedTerm1727 reducedTerm1728 := by decide +kernel

def reducedMerge1722 : Integer.Sparse Master := [(Sum.inr 2266, -1722459352110465024000), (Sum.inr 2278, -1722459352110465024000)]

def originalMerge1722 : Integer.Sparse OriginalKey := originalTerm1729 ++ originalTerm1730

theorem reducedMerge1722Check : reducedMerge1722 = Integer.Sparse.mergeBy masterLess reducedTerm1729 reducedTerm1730 := by decide +kernel

def reducedMerge1723 : Integer.Sparse Master := [(Sum.inr 2266, -1722459352110465024000), (Sum.inr 2278, -1722459352110465024000)]

def originalMerge1723 : Integer.Sparse OriginalKey := originalMerge1721 ++ originalMerge1722

theorem reducedMerge1723Check : reducedMerge1723 = Integer.Sparse.mergeBy masterLess reducedMerge1721 reducedMerge1722 := by decide +kernel

def reducedMerge1724 : Integer.Sparse Master := [(Sum.inr 2266, -1722459352110465024000), (Sum.inr 2278, -1722459352110465024000), (Sum.inr 4891, 39451307385118261248000), (Sum.inr 4892, 6273766636234997760000)]

def originalMerge1724 : Integer.Sparse OriginalKey := originalMerge1720 ++ originalMerge1723

theorem reducedMerge1724Check : reducedMerge1724 = Integer.Sparse.mergeBy masterLess reducedMerge1720 reducedMerge1723 := by decide +kernel

def reducedMerge1725 : Integer.Sparse Master := [(Sum.inr 2279, -6553562748283256832000), (Sum.inr 2281, 1215313374856347648000), (Sum.inr 2294, 1215313374856347648000)]

def originalMerge1725 : Integer.Sparse OriginalKey := originalTerm1731 ++ originalTerm1732

theorem reducedMerge1725Check : reducedMerge1725 = Integer.Sparse.mergeBy masterLess reducedTerm1731 reducedTerm1732 := by decide +kernel

def reducedMerge1726 : Integer.Sparse Master := [(Sum.inr 4900, -1647434443064868864000)]

def originalMerge1726 : Integer.Sparse OriginalKey := originalTerm1733 ++ originalTerm1734

theorem reducedMerge1726Check : reducedMerge1726 = Integer.Sparse.mergeBy masterLess reducedTerm1733 reducedTerm1734 := by decide +kernel

def reducedMerge1727 : Integer.Sparse Master := [(Sum.inr 2279, -6553562748283256832000), (Sum.inr 2281, 1215313374856347648000), (Sum.inr 2294, 1215313374856347648000), (Sum.inr 4900, -1647434443064868864000)]

def originalMerge1727 : Integer.Sparse OriginalKey := originalMerge1725 ++ originalMerge1726

theorem reducedMerge1727Check : reducedMerge1727 = Integer.Sparse.mergeBy masterLess reducedMerge1725 reducedMerge1726 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
