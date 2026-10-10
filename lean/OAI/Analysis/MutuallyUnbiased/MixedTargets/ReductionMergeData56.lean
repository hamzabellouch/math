import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData56
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData57
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData54
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData55

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge1792 : Integer.Sparse Master := [(Sum.inr 5090, -18907268073784344576000), (Sum.inr 5097, 1037405314429747200000), (Sum.inr 5103, 6797176070885867520000), (Sum.inr 5112, -6581206302477778944000), (Sum.inr 5116, 1658951609427689472000), (Sum.inr 5128, -2003708022304407552000), (Sum.inr 5129, 6585849716091125760000), (Sum.inr 5138, 12127532681381806080000), (Sum.inr 5139, -49178321197557350400000), (Sum.inr 5140, -17211622947812278272000), (Sum.inr 5144, 3601578321337909248000), (Sum.inr 5145, 11949080038817660928000), (Sum.inr 5147, 26234697751049797632000), (Sum.inr 5150, -1803031804161294336000), (Sum.inr 5151, -1219510267957739520000), (Sum.inr 5160, 34816216585195487232000), (Sum.inr 5161, 758866233230622720000), (Sum.inr 5164, 22613357947383447552000), (Sum.inr 5173, 13429246920497823744000), (Sum.inr 5175, -4064171765800108032000), (Sum.inr 5184, -4291086391493787648000), (Sum.inr 5185, 9726337145084313600000), (Sum.inr 5187, 30794924164413652992000), (Sum.inr 5188, 5010817572354392064000), (Sum.inr 5189, -5752353613478363136000), (Sum.inr 5197, 7848902981735940096000), (Sum.inr 5198, 9732294813230825472000), (Sum.inr 5199, 55912898410749886464000), (Sum.inr 5201, 18198562535170375680000), (Sum.inr 5205, 16689362260860076032000)]

def originalMerge1792 : Integer.Sparse OriginalKey := originalMerge1777 ++ originalMerge1791

theorem reducedMerge1792Check : reducedMerge1792 = Integer.Sparse.mergeBy masterLess reducedMerge1777 reducedMerge1791 := by decide +kernel

def reducedMerge1793 : Integer.Sparse Master := [(Sum.inr 4935, 3259996962101526528000), (Sum.inr 4942, 13377767853843283968000), (Sum.inr 4944, -11958904477318643712000), (Sum.inr 4945, -127393862378323968000), (Sum.inr 4951, -1418863376524640256000), (Sum.inr 4954, 19134699747307683840000), (Sum.inr 4955, -5686906574229995520000), (Sum.inr 4956, -5324013064735948800000), (Sum.inr 4957, 29561192263900200960000), (Sum.inr 4958, -1083441906686361600000), (Sum.inr 4959, -12567225913008979968000), (Sum.inr 4963, -4535331438044381184000), (Sum.inr 4964, -23732159479676928000000), (Sum.inr 4965, -18533635534082801664000), (Sum.inr 4966, -22975789646216429568000), (Sum.inr 4975, -8499226830254899200000), (Sum.inr 4976, -16875309640898838528000), (Sum.inr 5034, 2978479197322739712000), (Sum.inr 5035, 16389072352617431040000), (Sum.inr 5040, 23233730127482585088000), (Sum.inr 5041, 92883104915521536000), (Sum.inr 5042, -9483177650962563072000), (Sum.inr 5043, -2890541624919588864000), (Sum.inr 5044, -7341806534933348352000), (Sum.inr 5065, -14530652001365262336000), (Sum.inr 5067, 7427653233623433216000), (Sum.inr 5074, -12264455942580731904000), (Sum.inr 5085, 8916509350529335296000), (Sum.inr 5086, 12233494979845816320000), (Sum.inr 5087, 2026846219688607744000), (Sum.inr 5090, -18907268073784344576000), (Sum.inr 5097, 1037405314429747200000), (Sum.inr 5103, 6797176070885867520000), (Sum.inr 5112, -6581206302477778944000), (Sum.inr 5116, 1658951609427689472000), (Sum.inr 5128, -2003708022304407552000), (Sum.inr 5129, 6585849716091125760000), (Sum.inr 5138, 12127532681381806080000), (Sum.inr 5139, -49178321197557350400000), (Sum.inr 5140, -17211622947812278272000), (Sum.inr 5144, 3601578321337909248000), (Sum.inr 5145, 11949080038817660928000), (Sum.inr 5147, 26234697751049797632000), (Sum.inr 5150, -1803031804161294336000), (Sum.inr 5151, -1219510267957739520000), (Sum.inr 5160, 34816216585195487232000), (Sum.inr 5161, 758866233230622720000), (Sum.inr 5164, 22613357947383447552000), (Sum.inr 5173, 13429246920497823744000), (Sum.inr 5175, -4064171765800108032000), (Sum.inr 5184, -4291086391493787648000), (Sum.inr 5185, 9726337145084313600000), (Sum.inr 5187, 30794924164413652992000), (Sum.inr 5188, 5010817572354392064000), (Sum.inr 5189, -5752353613478363136000), (Sum.inr 5197, 7848902981735940096000), (Sum.inr 5198, 9732294813230825472000), (Sum.inr 5199, 55912898410749886464000), (Sum.inr 5201, 18198562535170375680000), (Sum.inr 5205, 16689362260860076032000)]

def originalMerge1793 : Integer.Sparse OriginalKey := originalMerge1763 ++ originalMerge1792

theorem reducedMerge1793Check : reducedMerge1793 = Integer.Sparse.mergeBy masterLess reducedMerge1763 reducedMerge1792 := by decide +kernel

def reducedMerge1794 : Integer.Sparse Master := [(Sum.inr 2243, 9372634478002962432000), (Sum.inr 2244, 2883452798765629440000), (Sum.inr 2245, -4057256850042912768000), (Sum.inr 2247, -757011477946171392000), (Sum.inr 2262, 2883452798765629440000), (Sum.inr 2266, -1722459352110465024000), (Sum.inr 2277, -4057256850042912768000), (Sum.inr 2278, -1722459352110465024000), (Sum.inr 2279, -6553562748283256832000), (Sum.inr 2281, 1215313374856347648000), (Sum.inr 2290, -757011477946171392000), (Sum.inr 2294, 1215313374856347648000), (Sum.inr 4705, 5611114966542188544000), (Sum.inr 4756, -4157338039461347328000), (Sum.inr 4757, -9921532838029295616000), (Sum.inr 4761, -9955508355996844032000), (Sum.inr 4762, -3552860462980792320000), (Sum.inr 4765, 1531209998492762112000), (Sum.inr 4768, -10577125298707365888000), (Sum.inr 4771, -2142501973049475072000), (Sum.inr 4772, -7032198870020653056000), (Sum.inr 4773, 2026857879932239872000), (Sum.inr 4774, -2118434941245063168000), (Sum.inr 4775, 12472080070696501248000), (Sum.inr 4776, 13670070453059715072000), (Sum.inr 4777, 1819985088072646656000), (Sum.inr 4792, -3874325650567593984000), (Sum.inr 4793, 2175984329530540032000), (Sum.inr 4795, -657568140574851072000), (Sum.inr 4803, 9126733393928650752000), (Sum.inr 4808, 6795525312677412864000), (Sum.inr 4815, 10203027601367236608000), (Sum.inr 4816, 16684169003853152256000), (Sum.inr 4817, -4302249789556260864000), (Sum.inr 4819, -9689775870270504960000), (Sum.inr 4821, 24425621100813090816000), (Sum.inr 4830, 4276208522593566720000), (Sum.inr 4836, 14865336275325419520000), (Sum.inr 4844, -10611725918904778752000), (Sum.inr 4851, -3651536391380140032000), (Sum.inr 4852, 25540881314177875968000), (Sum.inr 4853, -8931969569439350784000), (Sum.inr 4856, 47721697208593809408000), (Sum.inr 4863, 3301651066537377792000), (Sum.inr 4867, 25180426029650411520000), (Sum.inr 4872, -1313798019878486016000), (Sum.inr 4878, 21125648675937189888000), (Sum.inr 4879, 58246227271801110528000), (Sum.inr 4880, 15911341251193995264000), (Sum.inr 4881, 9824764650698833920000), (Sum.inr 4884, 19178062513867063296000), (Sum.inr 4885, -1093534813718839296000), (Sum.inr 4886, 22163666956793413632000), (Sum.inr 4891, 39451307385118261248000), (Sum.inr 4892, 6273766636234997760000), (Sum.inr 4900, -1647434443064868864000), (Sum.inr 4930, -7941663994208845824000), (Sum.inr 4931, 2611987518440079360000), (Sum.inr 4933, 1421670070005792768000), (Sum.inr 4934, -6239960297145630720000), (Sum.inr 4935, 3259996962101526528000), (Sum.inr 4942, 13377767853843283968000), (Sum.inr 4944, -11958904477318643712000), (Sum.inr 4945, -127393862378323968000), (Sum.inr 4951, -1418863376524640256000), (Sum.inr 4954, 19134699747307683840000), (Sum.inr 4955, -5686906574229995520000), (Sum.inr 4956, -5324013064735948800000), (Sum.inr 4957, 29561192263900200960000), (Sum.inr 4958, -1083441906686361600000), (Sum.inr 4959, -12567225913008979968000), (Sum.inr 4963, -4535331438044381184000), (Sum.inr 4964, -23732159479676928000000), (Sum.inr 4965, -18533635534082801664000), (Sum.inr 4966, -22975789646216429568000), (Sum.inr 4975, -8499226830254899200000), (Sum.inr 4976, -16875309640898838528000), (Sum.inr 5034, 2978479197322739712000), (Sum.inr 5035, 16389072352617431040000), (Sum.inr 5040, 23233730127482585088000), (Sum.inr 5041, 92883104915521536000), (Sum.inr 5042, -9483177650962563072000), (Sum.inr 5043, -2890541624919588864000), (Sum.inr 5044, -7341806534933348352000), (Sum.inr 5065, -14530652001365262336000), (Sum.inr 5067, 7427653233623433216000), (Sum.inr 5074, -12264455942580731904000), (Sum.inr 5085, 8916509350529335296000), (Sum.inr 5086, 12233494979845816320000), (Sum.inr 5087, 2026846219688607744000), (Sum.inr 5090, -18907268073784344576000), (Sum.inr 5097, 1037405314429747200000), (Sum.inr 5103, 6797176070885867520000), (Sum.inr 5112, -6581206302477778944000), (Sum.inr 5116, 1658951609427689472000), (Sum.inr 5128, -2003708022304407552000), (Sum.inr 5129, 6585849716091125760000), (Sum.inr 5138, 12127532681381806080000), (Sum.inr 5139, -49178321197557350400000), (Sum.inr 5140, -17211622947812278272000), (Sum.inr 5144, 3601578321337909248000), (Sum.inr 5145, 11949080038817660928000), (Sum.inr 5147, 26234697751049797632000), (Sum.inr 5150, -1803031804161294336000), (Sum.inr 5151, -1219510267957739520000), (Sum.inr 5160, 34816216585195487232000), (Sum.inr 5161, 758866233230622720000), (Sum.inr 5164, 22613357947383447552000), (Sum.inr 5173, 13429246920497823744000), (Sum.inr 5175, -4064171765800108032000), (Sum.inr 5184, -4291086391493787648000), (Sum.inr 5185, 9726337145084313600000), (Sum.inr 5187, 30794924164413652992000), (Sum.inr 5188, 5010817572354392064000), (Sum.inr 5189, -5752353613478363136000), (Sum.inr 5197, 7848902981735940096000), (Sum.inr 5198, 9732294813230825472000), (Sum.inr 5199, 55912898410749886464000), (Sum.inr 5201, 18198562535170375680000), (Sum.inr 5205, 16689362260860076032000)]

def originalMerge1794 : Integer.Sparse OriginalKey := originalMerge1734 ++ originalMerge1793

theorem reducedMerge1794Check : reducedMerge1794 = Integer.Sparse.mergeBy masterLess reducedMerge1734 reducedMerge1793 := by decide +kernel

def reducedMerge1795 : Integer.Sparse Master := [(Sum.inr 5215, -11601654236794847232000), (Sum.inr 5216, -238272485558059008000)]

def originalMerge1795 : Integer.Sparse OriginalKey := originalTerm1800 ++ originalTerm1801

theorem reducedMerge1795Check : reducedMerge1795 = Integer.Sparse.mergeBy masterLess reducedTerm1800 reducedTerm1801 := by decide +kernel

def reducedMerge1796 : Integer.Sparse Master := [(Sum.inr 5206, 11015478679850975232000), (Sum.inr 5215, -11601654236794847232000), (Sum.inr 5216, -238272485558059008000)]

def originalMerge1796 : Integer.Sparse OriginalKey := originalTerm1799 ++ originalMerge1795

theorem reducedMerge1796Check : reducedMerge1796 = Integer.Sparse.mergeBy masterLess reducedTerm1799 reducedMerge1795 := by decide +kernel

def reducedMerge1797 : Integer.Sparse Master := [(Sum.inr 5217, 9806018085126144000000), (Sum.inr 5219, 10171942174410670080000)]

def originalMerge1797 : Integer.Sparse OriginalKey := originalTerm1802 ++ originalTerm1803

theorem reducedMerge1797Check : reducedMerge1797 = Integer.Sparse.mergeBy masterLess reducedTerm1802 reducedTerm1803 := by decide +kernel

def reducedMerge1798 : Integer.Sparse Master := [(Sum.inr 5220, -381292928484507648000), (Sum.inr 5222, 3552860462980792320000)]

def originalMerge1798 : Integer.Sparse OriginalKey := originalTerm1804 ++ originalTerm1805

theorem reducedMerge1798Check : reducedMerge1798 = Integer.Sparse.mergeBy masterLess reducedTerm1804 reducedTerm1805 := by decide +kernel

def reducedMerge1799 : Integer.Sparse Master := [(Sum.inr 5217, 9806018085126144000000), (Sum.inr 5219, 10171942174410670080000), (Sum.inr 5220, -381292928484507648000), (Sum.inr 5222, 3552860462980792320000)]

def originalMerge1799 : Integer.Sparse OriginalKey := originalMerge1797 ++ originalMerge1798

theorem reducedMerge1799Check : reducedMerge1799 = Integer.Sparse.mergeBy masterLess reducedMerge1797 reducedMerge1798 := by decide +kernel

def reducedMerge1800 : Integer.Sparse Master := [(Sum.inr 5206, 11015478679850975232000), (Sum.inr 5215, -11601654236794847232000), (Sum.inr 5216, -238272485558059008000), (Sum.inr 5217, 9806018085126144000000), (Sum.inr 5219, 10171942174410670080000), (Sum.inr 5220, -381292928484507648000), (Sum.inr 5222, 3552860462980792320000)]

def originalMerge1800 : Integer.Sparse OriginalKey := originalMerge1796 ++ originalMerge1799

theorem reducedMerge1800Check : reducedMerge1800 = Integer.Sparse.mergeBy masterLess reducedMerge1796 reducedMerge1799 := by decide +kernel

def reducedMerge1801 : Integer.Sparse Master := [(Sum.inr 5226, 7805365883397734400000), (Sum.inr 5229, 12678992556746342400000)]

def originalMerge1801 : Integer.Sparse OriginalKey := originalTerm1806 ++ originalTerm1807

theorem reducedMerge1801Check : reducedMerge1801 = Integer.Sparse.mergeBy masterLess reducedTerm1806 reducedTerm1807 := by decide +kernel

def reducedMerge1802 : Integer.Sparse Master := [(Sum.inr 5231, 8788145924144627712000), (Sum.inr 5232, 14640885025087684608000)]

def originalMerge1802 : Integer.Sparse OriginalKey := originalTerm1808 ++ originalTerm1809

theorem reducedMerge1802Check : reducedMerge1802 = Integer.Sparse.mergeBy masterLess reducedTerm1808 reducedTerm1809 := by decide +kernel

def reducedMerge1803 : Integer.Sparse Master := [(Sum.inr 5226, 7805365883397734400000), (Sum.inr 5229, 12678992556746342400000), (Sum.inr 5231, 8788145924144627712000), (Sum.inr 5232, 14640885025087684608000)]

def originalMerge1803 : Integer.Sparse OriginalKey := originalMerge1801 ++ originalMerge1802

theorem reducedMerge1803Check : reducedMerge1803 = Integer.Sparse.mergeBy masterLess reducedMerge1801 reducedMerge1802 := by decide +kernel

def reducedMerge1804 : Integer.Sparse Master := [(Sum.inr 5233, 4998927687537917952000), (Sum.inr 5235, 1313082224189374464000)]

def originalMerge1804 : Integer.Sparse OriginalKey := originalTerm1810 ++ originalTerm1811

theorem reducedMerge1804Check : reducedMerge1804 = Integer.Sparse.mergeBy masterLess reducedTerm1810 reducedTerm1811 := by decide +kernel

def reducedMerge1805 : Integer.Sparse Master := [(Sum.inr 5236, -9806018085126144000000), (Sum.inr 5243, 2663428588472107008000)]

def originalMerge1805 : Integer.Sparse OriginalKey := originalTerm1812 ++ originalTerm1813

theorem reducedMerge1805Check : reducedMerge1805 = Integer.Sparse.mergeBy masterLess reducedTerm1812 reducedTerm1813 := by decide +kernel

def reducedMerge1806 : Integer.Sparse Master := [(Sum.inr 5233, 4998927687537917952000), (Sum.inr 5235, 1313082224189374464000), (Sum.inr 5236, -9806018085126144000000), (Sum.inr 5243, 2663428588472107008000)]

def originalMerge1806 : Integer.Sparse OriginalKey := originalMerge1804 ++ originalMerge1805

theorem reducedMerge1806Check : reducedMerge1806 = Integer.Sparse.mergeBy masterLess reducedMerge1804 reducedMerge1805 := by decide +kernel

def reducedMerge1807 : Integer.Sparse Master := [(Sum.inr 5226, 7805365883397734400000), (Sum.inr 5229, 12678992556746342400000), (Sum.inr 5231, 8788145924144627712000), (Sum.inr 5232, 14640885025087684608000), (Sum.inr 5233, 4998927687537917952000), (Sum.inr 5235, 1313082224189374464000), (Sum.inr 5236, -9806018085126144000000), (Sum.inr 5243, 2663428588472107008000)]

def originalMerge1807 : Integer.Sparse OriginalKey := originalMerge1803 ++ originalMerge1806

theorem reducedMerge1807Check : reducedMerge1807 = Integer.Sparse.mergeBy masterLess reducedMerge1803 reducedMerge1806 := by decide +kernel

def reducedMerge1808 : Integer.Sparse Master := [(Sum.inr 5206, 11015478679850975232000), (Sum.inr 5215, -11601654236794847232000), (Sum.inr 5216, -238272485558059008000), (Sum.inr 5217, 9806018085126144000000), (Sum.inr 5219, 10171942174410670080000), (Sum.inr 5220, -381292928484507648000), (Sum.inr 5222, 3552860462980792320000), (Sum.inr 5226, 7805365883397734400000), (Sum.inr 5229, 12678992556746342400000), (Sum.inr 5231, 8788145924144627712000), (Sum.inr 5232, 14640885025087684608000), (Sum.inr 5233, 4998927687537917952000), (Sum.inr 5235, 1313082224189374464000), (Sum.inr 5236, -9806018085126144000000), (Sum.inr 5243, 2663428588472107008000)]

def originalMerge1808 : Integer.Sparse OriginalKey := originalMerge1800 ++ originalMerge1807

theorem reducedMerge1808Check : reducedMerge1808 = Integer.Sparse.mergeBy masterLess reducedMerge1800 reducedMerge1807 := by decide +kernel

def reducedMerge1809 : Integer.Sparse Master := [(Sum.inr 5249, 8721406518151348224000)]

def originalMerge1809 : Integer.Sparse OriginalKey := originalTerm1815 ++ originalTerm1816

theorem reducedMerge1809Check : reducedMerge1809 = Integer.Sparse.mergeBy masterLess reducedTerm1815 reducedTerm1816 := by decide +kernel

def reducedMerge1810 : Integer.Sparse Master := [(Sum.inr 5244, -12840196478415667200000), (Sum.inr 5249, 8721406518151348224000)]

def originalMerge1810 : Integer.Sparse OriginalKey := originalTerm1814 ++ originalMerge1809

theorem reducedMerge1810Check : reducedMerge1810 = Integer.Sparse.mergeBy masterLess reducedTerm1814 reducedMerge1809 := by decide +kernel

def reducedMerge1811 : Integer.Sparse Master := [(Sum.inr 5251, 20804483957839626240000), (Sum.inr 5252, -15787189652894908416000)]

def originalMerge1811 : Integer.Sparse OriginalKey := originalTerm1817 ++ originalTerm1818

theorem reducedMerge1811Check : reducedMerge1811 = Integer.Sparse.mergeBy masterLess reducedTerm1817 reducedTerm1818 := by decide +kernel

def reducedMerge1812 : Integer.Sparse Master := [(Sum.inr 5254, -18103702594567274496000), (Sum.inr 5255, 10628823676665987072000)]

def originalMerge1812 : Integer.Sparse OriginalKey := originalTerm1819 ++ originalTerm1820

theorem reducedMerge1812Check : reducedMerge1812 = Integer.Sparse.mergeBy masterLess reducedTerm1819 reducedTerm1820 := by decide +kernel

def reducedMerge1813 : Integer.Sparse Master := [(Sum.inr 5251, 20804483957839626240000), (Sum.inr 5252, -15787189652894908416000), (Sum.inr 5254, -18103702594567274496000), (Sum.inr 5255, 10628823676665987072000)]

def originalMerge1813 : Integer.Sparse OriginalKey := originalMerge1811 ++ originalMerge1812

theorem reducedMerge1813Check : reducedMerge1813 = Integer.Sparse.mergeBy masterLess reducedMerge1811 reducedMerge1812 := by decide +kernel

def reducedMerge1814 : Integer.Sparse Master := [(Sum.inr 5244, -12840196478415667200000), (Sum.inr 5249, 8721406518151348224000), (Sum.inr 5251, 20804483957839626240000), (Sum.inr 5252, -15787189652894908416000), (Sum.inr 5254, -18103702594567274496000), (Sum.inr 5255, 10628823676665987072000)]

def originalMerge1814 : Integer.Sparse OriginalKey := originalMerge1810 ++ originalMerge1813

theorem reducedMerge1814Check : reducedMerge1814 = Integer.Sparse.mergeBy masterLess reducedMerge1810 reducedMerge1813 := by decide +kernel

def reducedMerge1815 : Integer.Sparse Master := [(Sum.inr 2721, 3811256349900668928000), (Sum.inr 3532, 3811256349900668928000)]

def originalMerge1815 : Integer.Sparse OriginalKey := originalTerm1821 ++ originalTerm1822

theorem reducedMerge1815Check : reducedMerge1815 = Integer.Sparse.mergeBy masterLess reducedTerm1821 reducedTerm1822 := by decide +kernel

def reducedMerge1816 : Integer.Sparse Master := [(Sum.inr 2722, 5665773180262809600000), (Sum.inr 2723, 1418854997041348608000), (Sum.inr 3533, 5665773180262809600000), (Sum.inr 3544, 1418854997041348608000)]

def originalMerge1816 : Integer.Sparse OriginalKey := originalTerm1823 ++ originalTerm1824

theorem reducedMerge1816Check : reducedMerge1816 = Integer.Sparse.mergeBy masterLess reducedTerm1823 reducedTerm1824 := by decide +kernel

def reducedMerge1817 : Integer.Sparse Master := [(Sum.inr 2721, 3811256349900668928000), (Sum.inr 2722, 5665773180262809600000), (Sum.inr 2723, 1418854997041348608000), (Sum.inr 3532, 3811256349900668928000), (Sum.inr 3533, 5665773180262809600000), (Sum.inr 3544, 1418854997041348608000)]

def originalMerge1817 : Integer.Sparse OriginalKey := originalMerge1815 ++ originalMerge1816

theorem reducedMerge1817Check : reducedMerge1817 = Integer.Sparse.mergeBy masterLess reducedMerge1815 reducedMerge1816 := by decide +kernel

def reducedMerge1818 : Integer.Sparse Master := [(Sum.inr 5260, 9126071378630148096000), (Sum.inr 5263, -16830413886397612032000)]

def originalMerge1818 : Integer.Sparse OriginalKey := originalTerm1825 ++ originalTerm1826

theorem reducedMerge1818Check : reducedMerge1818 = Integer.Sparse.mergeBy masterLess reducedTerm1825 reducedTerm1826 := by decide +kernel

def reducedMerge1819 : Integer.Sparse Master := [(Sum.inr 5264, 642323079345733632000), (Sum.inr 5265, -25288345262529183744000)]

def originalMerge1819 : Integer.Sparse OriginalKey := originalTerm1827 ++ originalTerm1828

theorem reducedMerge1819Check : reducedMerge1819 = Integer.Sparse.mergeBy masterLess reducedTerm1827 reducedTerm1828 := by decide +kernel

def reducedMerge1820 : Integer.Sparse Master := [(Sum.inr 5260, 9126071378630148096000), (Sum.inr 5263, -16830413886397612032000), (Sum.inr 5264, 642323079345733632000), (Sum.inr 5265, -25288345262529183744000)]

def originalMerge1820 : Integer.Sparse OriginalKey := originalMerge1818 ++ originalMerge1819

theorem reducedMerge1820Check : reducedMerge1820 = Integer.Sparse.mergeBy masterLess reducedMerge1818 reducedMerge1819 := by decide +kernel

def reducedMerge1821 : Integer.Sparse Master := [(Sum.inr 2721, 3811256349900668928000), (Sum.inr 2722, 5665773180262809600000), (Sum.inr 2723, 1418854997041348608000), (Sum.inr 3532, 3811256349900668928000), (Sum.inr 3533, 5665773180262809600000), (Sum.inr 3544, 1418854997041348608000), (Sum.inr 5260, 9126071378630148096000), (Sum.inr 5263, -16830413886397612032000), (Sum.inr 5264, 642323079345733632000), (Sum.inr 5265, -25288345262529183744000)]

def originalMerge1821 : Integer.Sparse OriginalKey := originalMerge1817 ++ originalMerge1820

theorem reducedMerge1821Check : reducedMerge1821 = Integer.Sparse.mergeBy masterLess reducedMerge1817 reducedMerge1820 := by decide +kernel

def reducedMerge1822 : Integer.Sparse Master := [(Sum.inr 2721, 3811256349900668928000), (Sum.inr 2722, 5665773180262809600000), (Sum.inr 2723, 1418854997041348608000), (Sum.inr 3532, 3811256349900668928000), (Sum.inr 3533, 5665773180262809600000), (Sum.inr 3544, 1418854997041348608000), (Sum.inr 5244, -12840196478415667200000), (Sum.inr 5249, 8721406518151348224000), (Sum.inr 5251, 20804483957839626240000), (Sum.inr 5252, -15787189652894908416000), (Sum.inr 5254, -18103702594567274496000), (Sum.inr 5255, 10628823676665987072000), (Sum.inr 5260, 9126071378630148096000), (Sum.inr 5263, -16830413886397612032000), (Sum.inr 5264, 642323079345733632000), (Sum.inr 5265, -25288345262529183744000)]

def originalMerge1822 : Integer.Sparse OriginalKey := originalMerge1814 ++ originalMerge1821

theorem reducedMerge1822Check : reducedMerge1822 = Integer.Sparse.mergeBy masterLess reducedMerge1814 reducedMerge1821 := by decide +kernel

def reducedMerge1823 : Integer.Sparse Master := [(Sum.inr 2721, 3811256349900668928000), (Sum.inr 2722, 5665773180262809600000), (Sum.inr 2723, 1418854997041348608000), (Sum.inr 3532, 3811256349900668928000), (Sum.inr 3533, 5665773180262809600000), (Sum.inr 3544, 1418854997041348608000), (Sum.inr 5206, 11015478679850975232000), (Sum.inr 5215, -11601654236794847232000), (Sum.inr 5216, -238272485558059008000), (Sum.inr 5217, 9806018085126144000000), (Sum.inr 5219, 10171942174410670080000), (Sum.inr 5220, -381292928484507648000), (Sum.inr 5222, 3552860462980792320000), (Sum.inr 5226, 7805365883397734400000), (Sum.inr 5229, 12678992556746342400000), (Sum.inr 5231, 8788145924144627712000), (Sum.inr 5232, 14640885025087684608000), (Sum.inr 5233, 4998927687537917952000), (Sum.inr 5235, 1313082224189374464000), (Sum.inr 5236, -9806018085126144000000), (Sum.inr 5243, 2663428588472107008000), (Sum.inr 5244, -12840196478415667200000), (Sum.inr 5249, 8721406518151348224000), (Sum.inr 5251, 20804483957839626240000), (Sum.inr 5252, -15787189652894908416000), (Sum.inr 5254, -18103702594567274496000), (Sum.inr 5255, 10628823676665987072000), (Sum.inr 5260, 9126071378630148096000), (Sum.inr 5263, -16830413886397612032000), (Sum.inr 5264, 642323079345733632000), (Sum.inr 5265, -25288345262529183744000)]

def originalMerge1823 : Integer.Sparse OriginalKey := originalMerge1808 ++ originalMerge1822

theorem reducedMerge1823Check : reducedMerge1823 = Integer.Sparse.mergeBy masterLess reducedMerge1808 reducedMerge1822 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
